"""Inspect pinned Lean 4.35 NDJSON exports without executing Lean or a checker.

This is a structural inspection of the export, not a replacement type checker.
Nanoda counts each member of an inductive bundle as a separate declaration.
Expression dependencies are retained in compact arrays, rather than JSON trees.
"""

from __future__ import annotations

from array import array
from collections import Counter
import hashlib
import json
from pathlib import Path


PERMITTED_AXIOMS = frozenset({"Classical.choice", "Quot.sound", "propext"})
_BINDERS = {"default", "implicit", "strictImplicit", "instImplicit"}


def _object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("Duplicate JSON object key: " + key)
        result[key] = value
    return result


def _nat(value):
    if type(value) is not int or value < 0:
        raise ValueError("Expected a nonnegative integer index")
    return value


class _Inspector:
    def __init__(self):
        self.names = [""]  # Name.anonymous is implicit index 0.
        self.canonical_names = bytearray([1])
        self.name_ids = {"": 0}
        self.name_nodes = set()
        self.level_count = 1  # Level.zero is implicit index 0.
        self.offsets = array("Q", [0])
        self.edges = array("q")
        self.referenced_names = set()
        self.declarations = {}
        self.declaration_names = {}
        self.blocks = []
        self.counts = Counter()
        self.axioms = set()
        self.command_count = 0
        self.metadata = None

    @property
    def expression_count(self):
        return len(self.offsets) - 1

    def name_ref(self, value):
        index = _nat(value)
        if index >= len(self.names):
            raise ValueError("Forward or missing name reference: " + str(index))
        return index

    def level_ref(self, value):
        index = _nat(value)
        if index >= self.level_count:
            raise ValueError("Forward or missing universe reference: " + str(index))
        return index

    def expression_ref(self, value):
        index = _nat(value)
        if index >= self.expression_count:
            raise ValueError("Forward or missing expression reference: " + str(index))
        return index

    def constant_ref(self, value):
        index = self.name_ref(value)
        self.referenced_names.add(index)
        return -index - 1

    def implicit_constant(self, name):
        if name not in self.name_ids:
            raise ValueError("Missing implicit literal dependency: " + name)
        return self.constant_ref(self.name_ids[name])

    def name_record(self, record):
        index = _nat(record["in"])
        if index != len(self.names):
            raise ValueError("Noncontinuous or repeated name index")
        tag = "str" if "str" in record else "num"
        if set(record) != {"in", tag}:
            raise ValueError("Malformed interned name record")
        item = record[tag]
        prefix = self.name_ref(item["pre"])
        component = item["str"] if tag == "str" else _nat(item["i"])
        if tag == "str" and not isinstance(component, str):
            raise ValueError("Name string component is not a string")
        node = (tag, prefix, component)
        if node in self.name_nodes:
            raise ValueError("Repeated interned name node")
        self.name_nodes.add(node)
        rendered = (self.names[prefix] + "." if prefix else "") + str(component)
        self.names.append(rendered)
        canonical = tag == "str" and "." not in component and self.canonical_names[prefix]
        self.canonical_names.append(bool(canonical))
        if canonical:
            self.name_ids[rendered] = index

    def level_record(self, record):
        if _nat(record["il"]) != self.level_count:
            raise ValueError("Noncontinuous or repeated universe index")
        tags = set(record) - {"il"}
        if len(tags) != 1:
            raise ValueError("Malformed universe record")
        tag = tags.pop()
        value = record[tag]
        if tag == "succ":
            self.level_ref(value)
        elif tag in {"max", "imax"}:
            if not isinstance(value, list) or len(value) != 2:
                raise ValueError("Malformed binary universe operation")
            for item in value:
                self.level_ref(item)
        elif tag == "param":
            self.name_ref(value)
        else:
            raise ValueError("Unknown universe tag: " + tag)
        self.level_count += 1

    def expression_record(self, record):
        if _nat(record["ie"]) != self.expression_count:
            raise ValueError("Noncontinuous or repeated expression index")
        tags = set(record) - {"ie"}
        if len(tags) != 1:
            raise ValueError("Malformed expression record")
        tag = tags.pop()
        value = record[tag]
        refs = []
        if tag == "const":
            refs.append(self.constant_ref(value["name"]))
            for level in value["us"]:
                self.level_ref(level)
        elif tag == "sort":
            self.level_ref(value)
        elif tag == "bvar":
            _nat(value)
        elif tag in {"app", "lam", "forallE", "letE", "proj", "mdata"}:
            fields = {
                "app": ("fn", "arg"),
                "lam": ("type", "body"),
                "forallE": ("type", "body"),
                "letE": ("type", "value", "body"),
                "proj": ("struct",),
                "mdata": ("expr",),
            }[tag]
            refs.extend(self.expression_ref(value[field]) for field in fields)
            if tag in {"lam", "forallE", "letE"}:
                self.name_ref(value["name"])
            if tag in {"lam", "forallE"} and value["binderInfo"] not in _BINDERS:
                raise ValueError("Unknown binder information")
            if tag == "letE" and type(value["nondep"]) is not bool:
                raise ValueError("Malformed let nondep flag")
            if tag == "proj":
                _nat(value["idx"])
                refs.append(self.constant_ref(value["typeName"]))
        elif tag == "natVal":
            if not isinstance(value, str) or not value or not value.isascii() or not value.isdecimal():
                raise ValueError("Malformed natural literal")
            refs.append(self.implicit_constant("Nat"))
        elif tag == "strVal":
            if not isinstance(value, str):
                raise ValueError("Malformed string literal")
            # These are precisely the implicit dependencies added by LeanExport.
            refs.extend(self.implicit_constant(name) for name in ("Char.ofNat", "String.ofList"))
        else:
            raise ValueError("Unknown expression tag: " + tag)
        self.edges.extend(refs)
        self.offsets.append(len(self.edges))

    def declaration(self, tag, item, block=-1):
        name_id = self.name_ref(item["name"])
        name = self.names[name_id]
        if not name or name_id in self.declarations or name in self.declaration_names:
            raise ValueError("Anonymous or duplicate declaration: " + name)
        type_id = self.expression_ref(item["type"])
        value_id = None
        if tag in {"def", "thm", "opaque"}:
            # Membership and indexing both matter: expression 0 is a valid body.
            if "value" not in item:
                raise ValueError("Missing declaration body: " + name)
            value_id = self.expression_ref(item["value"])
        for parameter in item["levelParams"]:
            self.name_ref(parameter)
        if item.get("isUnsafe", False) is not False:
            raise ValueError("Unsafe declaration: " + name)
        if tag == "def" and item.get("safety") != "safe":
            raise ValueError("Unsafe or partial definition: " + name)
        if tag == "axiom":
            if name not in PERMITTED_AXIOMS or not self.canonical_names[name_id]:
                raise ValueError("Unpermitted axiom: " + name)
            self.axioms.add(name)
        rule_expressions = ()
        if tag == "recursor":
            rule_expressions = tuple(self.expression_ref(rule["rhs"]) for rule in item["rules"])
            for rule in item["rules"]:
                self.constant_ref(rule["ctor"])
        self.declarations[name_id] = (tag, type_id, value_id, rule_expressions, block)
        self.declaration_names[name] = name_id
        self.counts[tag] += 1

    def declaration_record(self, record):
        if len(record) != 1:
            raise ValueError("Malformed declaration command")
        tag, item = next(iter(record.items()))
        self.command_count += 1
        if tag == "inductive":
            if set(item) != {"types", "ctors", "recs"} or not item["types"]:
                raise ValueError("Malformed inductive bundle")
            block = len(self.blocks)
            names = []
            for field, member_tag in (("types", "inductive"), ("ctors", "constructor"), ("recs", "recursor")):
                for member in item[field]:
                    names.append(self.name_ref(member["name"]))
                    self.declaration(member_tag, member, block)
            self.blocks.append(tuple(names))
        elif tag in {"axiom", "def", "thm", "opaque", "quot"}:
            self.declaration(tag, item)
        else:
            raise ValueError("Unknown declaration tag: " + tag)

    def root_closure(self, root_ids):
        seen_expressions = bytearray(self.expression_count)
        seen_names = set()
        seen_blocks = set()
        stack = [-index - 1 for index in root_ids]
        while stack:
            reference = stack.pop()
            if reference >= 0:
                if seen_expressions[reference]:
                    continue
                seen_expressions[reference] = 1
                stack.extend(self.edges[self.offsets[reference]:self.offsets[reference + 1]])
            else:
                name_id = -reference - 1
                if name_id in seen_names:
                    continue
                seen_names.add(name_id)
                _tag, type_id, value_id, rule_expressions, block = self.declarations[name_id]
                stack.append(type_id)
                if value_id is not None:
                    stack.append(value_id)
                stack.extend(rule_expressions)
                if block >= 0 and block not in seen_blocks:
                    seen_blocks.add(block)
                    stack.extend(-member - 1 for member in self.blocks[block])
        closure_names = sorted(self.names[index] for index in seen_names)
        return {
            "declaration_count": len(seen_names),
            "expression_count": sum(seen_expressions),
            "axioms": sorted(set(closure_names) & self.axioms),
            "declaration_names_sha256": hashlib.sha256("\n".join(closure_names).encode()).hexdigest(),
            "exported_declarations_outside_root_closure": len(self.declarations) - len(seen_names),
            "method": "Actual expression type/value references, recursor rule bodies, complete inductive bundles, and implicit literal dependencies",
        }


def inspect_export(path, expected_names):
    """Validate actual roots, axioms, references and Nanoda's declaration count.

    ``roots`` maps each requested original name to its actual interned name,
    type and proof-body expression IDs. No truthiness test is used for IDs.
    The union closure is reported separately from explicitly added export roots.
    """
    path = Path(path)
    expected_names = tuple(expected_names)
    if not expected_names or len(set(expected_names)) != len(expected_names):
        raise ValueError("Expected theorem names must be nonempty and unique")
    inspector = _Inspector()
    digest = hashlib.sha256()
    size = 0
    line_number = 0
    with path.open("rb") as stream:
        for line_number, raw in enumerate(stream, 1):
            digest.update(raw)
            size += len(raw)
            try:
                record = json.loads(raw, object_pairs_hook=_object)
                if not isinstance(record, dict):
                    raise ValueError("Export line must contain an object")
                if "meta" in record:
                    if line_number != 1 or set(record) != {"meta"}:
                        raise ValueError("Metadata must occur exactly once at the beginning")
                    inspector.metadata = record["meta"]
                    if inspector.metadata["exporter"] != {"name": "lean4export", "version": "3.1.0"}:
                        raise ValueError("Unexpected pinned Lean exporter")
                    if inspector.metadata["format"]["version"] != "3.1.0":
                        raise ValueError("Unexpected pinned export format")
                    if inspector.metadata["lean"]["version"] != "4.35.0":
                        raise ValueError("Unexpected pinned Lean version")
                elif inspector.metadata is None:
                    raise ValueError("Missing export metadata")
                elif "in" in record:
                    inspector.name_record(record)
                elif "il" in record:
                    inspector.level_record(record)
                elif "ie" in record:
                    inspector.expression_record(record)
                else:
                    inspector.declaration_record(record)
            except (KeyError, TypeError, ValueError, IndexError) as error:
                raise ValueError(f"Invalid export at line {line_number}: {error}") from error
    if inspector.metadata is None or not inspector.declarations:
        raise ValueError("Empty or incomplete export")
    missing_references = inspector.referenced_names - inspector.declarations.keys()
    if missing_references:
        names = sorted(inspector.names[index] for index in missing_references)
        raise ValueError("Export has undeclared constant references: " + repr(names[:20]))
    roots = {}
    for name in expected_names:
        if name not in inspector.declaration_names:
            raise ValueError("Selected original theorem is absent: " + name)
        name_id = inspector.declaration_names[name]
        tag, type_id, value_id, _rules, _block = inspector.declarations[name_id]
        if tag != "thm" or value_id is None or not inspector.canonical_names[name_id]:
            raise ValueError("Selected original root is not a theorem with a proof body: " + name)
        roots[name] = {"tag": tag, "name_id": name_id, "type_id": type_id, "value_id": value_id}
    closure = inspector.root_closure(row["name_id"] for row in roots.values())
    return {
        "status": "PASS",
        "export_path": str(path.resolve()),
        "export_sha256": digest.hexdigest(),
        "export_bytes": size,
        "line_count": line_number,
        "metadata": inspector.metadata,
        "root_count": len(roots),
        "roots": roots,
        "actual_axioms": sorted(inspector.axioms),
        "expanded_declaration_count": len(inspector.declarations),
        "declaration_command_count": inspector.command_count,
        "declarations_by_tag": dict(sorted(inspector.counts.items())),
        "inductive_bundle_count": len(inspector.blocks),
        "name_count_including_anonymous": len(inspector.names),
        "level_count_including_zero": inspector.level_count,
        "expression_count": inspector.expression_count,
        "constant_references_closed": True,
        "root_closure": closure,
        "scope": "Structural inspection only; proof type checking is performed by Nanoda",
    }
