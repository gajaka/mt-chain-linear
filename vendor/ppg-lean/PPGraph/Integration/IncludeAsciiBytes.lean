/-
  Include an ASCII file as a literal list of byte values.

  This performs only frontend file I/O, like Lean's include_str. It does not
  parse JSON or prove a proposition. The emitted list is an ordinary kernel
  term; the JSON reader and its concrete decoding proofs remain pure Lean.
  Paths must be string literals relative to the source file.
-/
module

public meta import Lean.Elab.Term
public meta import Lean.Meta.AppBuilder

public section

open Lean Elab Term

syntax (name := includeAsciiBytes) "include_ascii_bytes " str : term

@[term_elab includeAsciiBytes]
meta def elabIncludeAsciiBytes : TermElab
  | `(include_ascii_bytes $path:str), _ => do
    let source := System.FilePath.mk (← readThe Core.Context).fileName
    let some directory := source.parent
      | throwError "Cannot find the source directory for {source}"
    let file := directory / path.getString
    let bytes ← IO.FS.readBinFile file
    let values := bytes.toList.map UInt8.toNat
    unless values.all (fun value => decide (value < 128)) do
      throwError "Expected an ASCII file: {file}"
    Meta.mkListLit (mkConst ``Nat) (values.map mkNatLit)
  | _, _ => throwUnsupportedSyntax
