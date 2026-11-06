/-
  PPGraphMoserTardosCheck.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), Theorem 5.7.2.

  The τ-check itself (Moser-Tardos arXiv:0903.0544v3, Lemma 2.1's proof,
  read 2026-09-20): a deterministic procedure over a witness tree T and a
  FIXED log ω, visiting T's vertices in order of DECREASING DEPTH and, at
  each vertex w (labelled `a := T.lab w`), reading `atIdx ω v n` for each
  `v ∈ P.footprint a` at the TREE-DETERMINED local index `n = localCount
  P T w v` - the number of STRICTLY DEEPER vertices of T whose label also
  uses `v`. The check passes at w iff those readings land in `P.bad a`;
  it passes overall iff every vertex passes.

  Well-defined thanks to `PPGraphMoserTardosCheckOrder.lean`'s
  `τBuild_sameDepthIndependent`: same-depth vertices never share a
  variable, so `localCount` genuinely counts "how many times v is used
  strictly below w" without any same-depth ambiguity - exactly what makes
  the paper's own informal "process in decreasing depth" recipe precise.

  Scope, deliberately: this file defines the check and states what it
  means for it to be well-formed; it does NOT yet prove Lemma 2.1(ii)
  (occurrence in the real trajectory implies the check passes) nor the
  independence-based probability bound. Both are separate, substantial
  next increments - see the file header of
  PPGraphMoserTardosCheckOrder.lean for the roadmap.

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.MoserTardos.Witness.CheckOrder
public import PPGraph.MoserTardos.Process.RandomTrajectory

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- The tree-determined local index (Moser-Tardos's |S(P)|)
-- -------------------------------------------------------------------

/-- `localCount P T w v` is the number of vertices of `T` STRICTLY
    deeper than `w` whose label's footprint also uses `v` - Moser-Tardos's
    `|S(P)|` (Lemma 2.1's proof), the tree-determined local index at
    which `w` should read variable `v`. -/
noncomputable def localCount {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (w : List ℕ) (v : V) : ℕ :=
  (T.dom.filter (fun w' => w.length < w'.length ∧ v ∈ P.footprint (T.lab w'))).card

-- -------------------------------------------------------------------
-- The check itself
-- -------------------------------------------------------------------

/-- The state the τ-check reconstructs at vertex `w`: for each variable,
    read the log `ω` at `w`'s own tree-determined local index for that
    variable (`localCount`). A FULL `MTState`, not just the restriction
    to `w`'s footprint - matches how `P.bad`/`depends_only_on` are stated
    elsewhere in this project (a full-state predicate that PROVABLY only
    depends on the declared footprint, rather than a footprint-indexed
    partial state). -/
noncomputable def checkState {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (ω : LogSpace S) (w : List ℕ) : MTState S :=
  fun v => atIdx ω v (localCount P T w v)

/-- Moser-Tardos's τ-check (Lemma 2.1's proof): visit every vertex of `T`
    (order is immaterial to this Prop-level statement - `localCount`
    already bakes the "decreasing depth" ordering into WHICH index gets
    read, so the check is well-defined as a plain conjunction over
    `T.dom`, no explicit traversal needed) and require that the
    reconstructed state at each vertex lands in that vertex's own bad
    set. -/
def τCheck {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (ω : LogSpace S) : Prop :=
  ∀ w ∈ T.dom, checkState P T ω w ∈ P.bad (T.lab w)

-- -------------------------------------------------------------------
-- checkState's bad-event depends only on FINITELY many log
-- coordinates -- the `depends_only_on`-shaped fact (PPGraphMoserTardos
-- .lean) the independence argument for Lemma 2.1(ii)'s probability
-- half needs: each vertex `w`'s check only reads the log at
-- `(localCount P T w v, v)` for `v` in the label's own footprint, so
-- two logs agreeing there give the SAME bad-membership verdict.
-- Immediate from `P.dep`/`depends_only_on` plus unfolding `checkState`
-- /`atIdx`; the real content is already in `P.dep`, this just routes
-- it through the (index, variable)-coordinate view `LogSpace` uses.
-- -------------------------------------------------------------------

theorem checkState_bad_depends_only_on_indices {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (w : List ℕ) (a : ι)
    (ω1 ω2 : LogSpace S)
    (hagree : ∀ v ∈ P.footprint a, ω1 (localCount P T w v, v) = ω2 (localCount P T w v, v)) :
    checkState P T ω1 w ∈ P.bad a ↔ checkState P T ω2 w ∈ P.bad a :=
  P.dep a (checkState P T ω1 w) (checkState P T ω2 w) hagree

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @localCount
#check @checkState
#check @τCheck
#check @checkState_bad_depends_only_on_indices
