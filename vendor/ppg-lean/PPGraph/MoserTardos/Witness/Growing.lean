/-
  PPGraphMoserTardosGrowing.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos)

  Layer 3, Part B: the address-indexed growing tree, and the backward
  construction of τ_C(t) from a log (Moser & Tardos, "A constructive
  proof of the general Lovász Local Lemma", arXiv:0903.0544v3,
  Section 2).

  Builds on PPGraphMoserTardosWitness.lean (neighbor). Deliberately
  does NOT attempt injectivity of t ↦ τ_C(t) here, nor the connection
  back to the plain `WTree`/`WellFormed`/`Proper` shape from that file
  -- both are separate follow-up steps.

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import PPGraph.MoserTardos.Witness.Witness

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- Growing trees: finite address sets, addressable for attachment
-- -------------------------------------------------------------------

/-- A growing witness tree, represented by ADDRESS rather than as a
    plain rose tree: `[]` is the root, `v ++ [k]` is the (k+1)-th
    child of `v`. `dom` is the finite set of addresses built so far;
    `lab` labels them (meaningless outside `dom`). This representation
    lets us "attach a new child at an arbitrary EXISTING vertex `v`",
    which the immutable `WTree` shape from PPGraphMoserTardosWitness
    cannot express. -/
structure GrowingTree (ι : Type) where
  dom : Finset (List ℕ)
  lab : List ℕ → ι

/-- Well-formedness of the address structure alone (says nothing about
    labels): the root is always present, and every address's parent is
    present too. Kept as an external predicate, not a structure field,
    so it is established by induction on the construction rather than
    assumed. -/
def GrowingTree.Valid {ι : Type} (T : GrowingTree ι) : Prop :=
  [] ∈ T.dom ∧ ∀ v : List ℕ, ∀ k : ℕ, v ++ [k] ∈ T.dom → v ∈ T.dom

/-- The starting tree for τ_C(t): a single root labelled `i0` (the
    isolated root τ_C^{(t)}(t) := [C(t)] in the paper's notation). -/
def GrowingTree.singleton {ι : Type} (i0 : ι) : GrowingTree ι where
  dom := {[]}
  lab := fun _ => i0

theorem GrowingTree.singleton_valid {ι : Type} (i0 : ι) :
    (GrowingTree.singleton i0).Valid := by
  refine ⟨by simp [GrowingTree.singleton], ?_⟩
  intro v k hv
  simp [GrowingTree.singleton] at hv

-- -------------------------------------------------------------------
-- Fresh child indices
-- -------------------------------------------------------------------

/-- Every vertex has some unused child-index: the map `k ↦ v ++ [k]`
    is injective, so if all of them were already in the finite set
    `T.dom` that set would have to be infinite. -/
theorem exists_fresh_index {ι : Type} (T : GrowingTree ι) (v : List ℕ) :
    ∃ k : ℕ, v ++ [k] ∉ T.dom := by
  by_contra h
  push Not at h
  have hinj : Function.Injective (fun k : ℕ => v ++ [k]) := by
    intro a b hab
    simpa using hab
  have hsub : Set.range (fun k : ℕ => v ++ [k]) ⊆ (↑T.dom : Set (List ℕ)) := by
    rintro _ ⟨k, rfl⟩
    exact h k
  have hfin : (Set.range (fun k : ℕ => v ++ [k])).Finite :=
    Set.Finite.subset T.dom.finite_toSet hsub
  exact (Set.infinite_range_of_injective hinj) hfin

/-- A canonical choice of fresh child-index at `v` (which one exactly
    is immaterial -- the paper only ever needs *some* fresh slot). -/
noncomputable def GrowingTree.freshIndex {ι : Type} (T : GrowingTree ι) (v : List ℕ) : ℕ :=
  Classical.choose (exists_fresh_index T v)

theorem GrowingTree.freshIndex_spec {ι : Type} (T : GrowingTree ι) (v : List ℕ) :
    v ++ [T.freshIndex v] ∉ T.dom :=
  Classical.choose_spec (exists_fresh_index T v)

/-- Attach a fresh child labelled `a` to the vertex at address `v`. -/
noncomputable def GrowingTree.attachChild {ι : Type} (T : GrowingTree ι) (v : List ℕ) (a : ι) :
    GrowingTree ι where
  dom := insert (v ++ [T.freshIndex v]) T.dom
  lab := fun w => if w = v ++ [T.freshIndex v] then a else T.lab w

theorem GrowingTree.attachChild_preserves_root {ι : Type}
    (T : GrowingTree ι) (v : List ℕ) (a : ι) (hroot : [] ∈ T.dom) :
    [] ∈ (T.attachChild v a).dom :=
  Finset.mem_insert.mpr (Or.inr hroot)

/-- If `l1 ++ [x] = l2 ++ [y]` then `l1 = l2` and `x = y` -- reading
    off the equality from the reversed lists turns it into a `cons`
    equation, which `injection` splits directly. -/
theorem list_concat_inj {α : Type} {l1 l2 : List α} {x y : α}
    (h : l1 ++ [x] = l2 ++ [y]) : l1 = l2 ∧ x = y := by
  have hr : (l1 ++ [x]).reverse = (l2 ++ [y]).reverse := by rw [h]
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append] at hr
  injection hr with hx hl
  refine ⟨?_, hx⟩
  have := congrArg List.reverse hl
  simpa using this

theorem GrowingTree.attachChild_preserves_prefix_closed {ι : Type}
    (T : GrowingTree ι) (v : List ℕ) (a : ι)
    (hv : v ∈ T.dom)
    (hpc : ∀ w : List ℕ, ∀ k : ℕ, w ++ [k] ∈ T.dom → w ∈ T.dom) :
    ∀ w : List ℕ, ∀ k : ℕ, w ++ [k] ∈ (T.attachChild v a).dom → w ∈ (T.attachChild v a).dom := by
  intro w k hw
  simp only [GrowingTree.attachChild, Finset.mem_insert] at hw
  rcases hw with heq | hw
  · have := (list_concat_inj heq).1
    exact Finset.mem_insert.mpr (Or.inr (this ▸ hv))
  · exact Finset.mem_insert.mpr (Or.inr (hpc w k hw))

theorem GrowingTree.attachChild_preserves_valid {ι : Type}
    (T : GrowingTree ι) (v : List ℕ) (a : ι) (hv : v ∈ T.dom) (hV : T.Valid) :
    (T.attachChild v a).Valid :=
  ⟨T.attachChild_preserves_root v a hV.1,
   T.attachChild_preserves_prefix_closed v a hv hV.2⟩

-- -------------------------------------------------------------------
-- Attachment candidates and the max-depth pick
-- -------------------------------------------------------------------

/-- The vertices `v` currently in the tree whose Γ+ contains `a`, i.e.
    `a ∈ Γ+([v])`: either `a` repeats `v`'s own label, or `a` is a
    genuine dependency-graph neighbor of it. These are exactly the
    valid attachment points for a new child labelled `a`. -/
noncomputable def GrowingTree.candidates {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (a : ι) : Finset (List ℕ) :=
  T.dom.filter (fun v => T.lab v = a ∨ neighbor P (T.lab v) a)

theorem exists_max_depth_candidate {α : Type} (s : Finset (List α)) (h : s.Nonempty) :
    ∃ v ∈ s, ∀ w ∈ s, w.length ≤ v.length := by
  have himg : (s.image List.length).Nonempty := h.image _
  obtain ⟨v, hv⟩ := Finset.mem_image.mp (Finset.max'_mem _ himg)
  refine ⟨v, hv.1, ?_⟩
  intro w hw
  rw [hv.2]
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ hw)

/-- One backward step of the τ_C(t) construction: if some existing
    vertex could take `a` as a child, attach it to the one at MAXIMUM
    DISTANCE FROM THE ROOT among all such candidates (ties broken
    arbitrarily, via `Classical.choose`, exactly as the paper allows);
    otherwise leave the tree unchanged ("skip time step i"). -/
noncomputable def GrowingTree.attachAt {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (a : ι) : GrowingTree ι :=
  if h : (T.candidates P a).Nonempty then
    T.attachChild (Classical.choose (exists_max_depth_candidate _ h)) a
  else
    T

-- -------------------------------------------------------------------
-- The τ_C(t) construction itself
-- -------------------------------------------------------------------

/-- `τBuild P C t n` is the tree after `n` backward steps starting
    from the isolated root labelled `C t`: step `n = 0` is
    τ_C^{(t)}(t), and step `n+1` processes log index `t - 1 - n`
    (so the first backward step, n=0 → n=1, handles `i = t - 1`, the
    second handles `t - 2`, and so on). -/
noncomputable def τBuild {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) : ℕ → GrowingTree ι
  | 0 => GrowingTree.singleton (C t)
  | (n + 1) => (τBuild P C t n).attachAt P (C (t - 1 - n))

/-- τ_C(t) itself: run all `t - 1` backward steps (indices `t-1` down
    to `1`; if `t = 0` there is nothing to scan and the tree is just
    the isolated root). -/
noncomputable def τC {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) : GrowingTree ι :=
  τBuild P C t (t - 1)

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @GrowingTree
#check @GrowingTree.Valid
#check @GrowingTree.singleton
#check @GrowingTree.singleton_valid
#check @exists_fresh_index
#check @GrowingTree.freshIndex
#check @GrowingTree.freshIndex_spec
#check @GrowingTree.attachChild
#check @GrowingTree.attachChild_preserves_root
#check @list_concat_inj
#check @GrowingTree.attachChild_preserves_prefix_closed
#check @GrowingTree.attachChild_preserves_valid
#check @GrowingTree.candidates
#check @exists_max_depth_candidate
#check @GrowingTree.attachAt
#check @τBuild
#check @τC
