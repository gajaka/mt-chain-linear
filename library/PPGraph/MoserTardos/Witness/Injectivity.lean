/-
  PPGraphMoserTardosInjectivity.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos)

  Layer 3, Part C: the injectivity argument.

  Builds on PPGraphMoserTardosGrowing.lean (GrowingTree, τBuild, τC).

  Matches Moser & Tardos (arXiv:0903.0544v3), end of Section 2 /
  start of Section 3, verbatim: "if t_i is the i-th time step with
  C(t_i) = A, then obviously the tree τ_C(t_i) contains exactly i
  vertices labelled A, thus τ_C(t_i) ≠ τ_C(t_j) unless i = j."

  The key mechanism the paper calls "obvious" but doesn't spell out:
  the ROOT of τ_C(t) is always labelled C(t) = A, and Γ+(A) always
  contains A itself (a child may repeat its parent's label -- see
  PPGraphMoserTardosWitness.lean's WellFormed), so EVERY earlier
  occurrence of A in the backward scan is guaranteed a valid
  attachment point (the root, or something deeper) and therefore
  always succeeds in adding exactly one new A-labelled vertex. This
  file proves that mechanism directly, then the counting/injectivity
  claim follows.

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import PPGraph.MoserTardos.Witness.Growing

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- Counting vertices by label
-- -------------------------------------------------------------------

/-- The number of vertices of `T` carrying label `A`. -/
def countLabel {ι : Type} [DecidableEq ι] (T : GrowingTree ι) (A : ι) : ℕ :=
  (T.dom.filter (fun v => T.lab v = A)).card

-- -------------------------------------------------------------------
-- The indices scanned after n backward steps from time t
-- -------------------------------------------------------------------

/-- The set of log indices already processed after `n` backward steps
    of `τBuild _ _ t _`: step `n` handles index `t - 1 - (n - 1)`, so
    after `n` steps the covered indices are `{t-1, t-2, ..., t-n}`. -/
def stepsCovered (t : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | (n + 1) => insert (t - 1 - n) (stepsCovered t n)

theorem stepsCovered_lt {t : ℕ} : ∀ n, n < t → ∀ k ∈ stepsCovered t n, t - 1 - n < k := by
  intro n
  induction n with
  | zero => intro _ k hk; simp [stepsCovered] at hk
  | succ m ih =>
    intro hn k hk
    simp only [stepsCovered, Finset.mem_insert] at hk
    rcases hk with hk | hk
    · omega
    · have := ih (by omega) k hk
      omega

theorem stepsCovered_fresh {t n : ℕ} (hn : n < t) : t - 1 - n ∉ stepsCovered t n := by
  intro hmem
  exact absurd (stepsCovered_lt n hn (t - 1 - n) hmem) (lt_irrefl _)

theorem stepsCovered_le {t : ℕ} (ht : 0 < t) : ∀ n, ∀ k ∈ stepsCovered t n, k ≤ t - 1 := by
  intro n
  induction n with
  | zero => intro k hk; simp [stepsCovered] at hk
  | succ m ih =>
    intro k hk
    simp only [stepsCovered, Finset.mem_insert] at hk
    rcases hk with hk | hk
    · omega
    · exact ih k hk

theorem stepsCovered_mem_of_lt {t : ℕ} : ∀ n, ∀ s, t - n ≤ s → s < t → s ∈ stepsCovered t n := by
  intro n
  induction n with
  | zero => intro s hle hlt; exfalso; omega
  | succ m ih =>
    intro s hle hlt
    simp only [stepsCovered, Finset.mem_insert]
    by_cases heq : s = t - 1 - m
    · exact Or.inl heq
    · exact Or.inr (ih s (by omega) hlt)

-- -------------------------------------------------------------------
-- Attaching a label that already occurs adds exactly one more of it
-- -------------------------------------------------------------------

theorem candidates_nonempty_of_label {S : VarSpaces V} {ι : Type} (P : MTProcess S ι)
    (T : GrowingTree ι) (a : ι) (v : List ℕ) (hv : v ∈ T.dom) (hlab : T.lab v = a) :
    (T.candidates P a).Nonempty :=
  ⟨v, Finset.mem_filter.mpr ⟨hv, Or.inl hlab⟩⟩

theorem GrowingTree.attachChild_preserves_lab_root {ι : Type} (T : GrowingTree ι)
    (v : List ℕ) (a : ι) : (T.attachChild v a).lab [] = T.lab [] := by
  simp [GrowingTree.attachChild]

theorem GrowingTree.attachChild_filter_eq {ι : Type} [DecidableEq ι]
    (T : GrowingTree ι) (v : List ℕ) (a : ι) :
    (T.attachChild v a).dom.filter (fun w => (T.attachChild v a).lab w = a) =
      insert (v ++ [T.freshIndex v]) (T.dom.filter (fun w => T.lab w = a)) := by
  apply Finset.ext
  intro w
  simp only [GrowingTree.attachChild, Finset.mem_filter, Finset.mem_insert]
  by_cases hw : w = v ++ [T.freshIndex v]
  · simp [hw]
  · simp [hw]

theorem GrowingTree.attachChild_countLabel {ι : Type} [DecidableEq ι]
    (T : GrowingTree ι) (v : List ℕ) (a : ι) :
    countLabel (T.attachChild v a) a = countLabel T a + 1 := by
  have hnotmem : (v ++ [T.freshIndex v]) ∉ T.dom.filter (fun w => T.lab w = a) := by
    intro hmem
    exact T.freshIndex_spec v (Finset.mem_filter.mp hmem).1
  unfold countLabel
  rw [GrowingTree.attachChild_filter_eq T v a, Finset.card_insert_of_notMem hnotmem]

theorem GrowingTree.attachChild_countLabel_ne {ι : Type} [DecidableEq ι]
    (T : GrowingTree ι) (v : List ℕ) (a A : ι) (hne : a ≠ A) :
    countLabel (T.attachChild v a) A = countLabel T A := by
  have hset : (T.attachChild v a).dom.filter (fun w => (T.attachChild v a).lab w = A) =
      T.dom.filter (fun w => T.lab w = A) := by
    apply Finset.ext
    intro w
    constructor
    · intro hw
      have hw' := Finset.mem_filter.mp hw
      rcases Finset.mem_insert.mp hw'.1 with heq | hmem
      · exfalso
        have hlab : (T.attachChild v a).lab w = A := hw'.2
        rw [heq] at hlab
        simp only [GrowingTree.attachChild, ite_true] at hlab
        exact hne hlab
      · apply Finset.mem_filter.mpr
        refine ⟨hmem, ?_⟩
        have hnefresh : w ≠ v ++ [T.freshIndex v] := by
          intro h; rw [h] at hmem; exact T.freshIndex_spec v hmem
        have hlab := hw'.2
        simp only [GrowingTree.attachChild] at hlab
        rw [ite_eq_right hnefresh] at hlab
        exact hlab
    · intro hw
      have hw' := Finset.mem_filter.mp hw
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_insert.mpr (Or.inr hw'.1), ?_⟩
      have hnefresh : w ≠ v ++ [T.freshIndex v] := by
        intro h; rw [h] at hw'; exact T.freshIndex_spec v hw'.1
      simp only [GrowingTree.attachChild]
      rw [ite_eq_right hnefresh]
      exact hw'.2
  unfold countLabel
  rw [hset]

theorem GrowingTree.attachAt_countLabel_of_label {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (T : GrowingTree ι) (a : ι) (v : List ℕ)
    (hv : v ∈ T.dom) (hlab : T.lab v = a) :
    countLabel (T.attachAt P a) a = countLabel T a + 1 := by
  have hne : (T.candidates P a).Nonempty := candidates_nonempty_of_label P T a v hv hlab
  unfold GrowingTree.attachAt
  rw [dite_eq_left hne]
  exact GrowingTree.attachChild_countLabel T _ a

theorem GrowingTree.attachAt_countLabel_of_ne {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (T : GrowingTree ι) (a A : ι) (hne : a ≠ A) :
    countLabel (T.attachAt P a) A = countLabel T A := by
  unfold GrowingTree.attachAt
  split
  · exact GrowingTree.attachChild_countLabel_ne T _ a A hne
  · rfl

-- -------------------------------------------------------------------
-- The main invariant: root survives, keeps its label, and the count
-- of A-labelled vertices tracks exactly how often A = C(t) recurs
-- -------------------------------------------------------------------

theorem τBuild_root_and_count {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) :
    ∀ n, n < t →
      [] ∈ (τBuild P C t n).dom ∧
      (τBuild P C t n).lab [] = C t ∧
      countLabel (τBuild P C t n) (C t) =
        1 + ((stepsCovered t n).filter (fun s => C s = C t)).card := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_⟩
    · simp [τBuild, GrowingTree.singleton]
    · simp [τBuild, GrowingTree.singleton]
    · simp [τBuild, GrowingTree.singleton, countLabel, stepsCovered]
  | succ m ih =>
    intro hm1
    have hm : m < t := by omega
    obtain ⟨hroot, hlab, hcount⟩ := ih hm
    show [] ∈ ((τBuild P C t m).attachAt P (C (t - 1 - m))).dom ∧
      ((τBuild P C t m).attachAt P (C (t - 1 - m))).lab [] = C t ∧
      countLabel ((τBuild P C t m).attachAt P (C (t - 1 - m))) (C t) =
        1 + ((stepsCovered t (m + 1)).filter (fun s => C s = C t)).card
    by_cases hA : C (t - 1 - m) = C t
    · have hkey := GrowingTree.attachAt_countLabel_of_label P (τBuild P C t m)
        (C (t - 1 - m)) [] hroot (hlab.trans hA.symm)
      refine ⟨?_, ?_, ?_⟩
      · unfold GrowingTree.attachAt
        by_cases hne : ((τBuild P C t m).candidates P (C (t - 1 - m))).Nonempty
        · rw [dite_eq_left hne]; exact GrowingTree.attachChild_preserves_root _ _ _ hroot
        · rw [dite_eq_right hne]; exact hroot
      · unfold GrowingTree.attachAt
        by_cases hne : ((τBuild P C t m).candidates P (C (t - 1 - m))).Nonempty
        · rw [dite_eq_left hne, GrowingTree.attachChild_preserves_lab_root]; exact hlab
        · rw [dite_eq_right hne]; exact hlab
      · have hbridge : countLabel ((τBuild P C t m).attachAt P (C (t - 1 - m))) (C t) =
            countLabel ((τBuild P C t m).attachAt P (C (t - 1 - m))) (C (t - 1 - m)) := by
          rw [hA]
        rw [hbridge, hkey, hA, hcount]
        have hfresh : (t - 1 - m) ∉ (stepsCovered t m).filter (fun s => C s = C t) := by
          intro hmem
          exact (stepsCovered_fresh hm) (Finset.mem_filter.mp hmem).1
        have hstep : stepsCovered t (m + 1) = insert (t - 1 - m) (stepsCovered t m) := rfl
        rw [hstep, Finset.filter_insert, ite_eq_left hA, Finset.card_insert_of_notMem hfresh]
        omega
    · have hkey := GrowingTree.attachAt_countLabel_of_ne P (τBuild P C t m)
        (C (t - 1 - m)) (C t) hA
      refine ⟨?_, ?_, ?_⟩
      · unfold GrowingTree.attachAt
        by_cases hne : ((τBuild P C t m).candidates P (C (t - 1 - m))).Nonempty
        · rw [dite_eq_left hne]; exact GrowingTree.attachChild_preserves_root _ _ _ hroot
        · rw [dite_eq_right hne]; exact hroot
      · unfold GrowingTree.attachAt
        by_cases hne : ((τBuild P C t m).candidates P (C (t - 1 - m))).Nonempty
        · rw [dite_eq_left hne, GrowingTree.attachChild_preserves_lab_root]; exact hlab
        · rw [dite_eq_right hne]; exact hlab
      · rw [hkey, hcount]
        have hstep : stepsCovered t (m + 1) = insert (t - 1 - m) (stepsCovered t m) := rfl
        rw [hstep, Finset.filter_insert, ite_eq_right hA]

-- -------------------------------------------------------------------
-- Injectivity: distinct occurrence-times of the same event give
-- distinct witness trees
-- -------------------------------------------------------------------

/-- The stronger, directly-useful fact underneath `τC_injective_on_occurrences`:
    the per-label occurrence COUNTS themselves differ (not just the trees), for
    the shared label `C t1 = C t2` -- exactly the invariant that survives
    `GrowingTree.toWTree`/`WTree.canonicalize` unchanged
    (`GrowingTree.toWTreeFuel_countLabel`, `WTree.canonicalize_countLabel`,
    PPGraphMoserTardosInjectivityBridge.lean), which the plain tree-inequality
    above does not by itself guarantee survives that conversion. -/
theorem τC_countLabel_ne_of_lt {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (C : ℕ → ι) (t1 t2 : ℕ)
    (ht1 : 0 < t1) (ht2 : 0 < t2) (hlt : t1 < t2) (hA : C t1 = C t2) :
    countLabel (τC P C t1) (C t1) ≠ countLabel (τC P C t2) (C t2) := by
  have hc1 := (τBuild_root_and_count P C t1 (t1 - 1) (by omega)).2.2
  have hc2 := (τBuild_root_and_count P C t2 (t2 - 1) (by omega)).2.2
  show countLabel (τBuild P C t1 (t1 - 1)) (C t1) ≠ countLabel (τBuild P C t2 (t2 - 1)) (C t2)
  rw [hc1, hc2, hA]
  intro hcount
  have hnotmem : t1 ∉ stepsCovered t1 (t1 - 1) := by
    intro hmem
    have := stepsCovered_le ht1 (t1 - 1) t1 hmem
    omega
  have hmem2 : t1 ∈ stepsCovered t2 (t2 - 1) := stepsCovered_mem_of_lt (t2 - 1) t1 (by omega) hlt
  have hsub : (stepsCovered t1 (t1 - 1)).filter (fun s => C s = C t2) ⊂
      (stepsCovered t2 (t2 - 1)).filter (fun s => C s = C t2) := by
    constructor
    · intro k hk
      have hk1 := Finset.mem_filter.mp hk
      have hkb := stepsCovered_le ht1 (t1 - 1) k hk1.1
      have hklb := stepsCovered_lt (t1 - 1) (by omega) k hk1.1
      exact Finset.mem_filter.mpr ⟨stepsCovered_mem_of_lt (t2 - 1) k (by omega) (by omega), hk1.2⟩
    · intro hcontra
      have hmemA : t1 ∈ (stepsCovered t2 (t2 - 1)).filter (fun s => C s = C t2) :=
        Finset.mem_filter.mpr ⟨hmem2, hA⟩
      have hmemB : t1 ∈ (stepsCovered t1 (t1 - 1)).filter (fun s => C s = C t2) := hcontra hmemA
      exact hnotmem (Finset.mem_filter.mp hmemB).1
  have hcard := Finset.card_lt_card hsub
  omega

theorem τC_injective_on_occurrences {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (C : ℕ → ι) (t1 t2 : ℕ)
    (ht1 : 0 < t1) (ht2 : 0 < t2) (hlt : t1 < t2) (hA : C t1 = C t2) :
    τC P C t1 ≠ τC P C t2 := by
  intro heq
  exact τC_countLabel_ne_of_lt P C t1 t2 ht1 ht2 hlt hA (by rw [heq, hA])

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @countLabel
#check @stepsCovered
#check @stepsCovered_lt
#check @stepsCovered_fresh
#check @stepsCovered_le
#check @stepsCovered_mem_of_lt
#check @candidates_nonempty_of_label
#check @GrowingTree.attachChild_preserves_lab_root
#check @GrowingTree.attachChild_filter_eq
#check @GrowingTree.attachChild_countLabel
#check @GrowingTree.attachChild_countLabel_ne
#check @GrowingTree.attachAt_countLabel_of_label
#check @GrowingTree.attachAt_countLabel_of_ne
#check @τBuild_root_and_count
#check @τC_countLabel_ne_of_lt
#check @τC_injective_on_occurrences
