/-
  PPGraphMoserTardosPegden.lean

  The algorithmic cluster-expansion criterion of Wesley Pegden,
  "An extension of the Moser-Tardos algorithmic local lemma",
  arXiv:1102.2853v2, Theorem 1.4.
  https://arxiv.org/abs/1102.2853

  The existing product budget enumerates every subset of a closed
  neighborhood. Pegden's criterion sums only over independent subsets.
  Real witness trees satisfy the stronger same-depth independence
  property already proved in this development, so their canonical forms
  belong to this smaller family. The existing occurrence-counting and
  probability bounds then give E[T_LOG] <= sum x, without assuming
  termination. The algorithm and the random-initialization law are unchanged.

  Budgets here are finite nonnegative reals; the proof also covers zero
  budgets when the associated probability bounds are zero. Independence
  always concerns distinct labels, so singleton child sets are allowed.

  The final example has one uniform ternary variable and bad events
  X = 0 and X = 1. It satisfies the new criterion with budgets 1, 1,
  while no budgets satisfy the old product criterion.
-/

module

public import PPGraph.MoserTardos.Bounds.OccurrenceExpectation
public import PPGraph.MoserTardos.Witness.LabelsAtDepthBridge
public import PPGraph.Integration.MoserTardosRepair
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! ## Independent subsets and the finite-depth tree bound -/



set_option linter.unusedSectionVars false

open Classical
open scoped NNReal ENNReal

namespace Pegden

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι]

/-- Independence concerns distinct labels; singletons, including the root's own label,
are allowed in the closed neighborhood. -/
def Independent (P : MTProcess S ι) (T : Finset ι) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, a ≠ b → ¬ neighbor P a b

theorem independent_empty (P : MTProcess S ι) : Independent P ∅ := by
  simp [Independent]

theorem independent_singleton (P : MTProcess S ι) (a : ι) :
    Independent P {a} := by
  simp [Independent]

theorem Independent.mono (P : MTProcess S ι) {T U : Finset ι}
    (h : Independent P U) (hTU : T ⊆ U) : Independent P T := by
  intro a ha b hb hne
  exact h a (hTU ha) b (hTU hb) hne

noncomputable def independentSubsets (P : MTProcess S ι) (α : ι) : Finset (Finset ι) := by
  classical
  exact (plusNeighbors P α).powerset.filter (Independent P)

@[simp]
theorem mem_independentSubsets (P : MTProcess S ι) (α : ι) (T : Finset ι) :
    T ∈ independentSubsets P α ↔ T ⊆ plusNeighbors P α ∧ Independent P T := by
  classical
  simp [independentSubsets]

@[simp]
theorem empty_mem_independentSubsets (P : MTProcess S ι) (α : ι) :
    ∅ ∈ independentSubsets P α := by
  simp [independent_empty]

noncomputable def polynomial (P : MTProcess S ι) (x : ι → ℝ≥0) (α : ι) : ℝ≥0 :=
  ∑ T ∈ independentSubsets P α, ∏ b ∈ T, x b

theorem polynomial_mono (P : MTProcess S ι) (x y : ι → ℝ≥0)
    (hxy : ∀ b, x b ≤ y b) (α : ι) :
    polynomial P x α ≤ polynomial P y α := by
  apply Finset.sum_le_sum
  intro T _
  exact Finset.prod_le_prod (fun b _ => hxy b)

theorem one_le_polynomial (P : MTProcess S ι) (x : ι → ℝ≥0) (α : ι) :
    1 ≤ polynomial P x α := by
  have h := Finset.single_le_sum (fun T (_ : T ∈ independentSubsets P α) =>
    show 0 ≤ ∏ b ∈ T, x b from zero_le) (empty_mem_independentSubsets P α)
  simpa [polynomial] using h

theorem polynomial_le_prod_one_add (P : MTProcess S ι) (x : ι → ℝ≥0) (α : ι) :
    polynomial P x α ≤ ∏ b ∈ plusNeighbors P α, (1 + x b) := by
  rw [Finset.prod_one_add]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset (Independent P) _)
    (fun _ _ _ => zero_le)

theorem product_budget_implies (P : MTProcess S ι) (p x : ι → ℝ≥0)
    (hprod : ∀ α, p α * ∏ b ∈ plusNeighbors P α, (1 + x b) ≤ x α) :
    ∀ α, p α * polynomial P x α ≤ x α := by
  intro α
  exact (mul_le_mul_of_nonneg_left (polynomial_le_prod_one_add P x α) zero_le).trans (hprod α)

noncomputable def weight (P : MTProcess S ι) (p : ι → ℝ≥0) : ℕ → ι → ℝ≥0
  | 0, α => p α
  | D + 1, α => p α * polynomial P (weight P p D) α

theorem weight_le (P : MTProcess S ι) (p x : ι → ℝ≥0)
    (h_self : ∀ α, p α * polynomial P x α ≤ x α) :
    ∀ D α, weight P p D α ≤ x α := by
  intro D
  induction D with
  | zero =>
    intro α
    change p α ≤ x α
    calc
      p α = p α * 1 := (mul_one _).symm
      _ ≤ p α * polynomial P x α :=
        mul_le_mul_of_nonneg_left (one_le_polynomial P x α) zero_le
      _ ≤ x α := h_self α
  | succ D ih =>
    intro α
    change p α * polynomial P (weight P p D) α ≤ x α
    exact (mul_le_mul_of_nonneg_left (polynomial_mono P (weight P p D) x ih α)
      zero_le).trans (h_self α)

noncomputable def treesUpTo (P : MTProcess S ι) : ℕ → ι → Finset (WTree ι)
  | 0, α => {WTree.mk α []}
  | D + 1, α => (independentSubsets P α).biUnion (fun T =>
      (T.pi (fun β => treesUpTo P D β)).image (fun choice =>
        WTree.mk α (T.attach.toList.map (fun p => choice p.1 p.2))))

theorem treesUpTo_subset (P : MTProcess S ι) :
    ∀ D α, treesUpTo P D α ⊆ wtreesUpTo P D α := by
  intro D
  induction D with
  | zero => intro α; exact Finset.Subset.refl _
  | succ D ih =>
    intro α t ht
    simp only [treesUpTo, Finset.mem_biUnion, Finset.mem_image, Finset.mem_pi] at ht
    obtain ⟨T, hT, choice, hc, rfl⟩ := ht
    simp only [wtreesUpTo, Finset.mem_biUnion, Finset.mem_image, Finset.mem_pi]
    exact ⟨T, Finset.mem_powerset.mpr ((mem_independentSubsets P α T).mp hT).1,
      choice, fun β hβ => ih β (hc β hβ), rfl⟩

theorem treesUpTo_mono (P : MTProcess S ι) :
    ∀ D α, treesUpTo P D α ⊆ treesUpTo P (D + 1) α := by
  intro D
  induction D with
  | zero =>
    intro α t ht
    simp only [treesUpTo, Finset.mem_singleton] at ht
    subst ht
    simp only [treesUpTo, Finset.mem_biUnion, Finset.mem_image]
    refine ⟨∅, empty_mem_independentSubsets P α,
      fun β hβ => absurd hβ (Finset.notMem_empty β), ?_, ?_⟩
    · rw [Finset.mem_pi]
      intro β hβ
      exact absurd hβ (Finset.notMem_empty β)
    · simp
  | succ D ih =>
    intro α t ht
    simp only [treesUpTo, Finset.mem_biUnion, Finset.mem_image] at ht ⊢
    obtain ⟨T, hT, choice, hc, ht⟩ := ht
    rw [Finset.mem_pi] at hc
    refine ⟨T, hT, choice, ?_, ht⟩
    rw [Finset.mem_pi]
    intro β hβ
    exact ih β (hc β hβ)

theorem treesUpTo_mono_le (P : MTProcess S ι) :
    ∀ D D' α, D ≤ D' → treesUpTo P D α ⊆ treesUpTo P D' α := by
  intro D D' α hle
  induction D', hle using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ k _ ih => exact ih.trans (treesUpTo_mono P k α)

theorem treesUpTo_succ_disjoint (P : MTProcess S ι) (D : ℕ) (α : ι) :
    (↑(independentSubsets P α) : Set (Finset ι)).PairwiseDisjoint
      (fun T => (T.pi (fun β => treesUpTo P D β)).image (fun choice =>
        WTree.mk α (T.attach.toList.map (fun p => choice p.1 p.2)))) := by
  intro T1 hT1 T2 hT2 hne
  have hdis := wtreesUpTo_succ_disjoint P D α
    (Finset.mem_powerset.mpr ((mem_independentSubsets P α T1).mp hT1).1)
    (Finset.mem_powerset.mpr ((mem_independentSubsets P α T2).mp hT2).1) hne
  apply hdis.mono
  · apply Finset.image_mono
    intro choice hc
    rw [Finset.mem_pi] at hc ⊢
    intro β hβ
    exact treesUpTo_subset P D β (hc β hβ)
  · apply Finset.image_mono
    intro choice hc
    rw [Finset.mem_pi] at hc ⊢
    intro β hβ
    exact treesUpTo_subset P D β (hc β hβ)

theorem sum_treesUpTo_weight_le (P : MTProcess S ι) (p : ι → ℝ≥0) :
    ∀ D α, ∑ t ∈ treesUpTo P D α, t.weight p ≤ weight P p D α := by
  intro D
  induction D with
  | zero =>
    intro α
    simp [treesUpTo, weight, WTree.weight_singleton]
  | succ D ih =>
    intro α
    show ∑ t ∈ (independentSubsets P α).biUnion (fun T =>
        (T.pi (fun β => treesUpTo P D β)).image (fun choice =>
          WTree.mk α (T.attach.toList.map (fun p => choice p.1 p.2)))), t.weight p ≤ _
    rw [Finset.sum_biUnion (treesUpTo_succ_disjoint P D α)]
    have hinner : ∀ T ∈ independentSubsets P α,
        (∑ t ∈ (T.pi (fun β => treesUpTo P D β)).image (fun choice =>
          WTree.mk α (T.attach.toList.map (fun p => choice p.1 p.2))), t.weight p)
        ≤ p α * ∏ b ∈ T, weight P p D b := by
      intro T _
      have hinj : Set.InjOn (fun choice : ∀ a ∈ T, WTree ι =>
          WTree.mk α (T.attach.toList.map (fun p => choice p.1 p.2)))
          (T.pi (fun β => treesUpTo P D β) : Finset (∀ a ∈ T, WTree ι)) := by
        intro x hx y hy
        apply wtreesUpTo_succ_injOn P D α T
        · exact Finset.mem_pi.mpr (fun β hβ =>
            treesUpTo_subset P D β (Finset.mem_pi.mp hx β hβ))
        · exact Finset.mem_pi.mpr (fun β hβ =>
            treesUpTo_subset P D β (Finset.mem_pi.mp hy β hβ))
      rw [Finset.sum_image hinj]
      simp_rw [weight_mk_attach]
      rw [← Finset.mul_sum]
      calc
        _ = p α * ∏ b ∈ T, ∑ t ∈ treesUpTo P D b, t.weight p := by
          rw [Finset.prod_sum]
        _ ≤ p α * ∏ b ∈ T, weight P p D b :=
          mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun b _ => ih b)) zero_le
    calc
      _ ≤ ∑ T ∈ independentSubsets P α, p α * ∏ b ∈ T, weight P p D b :=
        Finset.sum_le_sum hinner
      _ = weight P p (D + 1) α := by
        rw [← Finset.mul_sum]
        rfl

end Pegden


/-! ## Actual witnesses belong to the smaller family -/

namespace Pegden

open MeasureTheory Classical
open scoped NNReal ENNReal

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Actual witness trees satisfy this global depth condition, stronger than
    the independent-sibling condition used by the Pegden enumeration. -/
def DepthIndependent (P : MTProcess S ι) (t : WTree ι) : Prop :=
  ∀ d a b, a ∈ WTree.labelsAtDepth t d → b ∈ WTree.labelsAtDepth t d →
    a ≠ b → ¬ neighbor P a b

theorem mem_labelsAtDepthChildren_of_mem (cs : List (WTree ι))
    (c : WTree ι) (hc : c ∈ cs) (d : ℕ) (a : ι)
    (ha : a ∈ WTree.labelsAtDepth c d) :
    a ∈ WTree.labelsAtDepthChildren cs d := by
  induction cs with
  | nil => simp at hc
  | cons c' cs ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Multiset.mem_add.mpr (Or.inl ha)
    · exact Multiset.mem_add.mpr (Or.inr (ih hc))

theorem depthIndependent_child (P : MTProcess S ι) (t c : WTree ι)
    (ht : DepthIndependent P t) (hc : c ∈ t.children) :
    DepthIndependent P c := by
  cases t with
  | mk i cs =>
    intro d a b ha hb hab
    exact ht (d + 1) a b
      (mem_labelsAtDepthChildren_of_mem cs c hc d a ha)
      (mem_labelsAtDepthChildren_of_mem cs c hc d b hb) hab

theorem depthIndependent_labelSet (P : MTProcess S ι) (t : WTree ι)
    (ht : DepthIndependent P t) : Independent P t.labelSet := by
  intro a ha b hb hab
  obtain ⟨ca, hca, hla⟩ := (t.mem_labelSet_iff a).mp ha
  obtain ⟨cb, hcb, hlb⟩ := (t.mem_labelSet_iff b).mp hb
  have hroot (c : WTree ι) : c.label ∈ WTree.labelsAtDepth c 0 := by
    cases c
    simp [WTree.labelsAtDepth, WTree.label]
  cases t with
  | mk i cs =>
    apply ht 1 a b _ _ hab
    · rw [← hla]
      exact mem_labelsAtDepthChildren_of_mem cs ca hca 0 ca.label (hroot ca)
    · rw [← hlb]
      exact mem_labelsAtDepthChildren_of_mem cs cb hcb 0 cb.label (hroot cb)

theorem canonicalizeFuel_mem_treesUpTo (P : MTProcess S ι) :
    ∀ n (t : WTree ι), WTree.WellFormed P t → DepthIndependent P t →
      WTree.canonicalizeFuel n t ∈ treesUpTo P n t.label := by
  intro n
  induction n with
  | zero =>
    intro t _ _
    exact Finset.mem_singleton_self _
  | succ n ih =>
    intro t hwf hdi
    cases t with
    | mk i cs =>
      unfold WTree.WellFormed at hwf
      have hwf1 : ∀ c ∈ cs, c.label = i ∨ neighbor P i c.label := hwf.1
      have hwf2 : ∀ c ∈ cs, WTree.WellFormed P c := hwf.2
      have hTsub : (WTree.mk i cs).labelSet ⊆ plusNeighbors P i := by
        intro β hβ
        obtain ⟨c, hcmem, hclab⟩ := (WTree.mk i cs).mem_labelSet_iff β |>.mp hβ
        have h := hwf1 c hcmem
        rw [hclab] at h
        simpa only [plusNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] using h
      simp only [WTree.canonicalizeFuel, WTree.label, treesUpTo, Finset.mem_biUnion,
        independentSubsets, Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
      refine ⟨(WTree.mk i cs).labelSet, ⟨hTsub, depthIndependent_labelSet P _ hdi⟩,
        fun β hβ => WTree.canonicalizeFuel n ((WTree.mk i cs).childOf β hβ), ?_, rfl⟩
      rw [Finset.mem_pi]
      intro β hβ
      have hc := (WTree.mk i cs).childOf_mem β hβ
      have h := ih ((WTree.mk i cs).childOf β hβ) (hwf2 _ hc)
        (depthIndependent_child P _ _ hdi hc)
      rwa [(WTree.mk i cs).childOf_label β hβ] at h

theorem canonicalize_mem_treesUpTo (P : MTProcess S ι) (t : WTree ι)
    (hwf : WTree.WellFormed P t) (hdi : DepthIndependent P t) :
    WTree.canonicalize t ∈ treesUpTo P t.depth t.label :=
  canonicalizeFuel_mem_treesUpTo P t.depth t hwf hdi

theorem toWTree_depthIndependent (P : MTProcess S ι) (T : GrowingTree ι)
    (hV : T.Valid) (hroot : ([] : List ℕ) ∈ T.dom)
    (hSDI : SameDepthIndependent P T) : DepthIndependent P (T.toWTree []) := by
  intro d i j hi hj hij
  rw [GrowingTree.labelsAtDepth_toWTree_eq T hV hroot d] at hi hj
  rw [Multiset.mem_map] at hi hj
  obtain ⟨w1, hw1, hlab1⟩ := hi
  obtain ⟨w2, hw2, hlab2⟩ := hj
  simp only [Finset.mem_val, Finset.mem_filter] at hw1 hw2
  have hne : w1 ≠ w2 := by
    intro heq
    rw [heq] at hlab1
    exact hij (hlab1.symm.trans hlab2)
  have h := (hSDI w1 w2 hw1.1 hw2.1 (hw1.2.trans hw2.2.symm) hne).2
  rwa [hlab1, hlab2] at h

theorem τC_toWTree_depthIndependent (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) :
    DepthIndependent P ((τC P C t).toWTree []) :=
  toWTree_depthIndependent P (τC P C t) (τC_valid P C t) (τC_root_mem P C t)
    (τBuild_sameDepthIndependent P C t (t - 1))

/-- Every actually occurring canonical witness lies in the smaller enumeration
    whose children have pairwise nonadjacent labels. -/
theorem witnessOccurrence_nonempty_mem_treesUpTo (P : MTProcess S ι)
    (α : ι) (U : WTree ι) (hocc : (witnessOccurrence P α U).Nonempty) :
    ∃ D : ℕ, U ∈ treesUpTo P D α := by
  obtain ⟨ω, s, hs, hshape⟩ := hocc
  have hraw := τC_toWTree_wellFormed_proper P
    (shiftedC P (initialStateFromLog ω) ω) (s + 1)
  have hdi := τC_toWTree_depthIndependent P
    (shiftedC P (initialStateFromLog ω) ω) (s + 1)
  have hcanonical := canonicalize_mem_treesUpTo P
    ((τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)).toWTree [])
    hraw.2.1 hdi
  have hlabel :
      ((τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)).toWTree []).label = α :=
    hraw.1.trans ((shiftedC_succ P (initialStateFromLog ω) ω s).trans hs.2)
  have hcanonicalShape : WTree.canonicalize
      ((τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)).toWTree []) = U := hshape
  refine ⟨((τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)).toWTree []).depth, ?_⟩
  rw [← hcanonicalShape, ← hlabel]
  exact hcanonical

end Pegden


/-! ## The unbounded family and the probabilistic conclusion

The finite enumerations are canonical, so sibling permutations are not counted
again. Every finite part of their union lies in one depth bound. This gives a
bound for the countable sum without assuming termination or summability.
-/

namespace Pegden

open MeasureTheory Classical
open scoped NNReal ENNReal

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι]

/-- Canonical strongly proper witnesses, with no fixed depth bound. -/
def family (P : MTProcess S ι) (α : ι) : Set (WTree ι) :=
  {U | ∃ D : ℕ, U ∈ treesUpTo P D α}

/-- The usual product weight, restricted to the smaller canonical family. -/
noncomputable def familyWeight (P : MTProcess S ι) (p : ι → ℝ≥0)
    (α : ι) (U : WTree ι) : ℝ≥0∞ :=
  (family P α).indicator (fun T => (T.weight p : ℝ≥0∞)) U

theorem exists_treesUpTo_superset (P : MTProcess S ι) (α : ι)
    (F : Finset (WTree ι)) (hF : ∀ U ∈ F, U ∈ family P α) :
    ∃ D : ℕ, F ⊆ treesUpTo P D α := by
  classical
  revert hF
  induction F using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, Finset.empty_subset _⟩
  | insert U F _hnot ih =>
    intro hF
    obtain ⟨d, hd⟩ := hF U (Finset.mem_insert_self U F)
    obtain ⟨D, hD⟩ := ih (fun T hT => hF T (Finset.mem_insert_of_mem hT))
    refine ⟨max d D, ?_⟩
    intro T hT
    rcases Finset.mem_insert.mp hT with hTU | hTF
    · subst T
      exact treesUpTo_mono_le P d (max d D) α (le_max_left _ _) hd
    · exact treesUpTo_mono_le P D (max d D) α (le_max_right _ _) (hD hTF)

/-- Pegden's budget controls the whole family, not just a fixed depth. -/
theorem tsum_familyWeight_le (P : MTProcess S ι) (p x : ι → ℝ≥0)
    (h_self : ∀ α, p α * polynomial P x α ≤ x α) (α : ι) :
    (∑' U : WTree ι, familyWeight P p α U) ≤ (x α : ℝ≥0∞) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  let G : Finset (WTree ι) := F.filter (fun U => U ∈ family P α)
  have hG : ∀ U ∈ G, U ∈ family P α := by
    intro U hU
    exact (Finset.mem_filter.mp hU).2
  obtain ⟨D, hD⟩ := exists_treesUpTo_superset P α G hG
  calc
    (∑ U ∈ F, familyWeight P p α U) =
        ∑ U ∈ G, (U.weight p : ℝ≥0∞) := by
      simp only [G, familyWeight, Set.indicator_apply, Finset.sum_filter]
    _ ≤ ∑ U ∈ treesUpTo P D α, (U.weight p : ℝ≥0∞) :=
      Finset.sum_le_sum_of_subset hD
    _ ≤ (weight P p D α : ℝ≥0∞) := by
      rw [← ENNReal.ofNNReal_finsetSum]
      exact ENNReal.coe_le_coe.mpr (sum_treesUpTo_weight_le P p D α)
    _ ≤ (x α : ℝ≥0∞) :=
      ENNReal.coe_le_coe.mpr (weight_le P p x h_self D α)

variable [Nonempty ι]

/-- A witness outside the strongly proper canonical family never occurs. -/
theorem witnessOccurrence_eq_empty_of_not_mem_family (P : MTProcess S ι)
    (α : ι) (U : WTree ι) (hU : U ∉ family P α) :
    witnessOccurrence P α U = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ω hω
  exact hU (witnessOccurrence_nonempty_mem_treesUpTo P α U ⟨ω, hω⟩)

/-- The existing witness probability bound, with impossible shapes removed. -/
theorem logMeasure_witnessOccurrence_le_familyWeight [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ (p i : ℝ≥0∞))
    (α : ι) (U : WTree ι) :
    logMeasure S (witnessOccurrence P α U) ≤ familyWeight P p α U := by
  by_cases hU : U ∈ family P α
  · simpa only [familyWeight, Set.indicator_of_mem hU] using
      logMeasure_witnessOccurrence_le_weight P hbad p hp α U
  · rw [witnessOccurrence_eq_empty_of_not_mem_family P α U hU, measure_empty]
    exact zero_le

/-- Pegden, Theorem 1.4: the expected number of resamplings of each
event is bounded by its cluster-expansion budget. -/
theorem randomInitExpectedResamplingCount_le [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p x : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ (p i : ℝ≥0∞))
    (h_self : ∀ α, p α * polynomial P x α ≤ x α)
    (α : ι) : randomInitExpectedResamplingCount P α ≤ (x α : ℝ≥0∞) := by
  rw [randomInitExpectedResamplingCount_eq_tsum_witnessOccurrence P hbad α]
  exact (ENNReal.tsum_le_tsum (fun U =>
    logMeasure_witnessOccurrence_le_familyWeight P hbad p hp α U)).trans
      (tsum_familyWeight_le P p x h_self α)

/-- Pegden's expected-work bound for the existing MT process and its
slot-zero random initialization. No termination assumption is made. -/
theorem randomInitETLog_le_sum [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p x : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ (p i : ℝ≥0∞))
    (h_self : ∀ α, p α * polynomial P x α ≤ x α) :
    randomInitETLog P ≤ (↑(∑ α : ι, x α) : ℝ≥0∞) := by
  calc
    randomInitETLog P = ∑ α : ι, randomInitExpectedResamplingCount P α :=
      randomInitETLog_eq_sum_expectedResamplingCount P hbad
    _ ≤ ∑ α : ι, (x α : ℝ≥0∞) :=
      Finset.sum_le_sum (fun α _ =>
        randomInitExpectedResamplingCount_le P hbad p x hp h_self α)
    _ = (↑(∑ α : ι, x α) : ℝ≥0∞) := by
      rw [ENNReal.ofNNReal_finsetSum]

/-- The nonnegative real budgets are finite, so expected work is finite. -/
theorem randomInitETLog_lt_top [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p x : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ (p i : ℝ≥0∞))
    (h_self : ∀ α, p α * polynomial P x α ≤ x α) :
    randomInitETLog P < ⊤ :=
  lt_of_le_of_lt (randomInitETLog_le_sum P hbad p x hp h_self) ENNReal.coe_lt_top

/-- Almost-sure termination follows for the random-initialization law. -/
theorem ae_randomInit_exists_good [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p x : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ (p i : ℝ≥0∞))
    (h_self : ∀ α, p α * polynomial P x α ≤ x α) :
    ∀ᵐ ω ∂logMeasure S,
      ∃ T : ℕ, MTGood P (randTraj P (initialStateFromLog ω) ω T) :=
  _root_.ae_randomInit_exists_good P hbad
    (randomInitETLog_lt_top P hbad p x hp h_self)

/-- The stronger criterion also supplies the good-state existence witness. -/
theorem exists_MTGood [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p x : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ (p i : ℝ≥0∞))
    (h_self : ∀ α, p α * polynomial P x α ≤ x α) :
    ∃ z : MTState S, MTGood P z :=
  exists_MTGood_of_randomInitETLog_lt_top P hbad
    (randomInitETLog_lt_top P hbad p x hp h_self)

/-- As in the existing repair bridge, arbitrary-start reachability is
existential via the constant-log argument. It does not assert almost-sure
termination from every fixed initial state or preservation of a separate core. -/
theorem mtRepairGraph_globally_repairable [Fintype V]
    (P : MTProcess S ι) (edges : MTState S → MTState S → Prop)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (p x : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ (p i : ℝ≥0∞))
    (h_self : ∀ α, p α * polynomial P x α ≤ x α) :
    globally_repairable (mtRepairGraph P edges) :=
  mtRepairGraph_globally_repairable_of_randomInitETLog_lt_top P edges hbad
    (randomInitETLog_lt_top P hbad p x hp h_self)

end Pegden


/-! ## A strict improvement on a concrete finite probability space -/

namespace Pegden

open MeasureTheory
open scoped NNReal ENNReal

namespace TernaryExample

noncomputable def spaces : VarSpaces Unit where
  space _ := Fin 3
  measSpace _ := inferInstance
  measure _ := Measure.uniformOfFinset (Finset.univ : Finset (Fin 3))
  isProb _ := ⟨by
    norm_num [Measure.uniformOfFinset, Measure.finsetSum_apply]
    exact ENNReal.mul_inv_cancel (by norm_num) (by simp)⟩

instance spaceMeasurableSingleton (v : Unit) : MeasurableSingletonClass (spaces.space v) := by
  change MeasurableSingletonClass (Fin 3)
  infer_instance

def process : MTProcess spaces (Fin 2) where
  bad i := {ω | ω () = i.castLE (by decide)}
  footprint _ := Finset.univ
  dep i := by
    intro ω ω' h
    change (ω () = _) ↔ (ω' () = _)
    rw [h () (Finset.mem_univ ())]

theorem bad_measurable (i : Fin 2) : MeasurableSet (process.bad i) := by
  exact measurableSet_singleton _ |>.preimage (measurable_pi_apply ())

theorem bad_probability (i : Fin 2) :
    Measure.pi (fun v => spaces.measure v) (process.bad i) = (1 / 3 : ℝ≥0∞) := by
  have : ∀ v, IsProbabilityMeasure (spaces.measure v) := spaces.isProb
  have h := measurePreserving_eval (μ := fun v => spaces.measure v) ()
  calc
    Measure.pi (fun v => spaces.measure v) (process.bad i) =
        spaces.measure () ({(i.castLE (by decide) : spaces.space ())}) :=
      h.measure_preimage (measurableSet_singleton _)
    _ = (1 / 3 : ℝ≥0∞) := by
      change Measure.uniformOfFinset (Finset.univ : Finset (Fin 3))
        {(i.castLE (by decide) : Fin 3)} = _
      norm_num [Measure.uniformOfFinset_apply_singleton]

theorem all_neighbor (i j : Fin 2) : neighbor process i j := by
  simp [neighbor, process]

theorem plusNeighbors_eq_univ (i : Fin 2) : plusNeighbors process i = Finset.univ := by
  classical
  ext j
  simp [plusNeighbors, all_neighbor]

theorem independentSubsets_eq (i : Fin 2) :
    independentSubsets process i = {∅, {0}, {1}} := by
  classical
  rw [independentSubsets, plusNeighbors_eq_univ]
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
  simp only [Independent, all_neighbor, not_true_eq_false]
  fin_cases T <;> decide

theorem polynomial_one (i : Fin 2) : polynomial process (fun _ => 1) i = 3 := by
  classical
  rw [polynomial, independentSubsets_eq]
  norm_num

theorem criterion (i : Fin 2) :
    (1 / 3 : ℝ≥0) * polynomial process (fun _ => 1) i ≤ 1 := by
  rw [polynomial_one]
  norm_num

theorem good_target : ∀ i : Fin 2, (fun _ : Unit => (2 : Fin 3)) ∉ process.bad i := by
  intro i
  change (2 : Fin 3) ≠ i.castLE (by decide)
  fin_cases i <;> decide

theorem no_old_product_budget : ¬ ∃ x : Fin 2 → ℝ≥0,
    ∀ i, (1 / 3 : ℝ≥0) * ∏ j ∈ plusNeighbors process i, (1 + x j) ≤ x i := by
  rintro ⟨x, hx⟩
  have h0 := hx 0
  have h1 := hx 1
  simp only [plusNeighbors_eq_univ, Fin.prod_univ_two] at h0 h1
  have h0' : (1 / 3 : ℝ) * ((1 + (x 0 : ℝ)) * (1 + (x 1 : ℝ))) ≤ x 0 := by
    exact_mod_cast h0
  have h1' : (1 / 3 : ℝ) * ((1 + (x 0 : ℝ)) * (1 + (x 1 : ℝ))) ≤ x 1 := by
    exact_mod_cast h1
  rcases le_total (x 0 : ℝ) (x 1 : ℝ) with h | h
  · nlinarith [sq_nonneg ((x 0 : ℝ) - 1 / 2),
      mul_nonneg (show 0 ≤ (x 0 : ℝ) from (x 0).property) (sub_nonneg.mpr h)]
  · nlinarith [sq_nonneg ((x 1 : ℝ) - 1 / 2),
      mul_nonneg (show 0 ≤ (x 1 : ℝ) from (x 1).property) (sub_nonneg.mpr h)]

end TernaryExample
end Pegden


namespace Pegden.TernaryExample

open MeasureTheory
open scoped NNReal ENNReal

/-- The stronger criterion certifies an expected resampling count at most two for the
uniformly initialized ternary example. -/
theorem expected_work_le_two : randomInitETLog process ≤ 2 := by
  have hp : ∀ i, Measure.pi (fun v => spaces.measure v) (process.bad i) ≤
      ((1 / 3 : ℝ≥0) : ℝ≥0∞) := by
    intro i
    rw [bad_probability]
    norm_num
  simpa [Fin.sum_univ_two] using
    (Pegden.randomInitETLog_le_sum process bad_measurable
      (fun _ => (1 / 3 : ℝ≥0)) (fun _ => 1) hp criterion)

/-- Both parts refer to the same process and the exact same event probabilities. -/
theorem strictly_extends_product_criterion :
    randomInitETLog process ≤ 2 ∧
      ¬ ∃ x : Fin 2 → ℝ≥0,
        ∀ i, (1 / 3 : ℝ≥0) * ∏ j ∈ plusNeighbors process i, (1 + x j) ≤ x i :=
  ⟨expected_work_le_two, no_old_product_budget⟩

end Pegden.TernaryExample


-- Check every theorem introduced in this module.

#check @Pegden.independent_empty
#check @Pegden.independent_singleton
#check @Pegden.Independent.mono
#check @Pegden.mem_independentSubsets
#check @Pegden.empty_mem_independentSubsets
#check @Pegden.polynomial_mono
#check @Pegden.one_le_polynomial
#check @Pegden.polynomial_le_prod_one_add
#check @Pegden.product_budget_implies
#check @Pegden.weight_le
#check @Pegden.treesUpTo_subset
#check @Pegden.treesUpTo_mono
#check @Pegden.treesUpTo_mono_le
#check @Pegden.treesUpTo_succ_disjoint
#check @Pegden.sum_treesUpTo_weight_le
#check @Pegden.mem_labelsAtDepthChildren_of_mem
#check @Pegden.depthIndependent_child
#check @Pegden.depthIndependent_labelSet
#check @Pegden.canonicalizeFuel_mem_treesUpTo
#check @Pegden.canonicalize_mem_treesUpTo
#check @Pegden.toWTree_depthIndependent
#check @Pegden.τC_toWTree_depthIndependent
#check @Pegden.witnessOccurrence_nonempty_mem_treesUpTo
#check @Pegden.exists_treesUpTo_superset
#check @Pegden.tsum_familyWeight_le
#check @Pegden.witnessOccurrence_eq_empty_of_not_mem_family
#check @Pegden.logMeasure_witnessOccurrence_le_familyWeight
#check @Pegden.randomInitExpectedResamplingCount_le
#check @Pegden.randomInitETLog_le_sum
#check @Pegden.randomInitETLog_lt_top
#check @Pegden.ae_randomInit_exists_good
#check @Pegden.exists_MTGood
#check @Pegden.mtRepairGraph_globally_repairable
#check @Pegden.TernaryExample.bad_measurable
#check @Pegden.TernaryExample.bad_probability
#check @Pegden.TernaryExample.all_neighbor
#check @Pegden.TernaryExample.plusNeighbors_eq_univ
#check @Pegden.TernaryExample.independentSubsets_eq
#check @Pegden.TernaryExample.polynomial_one
#check @Pegden.TernaryExample.criterion
#check @Pegden.TernaryExample.good_target
#check @Pegden.TernaryExample.no_old_product_budget
#check @Pegden.TernaryExample.expected_work_le_two
#check @Pegden.TernaryExample.strictly_extends_product_criterion
