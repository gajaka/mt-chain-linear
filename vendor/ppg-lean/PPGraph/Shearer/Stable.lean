/-
  PPGraphShearerStable.lean

  Shearer coefficients and the Kolipaka--Szegedy bound for stable set
  sequences. Source: Harvey and Vondrak, "An Algorithmic Proof of the
  Lovasz Local Lemma via Resampling Oracles", arXiv:1504.02044v3,
  Claims 5.14--5.16, Lemmas 5.17 and 5.26.
  https://arxiv.org/abs/1504.02044

  The existing polynomial is the lower-indexed avoidance polynomial.
  The coefficients below are the upper-indexed q_J used in the algorithmic
  bound. All identities connecting the two are proved here.
-/

module

public import PPGraph.Shearer.Polynomial
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical
open scoped ENNReal

namespace Shearer

variable {ι : Type*} [DecidableEq ι]

/-- The weight of an independent set, zero for a non-independent set. -/
noncomputable def setWeight (G : SimpleGraph ι) (p : ι → ℝ) (J : Finset ι) : ℝ :=
  if Independent G J then ∏ j ∈ J, p j else 0

/-- The upper-indexed Shearer coefficient, expressed by disjoint extensions
of J inside B. For J outside B the coefficient is defined to be zero. -/
noncomputable def coefficient (G : SimpleGraph ι) (p : ι → ℝ)
    (B J : Finset ι) : ℝ :=
  if J ⊆ B then
    ∑ K ∈ (B \ J).powerset, (-1 : ℝ) ^ K.card * setWeight G p (J ∪ K)
  else 0

/-- The closed neighborhood of J, restricted to the finite event family B. -/
noncomputable def closed (G : SimpleGraph ι) (B J : Finset ι) : Finset ι :=
  B.filter (fun b => b ∈ J ∨ ∃ a ∈ J, G.Adj a b)

/-- Labels outside the closed neighborhood. -/
noncomputable def outside (G : SimpleGraph ι) (B J : Finset ι) : Finset ι :=
  B \ closed G B J

@[simp]
theorem mem_outside (G : SimpleGraph ι) (B J : Finset ι) (b : ι) :
    b ∈ outside G B J ↔ b ∈ B ∧ b ∉ J ∧ ∀ a ∈ J, ¬ G.Adj a b := by
  by_cases hb : b ∈ B <;> simp [outside, closed, hb]

theorem closed_subset (G : SimpleGraph ι) (B J : Finset ι) : closed G B J ⊆ B :=
  Finset.filter_subset _ _

theorem outside_subset (G : SimpleGraph ι) (B J : Finset ι) : outside G B J ⊆ B :=
  Finset.sdiff_subset

@[simp]
theorem closed_empty (G : SimpleGraph ι) (B : Finset ι) : closed G B ∅ = ∅ := by
  simp [closed]

@[simp]
theorem outside_empty (G : SimpleGraph ι) (B : Finset ι) : outside G B ∅ = B := by
  simp [outside]

@[simp]
theorem coefficient_empty (G : SimpleGraph ι) (p : ι → ℝ) (B : Finset ι) :
    coefficient G p B ∅ = polynomial G p B := by
  simp only [coefficient, Finset.empty_subset, ite_true, Finset.sdiff_empty,
    Finset.empty_union, polynomial, Finset.sum_filter, setWeight]
  apply Finset.sum_congr rfl
  intro K _
  split_ifs with hK
  · rw [Finset.prod_neg]
  · simp

theorem coefficient_eq_zero_of_not_independent (G : SimpleGraph ι) (p : ι → ℝ)
    (B J : Finset ι) (hJ : ¬ Independent G J) : coefficient G p B J = 0 := by
  unfold coefficient
  split_ifs with hJB
  · apply Finset.sum_eq_zero
    intro K _
    have hJK : ¬ Independent G (J ∪ K) :=
      fun h => hJ (Independent.mono G h Finset.subset_union_left)
    simp [setWeight, hJK]
  · rfl

/-- Splitting the ambient family by one label gives the cancellation
identity used in the finite inclusion-exclusion argument. -/
theorem coefficient_insert_split (G : SimpleGraph ι) (p : ι → ℝ)
    (B J : Finset ι) (a : ι) (ha : a ∉ B) (hJB : J ⊆ B) :
    coefficient G p (insert a B) J + coefficient G p (insert a B) (insert a J) =
      coefficient G p B J := by
  have haJ : a ∉ J := fun h => ha (hJB h)
  have hJ : J ⊆ insert a B := hJB.trans (Finset.subset_insert _ _)
  have hJa : insert a J ⊆ insert a B := Finset.insert_subset_insert a hJB
  have hdiff1 : insert a B \ J = insert a (B \ J) := by
    ext b
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    aesop
  have hdiff2 : insert a B \ insert a J = B \ J := by
    ext b
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    aesop
  have hafresh : a ∉ B \ J := fun h => ha (Finset.mem_sdiff.mp h).1
  simp only [coefficient, ite_eq_left hJ, ite_eq_left hJa, ite_eq_left hJB, hdiff1, hdiff2]
  rw [Finset.sum_powerset_insert hafresh]
  have hcancel :
      (∑ K ∈ (B \ J).powerset,
        (-1 : ℝ) ^ (insert a K).card * setWeight G p (J ∪ insert a K)) =
      -(∑ K ∈ (B \ J).powerset,
        (-1 : ℝ) ^ K.card * setWeight G p (insert a J ∪ K)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro K hK
    have haK : a ∉ K := fun h => hafresh (Finset.mem_powerset.mp hK h)
    rw [Finset.card_insert_of_notMem haK, pow_succ]
    have heq : J ∪ insert a K = insert a J ∪ K := by ext b; simp
    rw [heq]
    ring
  rw [hcancel]
  ring

/-- Claim 5.14: summing upper-indexed coefficients over subsets of U
recovers the avoidance polynomial on the complement of U. -/
theorem sum_coefficient (G : SimpleGraph ι) (p : ι → ℝ) (B U : Finset ι)
    (hUB : U ⊆ B) :
    (∑ J ∈ U.powerset, coefficient G p B J) = polynomial G p (B \ U) := by
  induction U using Finset.induction generalizing B with
  | empty => simp
  | @insert a U haU ih =>
    have haB : a ∈ B := hUB (Finset.mem_insert_self _ _)
    have hU : U ⊆ B.erase a := by
      intro b hb
      exact Finset.mem_erase.mpr ⟨(fun h => haU (h ▸ hb)),
        hUB (Finset.mem_insert_of_mem hb)⟩
    rw [Finset.sum_powerset_insert haU, ← Finset.sum_add_distrib]
    have heq : ∀ J ∈ U.powerset,
        coefficient G p B J + coefficient G p B (insert a J) =
          coefficient G p (B.erase a) J := by
      intro J hJ
      simpa only [Finset.insert_erase haB] using
        coefficient_insert_split G p (B.erase a) J a (Finset.notMem_erase _ _)
          ((Finset.mem_powerset.mp hJ).trans hU)
    rw [Finset.sum_congr rfl heq, ih (B.erase a) hU]
    congr 1
    ext b
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
    tauto

theorem independent_extension_filter (G : SimpleGraph ι) (B J : Finset ι)
    (hJ : Independent G J) :
    (B \ J).powerset.filter (fun K => Independent G (J ∪ K)) =
      (outside G B J).powerset.filter (Independent G) := by
  ext K
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hKB, hJK⟩
    refine ⟨?_, Independent.mono G hJK Finset.subset_union_right⟩
    intro b hb
    obtain ⟨hbB, hbJ⟩ := Finset.mem_sdiff.mp (hKB hb)
    exact (mem_outside G B J b).mpr ⟨hbB, hbJ,
      fun a ha => hJK a (Finset.mem_union_left K ha) b (Finset.mem_union_right J hb)⟩
  · rintro ⟨hKout, hK⟩
    refine ⟨?_, ?_⟩
    · intro b hb
      obtain ⟨hbB, hbJ, _⟩ := (mem_outside G B J b).mp (hKout hb)
      exact Finset.mem_sdiff.mpr ⟨hbB, hbJ⟩
    · intro a ha b hb
      rcases Finset.mem_union.mp ha with haJ | haK <;>
        rcases Finset.mem_union.mp hb with hbJ | hbK
      · exact hJ a haJ b hbJ
      · exact ((mem_outside G B J b).mp (hKout hbK)).2.2 a haJ
      · exact fun hadj => ((mem_outside G B J a).mp (hKout haK)).2.2 b hbJ hadj.symm
      · exact hK a haK b hbK

/-- Claim 5.16: factor a coefficient into the root-set probability and
the avoidance polynomial outside its closed neighborhood. -/
theorem coefficient_factor (G : SimpleGraph ι) (p : ι → ℝ) (B J : Finset ι)
    (hJB : J ⊆ B) (hJ : Independent G J) :
    coefficient G p B J = (∏ j ∈ J, p j) * polynomial G p (outside G B J) := by
  rw [coefficient, ite_eq_left hJB]
  have hfiltered :
      (∑ K ∈ (B \ J).powerset, (-1 : ℝ) ^ K.card * setWeight G p (J ∪ K)) =
      ∑ K ∈ (B \ J).powerset.filter (fun K => Independent G (J ∪ K)),
        (-1 : ℝ) ^ K.card * ∏ j ∈ J ∪ K, p j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro K _
    simp only [setWeight]
    split_ifs <;> simp
  rw [hfiltered, independent_extension_filter G B J hJ]
  unfold polynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K hK
  have hKout := Finset.mem_powerset.mp (Finset.mem_filter.mp hK).1
  have hdis : Disjoint J K := Finset.disjoint_left.mpr (by
    intro a haJ haK
    exact ((mem_outside G B J a).mp (hKout haK)).2.1 haJ)
  rw [Finset.prod_union hdis, Finset.prod_neg]
  ring

/-- Lemma 5.17: the coefficient vector is a fixed point of the stable-set
transition operator. This identity is proved from the explicit coefficients. -/
theorem coefficient_recurrence (G : SimpleGraph ι) (p : ι → ℝ) (B J : Finset ι)
    (hJB : J ⊆ B) (hJ : Independent G J) :
    coefficient G p B J =
      (∏ j ∈ J, p j) * ∑ K ∈ (closed G B J).powerset, coefficient G p B K := by
  rw [sum_coefficient G p B (closed G B J) (closed_subset G B J)]
  exact coefficient_factor G p B J hJB hJ

theorem coefficient_nonneg (G : SimpleGraph ι) (p : ι → ℝ) (B J : Finset ι)
    (hp : ∀ i ∈ B, 0 ≤ p i) (hcriterion : StrictCriterion G p B) :
    0 ≤ coefficient G p B J := by
  by_cases hJB : J ⊆ B
  · by_cases hJ : Independent G J
    · rw [coefficient_factor G p B J hJB hJ]
      exact mul_nonneg (Finset.prod_nonneg (fun i hi => hp i (hJB hi)))
        (hcriterion _ (outside_subset G B J)).le
    · rw [coefficient_eq_zero_of_not_independent G p B J hJ]
  · simp [coefficient, hJB]

/-- The allowed next independent layer, including the empty layer. -/
noncomputable def successors (G : SimpleGraph ι) (B J : Finset ι) : Finset (Finset ι) :=
  (closed G B J).powerset.filter (Independent G)

@[simp]
theorem mem_successors (G : SimpleGraph ι) (B J K : Finset ι) :
    K ∈ successors G B J ↔ K ⊆ closed G B J ∧ Independent G K := by
  simp [successors]

@[simp]
theorem empty_mem_successors (G : SimpleGraph ι) (B J : Finset ι) :
    ∅ ∈ successors G B J := by simp

@[simp]
theorem successors_empty (G : SimpleGraph ι) (B : Finset ι) :
    successors G B ∅ = {∅} := by simp [successors]

theorem coefficient_recurrence_independent (G : SimpleGraph ι) (p : ι → ℝ)
    (B J : Finset ι) (hJB : J ⊆ B) (hJ : Independent G J) :
    coefficient G p B J =
      (∏ j ∈ J, p j) * ∑ K ∈ successors G B J, coefficient G p B K := by
  rw [coefficient_recurrence G p B J hJB hJ]
  congr 1
  rw [successors, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro K _
  by_cases hK : Independent G K
  · simp [hK]
  · simp [hK, coefficient_eq_zero_of_not_independent G p B K hK]

/-- The finite Shearer budget for a root layer. -/
noncomputable def stableBudget (G : SimpleGraph ι) (p : ι → ℝ)
    (B J : Finset ι) : ℝ := coefficient G p B J / polynomial G p B

theorem stableBudget_nonneg (G : SimpleGraph ι) (p : ι → ℝ) (B J : Finset ι)
    (hp : ∀ i ∈ B, 0 ≤ p i) (hcriterion : StrictCriterion G p B) :
    0 ≤ stableBudget G p B J :=
  div_nonneg (coefficient_nonneg G p B J hp hcriterion)
    (hcriterion B Finset.Subset.rfl).le

@[simp]
theorem stableBudget_empty (G : SimpleGraph ι) (p : ι → ℝ) (B : Finset ι)
    (hcriterion : StrictCriterion G p B) : stableBudget G p B ∅ = 1 := by
  simp [stableBudget, ne_of_gt (hcriterion B Finset.Subset.rfl)]

theorem stableBudget_recurrence (G : SimpleGraph ι) (p : ι → ℝ) (B J : Finset ι)
    (hJB : J ⊆ B) (hJ : Independent G J) :
    stableBudget G p B J =
      (∏ j ∈ J, p j) * ∑ K ∈ successors G B J, stableBudget G p B K := by
  unfold stableBudget
  rw [coefficient_recurrence_independent G p B J hJB hJ, ← Finset.sum_div]
  ring

theorem prod_le_stableBudget (G : SimpleGraph ι) (p : ι → ℝ) (B J : Finset ι)
    (hJB : J ⊆ B) (hJ : Independent G J)
    (hp : ∀ i ∈ B, 0 ≤ p i) (hcriterion : StrictCriterion G p B) :
    (∏ j ∈ J, p j) ≤ stableBudget G p B J := by
  have hsum := Finset.single_le_sum
    (fun K (_ : K ∈ successors G B J) => stableBudget_nonneg G p B K hp hcriterion)
    (empty_mem_successors G B J)
  rw [stableBudget_empty G p B hcriterion] at hsum
  rw [stableBudget_recurrence G p B J hJB hJ]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsum
    (Finset.prod_nonneg (fun j hj => hp j (hJB hj)))

/-- All stable sequences of exactly d+1 layers starting with J. Empty
layers are allowed, and an empty layer can only be followed by empty layers. -/
noncomputable def stableSequences (G : SimpleGraph ι) (B : Finset ι) :
    ℕ → Finset ι → Finset (List (Finset ι))
  | 0, J => {[J]}
  | d + 1, J => (successors G B J).biUnion
      (fun K => (stableSequences G B d K).image (List.cons J))

noncomputable def sequenceWeight (p : ι → ℝ) (L : List (Finset ι)) : ℝ :=
  (L.map (fun J => ∏ j ∈ J, p j)).prod

@[simp]
theorem sequenceWeight_cons (p : ι → ℝ) (J : Finset ι) (L : List (Finset ι)) :
    sequenceWeight p (J :: L) = (∏ j ∈ J, p j) * sequenceWeight p L := rfl

theorem stableSequences_head_length (G : SimpleGraph ι) (B : Finset ι)
    (d : ℕ) (J : Finset ι) (L : List (Finset ι)) (hL : L ∈ stableSequences G B d J) :
    L.head? = some J ∧ L.length = d + 1 := by
  induction d generalizing J L with
  | zero =>
    simp only [stableSequences, Finset.mem_singleton] at hL
    subst L
    simp
  | succ d ih =>
    obtain ⟨K, _, hK⟩ := Finset.mem_biUnion.mp hL
    obtain ⟨L', hL', rfl⟩ := Finset.mem_image.mp hK
    have h := ih K L' hL'
    simp [h.2]

theorem stableSequences_next_disjoint (G : SimpleGraph ι) (B : Finset ι)
    (d : ℕ) (J K K' : Finset ι) (hne : K ≠ K') :
    Disjoint ((stableSequences G B d K).image (List.cons J))
      ((stableSequences G B d K').image (List.cons J)) := by
  apply Finset.disjoint_left.mpr
  intro L hL hL'
  obtain ⟨X, hX, hLX⟩ := Finset.mem_image.mp hL
  obtain ⟨Y, hY, hLY⟩ := Finset.mem_image.mp hL'
  have hXY : X = Y := List.cons.inj (hLX.trans hLY.symm) |>.2
  have hhead := (stableSequences_head_length G B d K X hX).1
  have hhead' := (stableSequences_head_length G B d K' Y hY).1
  exact hne (Option.some.inj (hhead.symm.trans ((congrArg List.head? hXY).trans hhead')))

/-- The actual finite enumeration satisfies the recurrence in equation (11)
of Harvey--Vondrak. No counting identity is assumed. -/
theorem sum_stableSequences_succ (G : SimpleGraph ι) (p : ι → ℝ)
    (B J : Finset ι) (d : ℕ) :
    (∑ L ∈ stableSequences G B (d + 1) J, sequenceWeight p L) =
      (∏ j ∈ J, p j) * ∑ K ∈ successors G B J,
        ∑ L ∈ stableSequences G B d K, sequenceWeight p L := by
  rw [stableSequences, Finset.sum_biUnion]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro K _
    rw [Finset.sum_image]
    · simp only [sequenceWeight_cons, Finset.mul_sum]
    · intro L _ L' _ h
      exact List.cons.inj h |>.2
  · intro K _ K' _ hne
    exact stableSequences_next_disjoint G B d J K K' hne

/-- Kolipaka--Szegedy, Harvey--Vondrak Lemma 5.26: every finite-depth sum
of stable-sequence weights is bounded by the explicit Shearer ratio. -/
theorem sum_stableSequences_le (G : SimpleGraph ι) (p : ι → ℝ)
    (B J : Finset ι) (d : ℕ) (hJB : J ⊆ B) (hJ : Independent G J)
    (hp : ∀ i ∈ B, 0 ≤ p i) (hcriterion : StrictCriterion G p B) :
    (∑ L ∈ stableSequences G B d J, sequenceWeight p L) ≤ stableBudget G p B J := by
  induction d generalizing J with
  | zero =>
    simpa [stableSequences, sequenceWeight] using
      prod_le_stableBudget G p B J hJB hJ hp hcriterion
  | succ d ih =>
    rw [sum_stableSequences_succ, stableBudget_recurrence G p B J hJB hJ]
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum
      intro K hK
      obtain ⟨hKsub, hKind⟩ := (mem_successors G B J K).mp hK
      exact ih K (hKsub.trans (closed_subset G B J)) hKind
    · exact Finset.prod_nonneg (fun j hj => hp j (hJB hj))

theorem stableSequences_layers (G : SimpleGraph ι) (B J : Finset ι) (d : ℕ)
    (hJB : J ⊆ B) (hJ : Independent G J)
    (L : List (Finset ι)) (hL : L ∈ stableSequences G B d J) :
    ∀ K ∈ L, K ⊆ B ∧ Independent G K := by
  induction d generalizing J L with
  | zero =>
    simp only [stableSequences, Finset.mem_singleton] at hL
    subst L
    intro K hK
    simp only [List.mem_singleton] at hK
    subst K
    exact ⟨hJB, hJ⟩
  | succ d ih =>
    obtain ⟨K, hK, hKseq⟩ := Finset.mem_biUnion.mp hL
    obtain ⟨tail, htail, rfl⟩ := Finset.mem_image.mp hKseq
    obtain ⟨hKsub, hKind⟩ := (mem_successors G B J K).mp hK
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact ⟨hJB, hJ⟩
    · exact ih K (hKsub.trans (closed_subset G B J)) hKind tail htail M hM

theorem sequenceWeight_nonneg (p : ι → ℝ) (L : List (Finset ι))
    (hp : ∀ J ∈ L, ∀ j ∈ J, 0 ≤ p j) : 0 ≤ sequenceWeight p L := by
  unfold sequenceWeight
  apply List.prod_nonneg
  intro x hx
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hx
  exact Finset.prod_nonneg (hp J hJ)

/-- Appending one empty layer preserves stability. -/
theorem stableSequences_append_empty (G : SimpleGraph ι) (B J : Finset ι) (d : ℕ)
    (L : List (Finset ι)) (hL : L ∈ stableSequences G B d J) :
    L ++ [∅] ∈ stableSequences G B (d + 1) J := by
  induction d generalizing J L with
  | zero =>
    simp only [stableSequences, Finset.mem_singleton] at hL
    subst L
    apply Finset.mem_biUnion.mpr
    refine ⟨∅, empty_mem_successors G B J, ?_⟩
    exact Finset.mem_image.mpr ⟨[∅], by simp [stableSequences], rfl⟩
  | succ d ih =>
    obtain ⟨K, hK, hKseq⟩ := Finset.mem_biUnion.mp hL
    obtain ⟨tail, htail, rfl⟩ := Finset.mem_image.mp hKseq
    exact Finset.mem_biUnion.mpr ⟨K, hK,
      Finset.mem_image.mpr ⟨tail ++ [∅], ih K tail htail, rfl⟩⟩

theorem stableSequences_append_padding (G : SimpleGraph ι) (B J : Finset ι) (d k : ℕ)
    (L : List (Finset ι)) (hL : L ∈ stableSequences G B d J) :
    L ++ List.replicate k ∅ ∈ stableSequences G B (d + k) J := by
  induction k with
  | zero => simpa using hL
  | succ k ih =>
    have h := stableSequences_append_empty G B J (d + k)
      (L ++ List.replicate k ∅) ih
    simpa [List.replicate_add, List.append_assoc, Nat.add_assoc] using h

/-- Pad a sequence to D+1 layers. It is used only when its length is at most D+1. -/
def padTo (D : ℕ) (L : List (Finset ι)) : List (Finset ι) :=
  L ++ List.replicate (D + 1 - L.length) ∅

theorem padTo_mem_stableSequences (G : SimpleGraph ι) (B J : Finset ι) (d D : ℕ)
    (L : List (Finset ι)) (hL : L ∈ stableSequences G B d J) (hdD : d ≤ D) :
    padTo D L ∈ stableSequences G B D J := by
  have hlen := (stableSequences_head_length G B d J L hL).2
  have h := stableSequences_append_padding G B J d (D - d) L hL
  have hnum : D + 1 - L.length = D - d := by omega
  simpa only [padTo, hnum, Nat.add_sub_of_le hdD] using h

@[simp]
theorem sequenceWeight_padTo (p : ι → ℝ) (D : ℕ) (L : List (Finset ι)) :
    sequenceWeight p (padTo D L) = sequenceWeight p L := by
  simp [sequenceWeight, padTo]

/-- Trimming at the first empty layer recovers every proper sequence,
so padding does not identify two different proper witnesses. -/
theorem takeWhile_padTo (D : ℕ) (L : List (Finset ι)) (hL : ∀ J ∈ L, J ≠ ∅) :
    (padTo D L).takeWhile (fun J => decide (J ≠ ∅)) = L := by
  unfold padTo
  rw [List.takeWhile_append_of_pos (fun J hJ => by simpa using hL J hJ)]
  simp

theorem padTo_injective_on_proper (D : ℕ) (L M : List (Finset ι))
    (hL : ∀ J ∈ L, J ≠ ∅) (hM : ∀ J ∈ M, J ≠ ∅)
    (h : padTo D L = padTo D M) : L = M := by
  have htrim := congrArg (List.takeWhile (fun J : Finset ι => decide (J ≠ ∅))) h
  simpa only [takeWhile_padTo D L hL, takeWhile_padTo D M hM] using htrim

/-- Proper stable sequences have no empty layers and no fixed depth bound. -/
def properFamily (G : SimpleGraph ι) (B J : Finset ι) : Set (List (Finset ι)) :=
  {L | (∃ d, L ∈ stableSequences G B d J) ∧ ∀ K ∈ L, K ≠ ∅}

noncomputable def properFamilyWeight (G : SimpleGraph ι) (p : ι → ℝ)
    (B J : Finset ι) (L : List (Finset ι)) : ℝ≥0∞ :=
  (properFamily G B J).indicator (fun M => ENNReal.ofReal (sequenceWeight p M)) L

theorem exists_padding_depth (G : SimpleGraph ι) (B J : Finset ι)
    (F : Finset (List (Finset ι))) (hF : ∀ L ∈ F, L ∈ properFamily G B J) :
    ∃ D, ∀ L ∈ F, padTo D L ∈ stableSequences G B D J := by
  refine ⟨F.sup List.length, ?_⟩
  intro L hL
  obtain ⟨d, hd⟩ := (hF L hL).1
  apply padTo_mem_stableSequences G B J d _ L hd
  have hlen := (stableSequences_head_length G B d J L hd).2
  have hmax := Finset.le_sup (f := List.length) hL
  omega

/-- The infinite sum over all proper stable sequences is finite and has
the same Shearer bound. Padding is injective and preserves every weight. -/
theorem tsum_properFamilyWeight_le (G : SimpleGraph ι) (p : ι → ℝ) (B J : Finset ι)
    (hJB : J ⊆ B) (hJ : Independent G J)
    (hp : ∀ i ∈ B, 0 ≤ p i) (hcriterion : StrictCriterion G p B) :
    (∑' L : List (Finset ι), properFamilyWeight G p B J L) ≤
      ENNReal.ofReal (stableBudget G p B J) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  let F' := F.filter (fun L => L ∈ properFamily G B J)
  have hF' : ∀ L ∈ F', L ∈ properFamily G B J :=
    fun L hL => (Finset.mem_filter.mp hL).2
  obtain ⟨D, hD⟩ := exists_padding_depth G B J F' hF'
  have hinj : ∀ L ∈ F', ∀ M ∈ F', padTo D L = padTo D M → L = M := by
    intro L hL M hM heq
    exact padTo_injective_on_proper D L M (hF' L hL).2 (hF' M hM).2 heq
  have himg : F'.image (padTo D) ⊆ stableSequences G B D J := by
    intro L hL
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hL
    exact hD M hM
  have hnonneg : ∀ L ∈ stableSequences G B D J, 0 ≤ sequenceWeight p L := by
    intro L hL
    apply sequenceWeight_nonneg
    intro K hK k hk
    exact hp k ((stableSequences_layers G B J D hJB hJ L hL K hK).1 hk)
  calc
    (∑ L ∈ F, properFamilyWeight G p B J L) =
        ∑ L ∈ F', ENNReal.ofReal (sequenceWeight p L) := by
      simp only [F', properFamilyWeight, Set.indicator_apply, Finset.sum_filter]
    _ = ∑ L ∈ F'.image (padTo D), ENNReal.ofReal (sequenceWeight p L) := by
      rw [Finset.sum_image hinj]
      simp only [sequenceWeight_padTo]
    _ ≤ ∑ L ∈ stableSequences G B D J, ENNReal.ofReal (sequenceWeight p L) :=
      Finset.sum_le_sum_of_subset himg
    _ = ENNReal.ofReal (∑ L ∈ stableSequences G B D J, sequenceWeight p L) :=
      (ENNReal.ofReal_sum_of_nonneg hnonneg).symm
    _ ≤ ENNReal.ofReal (stableBudget G p B J) :=
      ENNReal.ofReal_le_ofReal (sum_stableSequences_le G p B J D hJB hJ hp hcriterion)

theorem tsum_properFamilyWeight_lt_top (G : SimpleGraph ι) (p : ι → ℝ) (B J : Finset ι)
    (hJB : J ⊆ B) (hJ : Independent G J)
    (hp : ∀ i ∈ B, 0 ≤ p i) (hcriterion : StrictCriterion G p B) :
    (∑' L : List (Finset ι), properFamilyWeight G p B J L) < ⊤ :=
  (tsum_properFamilyWeight_le G p B J hJB hJ hp hcriterion).trans_lt ENNReal.ofReal_lt_top

end Shearer

#check @Shearer.mem_outside
#check @Shearer.closed_subset
#check @Shearer.outside_subset
#check @Shearer.closed_empty
#check @Shearer.outside_empty
#check @Shearer.coefficient_empty
#check @Shearer.coefficient_eq_zero_of_not_independent
#check @Shearer.coefficient_insert_split
#check @Shearer.sum_coefficient
#check @Shearer.independent_extension_filter
#check @Shearer.coefficient_factor
#check @Shearer.coefficient_recurrence
#check @Shearer.coefficient_nonneg
#check @Shearer.mem_successors
#check @Shearer.empty_mem_successors
#check @Shearer.successors_empty
#check @Shearer.coefficient_recurrence_independent
#check @Shearer.stableBudget_nonneg
#check @Shearer.stableBudget_empty
#check @Shearer.stableBudget_recurrence
#check @Shearer.prod_le_stableBudget
#check @Shearer.sequenceWeight_cons
#check @Shearer.stableSequences_head_length
#check @Shearer.stableSequences_next_disjoint
#check @Shearer.sum_stableSequences_succ
#check @Shearer.sum_stableSequences_le
#check @Shearer.stableSequences_layers
#check @Shearer.sequenceWeight_nonneg
#check @Shearer.stableSequences_append_empty
#check @Shearer.stableSequences_append_padding
#check @Shearer.padTo_mem_stableSequences
#check @Shearer.sequenceWeight_padTo
#check @Shearer.takeWhile_padTo
#check @Shearer.padTo_injective_on_proper
#check @Shearer.exists_padding_depth
#check @Shearer.tsum_properFamilyWeight_le
#check @Shearer.tsum_properFamilyWeight_lt_top
