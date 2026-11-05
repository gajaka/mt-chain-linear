/-
  PPGraphVariableLLL.lean
  Variable-Version Lovász Local Lemma (He, Li, Liu, Wang, Xia, FOCS 2017,
  "Variable-Version Lovász Local Lemma: Beyond Shearer's Bound",
  arXiv:1709.05143), geometric (GLLL) reformulation, Section 3.

  This file formalizes only Lemma 10 (p.8), the first step toward the
  paper's main result (Theorem 15, p.13, the full necessary-and-sufficient
  boundary characterization). Lemma 10 says: for any bigraph H and any
  probability vector p in (0,1)^n, the ray {lambda*p : lambda>0} crosses
  the feasibility boundary of H exactly once. The full Theorem 15 needs
  four more lemmas (11-14: a Fubini-based discretization induction, a
  convex-geometry/Caratheodory argument, a compactness argument, and a
  mass-shifting argument) that are each multi-page arguments in the paper
  and are NOT attempted here - see the project notes for why only Lemma 10
  is in scope for now.

  Honest gap relative to the paper: the paper's proof of Lemma 10 ends
  "It is easy to see that lambda_0*p is in the boundary" without further
  argument. That step is NOT free in Lean - it needs the fact that a
  cylinder can always be grown (within its own dependency coordinates) to
  any larger prescribed measure up to 1. This file proves that fact from
  scratch (`exists_cylinder_superset_measure_eq`), since the Mathlib
  version pinned by this project has no ready-made "non-atomic measure ->
  intermediate values achieved by subsets" theorem to call directly. The
  construction: grow the cylinder along one dependency coordinate up to a
  cutoff t; the resulting family of cylinders is 1-Lipschitz in t (moving
  the cutoff by delta changes the measure by at most delta); the
  intermediate value theorem then hits the target measure exactly.

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Topology

noncomputable section

variable {n m : ℕ}

-- Section 1: the geometric (GLLL) reformulation of variable-LLL [§3.1, p.8].
-- 𝕀^m is realized as (Fin m → ℝ) together with the product measure of m
-- copies of Lebesgue measure restricted to [0,1]; a subset that only
-- "sees" [0,1]^m matters, everything outside contributes measure zero.

instance instIsProbabilityMeasureRestrictIccZeroOne :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  simp

/-- μ from the paper: product Lebesgue measure on ℝ^m, restricted
    coordinate-wise to [0,1]. -/
def cubeMeasure (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi (fun _ : Fin m => volume.restrict (Set.Icc (0 : ℝ) 1))

instance cubeMeasure.instIsProbabilityMeasure (m : ℕ) :
    IsProbabilityMeasure (cubeMeasure m) := by
  unfold cubeMeasure; infer_instance

/-- eval at one coordinate is measure-preserving from cubeMeasure to the
    base [0,1]-restricted Lebesgue measure - the "marginal" of the cube
    measure along any single coordinate. -/
theorem measurePreserving_eval_cube (j₀ : Fin m) :
    MeasurePreserving (Function.eval j₀) (cubeMeasure m) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  measurePreserving_eval (μ := fun _ : Fin m => volume.restrict (Set.Icc (0 : ℝ) 1)) j₀

/-- The measure of a single-coordinate slice [Ioc s t] pulled back through
    eval j₀, for 0 ≤ s ≤ t ≤ 1, equals exactly t - s. This is the box-measure
    computation underlying the Lipschitz bound in Section 4. -/
theorem cubeMeasure_slice_eq (j₀ : Fin m) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    cubeMeasure m (Function.eval j₀ ⁻¹' Set.Ioc s t) = ENNReal.ofReal (t - s) := by
  have h := measurePreserving_eval_cube (m := m) j₀
  have hint : Set.Ioc s t ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc s t := by
    apply Set.inter_eq_left.mpr
    intro x hx
    exact ⟨hs.trans hx.1.le, hx.2.trans ht⟩
  rw [← Measure.map_apply h.measurable measurableSet_Ioc, h.map_eq,
    Measure.restrict_apply measurableSet_Ioc, hint, Real.volume_Ioc]

-- Section 2: bigraphs, cylinders, conforms-with [Def. before Thm 15, p.8].
-- Simplification relative to the paper: we require a cylinder to depend on
-- AT MOST the dependency set given by H, not exactly that set (the paper's
-- `dim(B) = S` convention). This does not affect Lemma 10 (which is
-- agnostic to the precise conforms-with convention) and keeps the
-- formalization tractable.

/-- A bigraph H = ([n],[m],E): n events, m variables, dep i = the variables
    event i depends on (dim(A_i) in the paper's notation). -/
structure Bigraph (n m : ℕ) where
  dep : Fin n → Finset (Fin m)

/-- A ⊆ ℝ^m depends only on the coordinates in S: agreeing on S forces the
    same membership regardless of the other coordinates. Matches the
    paper's cylinder shape A = B × 𝕀^{[m]\S} [p.8], stated pointwise. -/
def IsCylinderOver (S : Finset (Fin m)) (A : Set (Fin m → ℝ)) : Prop :=
  ∀ x y : Fin m → ℝ, (∀ j ∈ S, x j = y j) → (x ∈ A ↔ y ∈ A)

theorem IsCylinderOver.mono {S T : Finset (Fin m)} (hST : S ⊆ T) {A : Set (Fin m → ℝ)}
    (h : IsCylinderOver S A) : IsCylinderOver T A :=
  fun x y hxy => h x y (fun j hj => hxy j (hST hj))

theorem IsCylinderOver.union {S : Finset (Fin m)} {A B : Set (Fin m → ℝ)}
    (hA : IsCylinderOver S A) (hB : IsCylinderOver S B) : IsCylinderOver S (A ∪ B) :=
  fun x y hxy => by rw [Set.mem_union, Set.mem_union, hA x y hxy, hB x y hxy]

theorem isCylinderOver_singleton_preimage (j₀ : Fin m) (s : Set ℝ) :
    IsCylinderOver ({j₀} : Finset (Fin m)) (Function.eval j₀ ⁻¹' s) := by
  intro x y hxy
  simp only [Set.mem_preimage, Function.eval]
  rw [hxy j₀ (Finset.mem_singleton_self j₀)]

/-- A family A of measurable sets conforms with H if each A_i depends only
    on H's dependency set for event i. -/
def ConformsWith (H : Bigraph n m) (A : Fin n → Set (Fin m → ℝ)) : Prop :=
  ∀ i, MeasurableSet (A i) ∧ IsCylinderOver (H.dep i) (A i)

-- Section 3: interior, exterior, boundary [Definitions 1-3, p.8].

/-- p ∈ Interior(H): p lies in (0,1)^n, and for EVERY cylinder set A
    conforming with H at measure vector p, the intersection of complements
    has positive measure [Definition 1]. -/
def Interior (H : Bigraph n m) (p : Fin n → ℝ) : Prop :=
  (∀ i, p i ∈ Set.Ioo (0 : ℝ) 1) ∧
    ∀ A : Fin n → Set (Fin m → ℝ), ConformsWith H A →
      (∀ i, cubeMeasure m (A i) = ENNReal.ofReal (p i)) →
      0 < cubeMeasure m (⋂ i, (A i)ᶜ)

def Exterior (H : Bigraph n m) (p : Fin n → ℝ) : Prop := ¬ Interior H p

/-- The boundary [Definition 3]: p such that scaling down (any amount) lands
    in the interior, and scaling up (any amount) leaves it. -/
def Boundary (H : Bigraph n m) (p : Fin n → ℝ) : Prop :=
  ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
    Interior H (fun i => (1 - ε) * p i) ∧ ¬ Interior H (fun i => (1 + ε) * p i)

-- Section 4: the two directional facts from Lemma 10's proof [p.8].

/-- If some coordinate of p is ≥ 1, p is trivially not in the interior -
    Interior H p requires p ∈ (0,1)^n by definition, so this is immediate
    from the domain restriction, no measure-theoretic argument needed. This
    is the "large λ" half of Lemma 10's proof. -/
theorem not_interior_of_ge_one (H : Bigraph n m) (p : Fin n → ℝ) (i : Fin n) (hi : 1 ≤ p i) :
    ¬ Interior H p := by
  rintro ⟨hdom, -⟩
  exact absurd (hdom i).2 (not_lt.mpr hi)

/-- If the coordinates of p are in (0,1) and sum to less than 1, p is in the
    interior - the union bound / subadditivity argument. This is the
    "small λ" half of Lemma 10's proof. -/
theorem interior_of_sum_lt_one (H : Bigraph n m) (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Ioo (0 : ℝ) 1) (hsum : ∑ i, p i < 1) : Interior H p := by
  refine ⟨hp, ?_⟩
  intro A hA hmeas
  have hcompl_eq : ⋂ i, (A i)ᶜ = (⋃ i, A i)ᶜ := (Set.compl_iUnion A).symm
  have hmeasU : MeasurableSet (⋃ i, A i) := MeasurableSet.iUnion (fun i => (hA i).1)
  have hunion_le : cubeMeasure m (⋃ i, A i) ≤ ∑ i, cubeMeasure m (A i) :=
    measure_iUnion_fintype_le (cubeMeasure m) A
  have hsum_eq : ∑ i, cubeMeasure m (A i) = ENNReal.ofReal (∑ i, p i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => (hp i).1.le)]
    exact Finset.sum_congr rfl (fun i _ => hmeas i)
  have hunion_lt : cubeMeasure m (⋃ i, A i) < 1 := by
    calc cubeMeasure m (⋃ i, A i) ≤ ∑ i, cubeMeasure m (A i) := hunion_le
      _ = ENNReal.ofReal (∑ i, p i) := hsum_eq
      _ < ENNReal.ofReal 1 := ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr hsum
      _ = 1 := by simp
  have hne_top : cubeMeasure m (⋃ i, A i) ≠ ⊤ := ne_top_of_lt hunion_lt
  rw [hcompl_eq, measure_compl hmeasU hne_top,
    show cubeMeasure m Set.univ = 1 from IsProbabilityMeasure.measure_univ]
  exact tsub_pos_of_lt hunion_lt

-- Section 5: extending a cylinder to a larger prescribed measure.
-- This is the fact the paper's Lemma 10 leans on via "it is easy to see"
-- without proof - see the file header. Built here via a 1-Lipschitz
-- "grow along one coordinate" family and the intermediate value theorem,
-- decomposed into small top-level lemmas mirroring the PVS-style
-- granularity used for the General/Lopsided LLL files.

/-- Grows A along coordinate j₀ up to cutoff t: A ∪ {x : x j₀ ≤ t}. The
    family {growAlong A j₀ t}_t interpolates A's measure up to 1 as t runs
    over [0,1]. -/
def growAlong (A : Set (Fin m → ℝ)) (j₀ : Fin m) (t : ℝ) : Set (Fin m → ℝ) :=
  A ∪ Function.eval j₀ ⁻¹' Set.Iic t

theorem growAlong_measurable {A : Set (Fin m → ℝ)} (hA : MeasurableSet A) (j₀ : Fin m) (t : ℝ) :
    MeasurableSet (growAlong A j₀ t) :=
  hA.union (measurableSet_Iic.preimage (measurable_pi_apply j₀))

theorem growAlong_cylinderOver {S : Finset (Fin m)} {A : Set (Fin m → ℝ)}
    (hcyl : IsCylinderOver S A) {j₀ : Fin m} (hj₀ : j₀ ∈ S) (t : ℝ) :
    IsCylinderOver S (growAlong A j₀ t) :=
  hcyl.union ((isCylinderOver_singleton_preimage j₀ (Set.Iic t)).mono
    (Finset.singleton_subset_iff.mpr hj₀))

theorem growAlong_subset (A : Set (Fin m → ℝ)) (j₀ : Fin m) (t : ℝ) :
    A ⊆ growAlong A j₀ t := Set.subset_union_left

theorem growAlong_mono (A : Set (Fin m → ℝ)) (j₀ : Fin m) {s t : ℝ} (hst : s ≤ t) :
    growAlong A j₀ s ⊆ growAlong A j₀ t :=
  Set.union_subset_union_right A (fun x hx => le_trans hx hst)

theorem growAlong_ne_top (A : Set (Fin m → ℝ)) (j₀ : Fin m) (t : ℝ) :
    cubeMeasure m (growAlong A j₀ t) ≠ ⊤ := by
  have h : cubeMeasure m (growAlong A j₀ t) ≤ cubeMeasure m Set.univ :=
    measure_mono (Set.subset_univ _)
  rw [show cubeMeasure m Set.univ = 1 from IsProbabilityMeasure.measure_univ] at h
  exact ne_top_of_le_ne_top (by norm_num) h

/-- The part gained by growing from s to t is confined to the coordinate-j₀
    slice (s,t] - the key fact behind the Lipschitz bound below. -/
theorem growAlong_diff_subset_slice (A : Set (Fin m → ℝ)) (j₀ : Fin m) {s t : ℝ} (hst : s ≤ t) :
    growAlong A j₀ t \ growAlong A j₀ s ⊆ Function.eval j₀ ⁻¹' Set.Ioc s t := by
  intro x hx
  obtain ⟨hxFt, hxFs⟩ := hx
  simp only [growAlong, Set.mem_union, Set.mem_preimage, Set.mem_Iic] at hxFt hxFs
  push Not at hxFs
  rcases hxFt with hxA | hxle
  · exact absurd hxA hxFs.1
  · exact ⟨hxFs.2, hxle⟩

/-- The real-valued measure of growAlong, as a function of the cutoff - the
    object whose continuity is what "it is easy to see" is secretly about. -/
noncomputable def growAlongToReal (A : Set (Fin m → ℝ)) (j₀ : Fin m) (t : ℝ) : ℝ :=
  (cubeMeasure m (growAlong A j₀ t)).toReal

/-- One Lipschitz step: growing the cutoff from s to t (both in [0,1]) can
    only increase the measure by at most t - s. -/
theorem growAlong_measure_step_le (A : Set (Fin m → ℝ)) (j₀ : Fin m) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    growAlongToReal A j₀ t ≤ growAlongToReal A j₀ s + (t - s) := by
  show (cubeMeasure m (growAlong A j₀ t)).toReal ≤
    (cubeMeasure m (growAlong A j₀ s)).toReal + (t - s)
  have hle : cubeMeasure m (growAlong A j₀ t \ growAlong A j₀ s) ≤ ENNReal.ofReal (t - s) :=
    le_trans (measure_mono (growAlong_diff_subset_slice A j₀ hst))
      (le_of_eq (cubeMeasure_slice_eq j₀ hs hst ht))
  have hslice_ne_top : cubeMeasure m (growAlong A j₀ t \ growAlong A j₀ s) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hFt_eq : growAlong A j₀ t = growAlong A j₀ s ∪ growAlong A j₀ t \ growAlong A j₀ s :=
    (Set.union_sdiff_cancel (growAlong_mono A j₀ hst)).symm
  have hunion_le : cubeMeasure m (growAlong A j₀ t) ≤
      cubeMeasure m (growAlong A j₀ s) + cubeMeasure m (growAlong A j₀ t \ growAlong A j₀ s) := by
    conv_lhs => rw [hFt_eq]
    exact measure_union_le (growAlong A j₀ s) (growAlong A j₀ t \ growAlong A j₀ s)
  have h1 : (cubeMeasure m (growAlong A j₀ t)).toReal ≤
      (cubeMeasure m (growAlong A j₀ s) +
        cubeMeasure m (growAlong A j₀ t \ growAlong A j₀ s)).toReal :=
    ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨growAlong_ne_top A j₀ s, hslice_ne_top⟩)
      hunion_le
  have h2 : (cubeMeasure m (growAlong A j₀ s) +
      cubeMeasure m (growAlong A j₀ t \ growAlong A j₀ s)).toReal ≤
      (cubeMeasure m (growAlong A j₀ s)).toReal + (t - s) := by
    rw [ENNReal.toReal_add (growAlong_ne_top A j₀ s) hslice_ne_top]
    gcongr
    calc (cubeMeasure m (growAlong A j₀ t \ growAlong A j₀ s)).toReal ≤
        (ENNReal.ofReal (t - s)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = t - s := ENNReal.toReal_ofReal (by linarith)
  linarith [h1, h2]

theorem growAlongToReal_mono (A : Set (Fin m → ℝ)) (j₀ : Fin m) {s t : ℝ} (hst : s ≤ t) :
    growAlongToReal A j₀ s ≤ growAlongToReal A j₀ t := by
  show (cubeMeasure m (growAlong A j₀ s)).toReal ≤ (cubeMeasure m (growAlong A j₀ t)).toReal
  exact ENNReal.toReal_mono (growAlong_ne_top A j₀ t) (measure_mono (growAlong_mono A j₀ hst))

theorem growAlongToReal_continuousOn (A : Set (Fin m → ℝ)) (j₀ : Fin m) :
    ContinuousOn (growAlongToReal A j₀) (Set.Icc (0 : ℝ) 1) := by
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |growAlongToReal A j₀ s - growAlongToReal A j₀ t| ≤ |s - t| := by
    intro s hs t ht
    rcases le_total s t with hst | hst
    · rw [abs_of_nonpos (by linarith [growAlongToReal_mono A j₀ hst] :
          growAlongToReal A j₀ s - growAlongToReal A j₀ t ≤ 0),
        abs_of_nonpos (by linarith : s - t ≤ 0)]
      linarith [growAlong_measure_step_le A j₀ hs.1 hst ht.2]
    · rw [abs_of_nonneg (by linarith [growAlongToReal_mono A j₀ hst] :
          0 ≤ growAlongToReal A j₀ s - growAlongToReal A j₀ t),
        abs_of_nonneg (by linarith : 0 ≤ s - t)]
      linarith [growAlong_measure_step_le A j₀ ht.1 hst hs.2]
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  refine ⟨ε, hε, fun a ha hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  exact lt_of_le_of_lt (hbound a ha b hb) hdist

theorem cubeMeasure_eval_Iic_zero (j₀ : Fin m) :
    cubeMeasure m (Function.eval j₀ ⁻¹' Set.Iic (0 : ℝ)) = 0 := by
  have h := measurePreserving_eval_cube (m := m) j₀
  rw [← Measure.map_apply h.measurable measurableSet_Iic, h.map_eq,
    Measure.restrict_apply measurableSet_Iic]
  have hset : Set.Iic (0 : ℝ) ∩ Set.Icc (0 : ℝ) 1 = {0} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, _⟩; linarith
    · rintro rfl; norm_num
  rw [hset]
  simp

theorem cubeMeasure_eval_Iic_one (j₀ : Fin m) :
    cubeMeasure m (Function.eval j₀ ⁻¹' Set.Iic (1 : ℝ)) = 1 := by
  have h := measurePreserving_eval_cube (m := m) j₀
  rw [← Measure.map_apply h.measurable measurableSet_Iic, h.map_eq,
    Measure.restrict_apply measurableSet_Iic]
  have hset : Set.Iic (1 : ℝ) ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨_, h2⟩; exact h2
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2⟩
  rw [hset, Real.volume_Icc]
  norm_num

theorem growAlongToReal_zero {A : Set (Fin m → ℝ)} (hA : MeasurableSet A) (j₀ : Fin m) :
    growAlongToReal A j₀ 0 = (cubeMeasure m A).toReal := by
  have heq : cubeMeasure m (growAlong A j₀ 0) = cubeMeasure m A := by
    apply le_antisymm
    · calc cubeMeasure m (growAlong A j₀ 0)
          ≤ cubeMeasure m A + cubeMeasure m (Function.eval j₀ ⁻¹' Set.Iic (0 : ℝ)) :=
            measure_union_le A (Function.eval j₀ ⁻¹' Set.Iic (0 : ℝ))
        _ = cubeMeasure m A := by rw [cubeMeasure_eval_Iic_zero, add_zero]
    · exact measure_mono (growAlong_subset A j₀ 0)
  show (cubeMeasure m (growAlong A j₀ 0)).toReal = (cubeMeasure m A).toReal
  rw [heq]

theorem growAlongToReal_one (A : Set (Fin m → ℝ)) (j₀ : Fin m) : growAlongToReal A j₀ 1 = 1 := by
  have hle : cubeMeasure m (growAlong A j₀ 1) ≤ 1 := by
    rw [← show cubeMeasure m Set.univ = 1 from IsProbabilityMeasure.measure_univ]
    exact measure_mono (Set.subset_univ _)
  have hge : (1 : ENNReal) ≤ cubeMeasure m (growAlong A j₀ 1) := by
    rw [← cubeMeasure_eval_Iic_one j₀]
    exact measure_mono Set.subset_union_right
  show (cubeMeasure m (growAlong A j₀ 1)).toReal = 1
  rw [le_antisymm hle hge]
  simp

theorem exists_cylinder_superset_measure_eq {S : Finset (Fin m)} {A : Set (Fin m → ℝ)}
    (hA : MeasurableSet A) (hcyl : IsCylinderOver S A) (j₀ : Fin m) (hj₀ : j₀ ∈ S)
    (q q' : ℝ) (hq : cubeMeasure m A = ENNReal.ofReal q) (hq0 : 0 ≤ q) (hqq' : q ≤ q')
    (hq'1 : q' ≤ 1) :
    ∃ B : Set (Fin m → ℝ), A ⊆ B ∧ MeasurableSet B ∧ IsCylinderOver S B ∧
      cubeMeasure m B = ENNReal.ofReal q' := by
  have hg0 : growAlongToReal A j₀ 0 = q := by
    rw [growAlongToReal_zero hA j₀, hq]; exact ENNReal.toReal_ofReal hq0
  have hg1 : growAlongToReal A j₀ 1 = 1 := growAlongToReal_one A j₀
  have hmem : q' ∈ Set.Icc (growAlongToReal A j₀ 0) (growAlongToReal A j₀ 1) :=
    ⟨by rw [hg0]; exact hqq', by rw [hg1]; exact hq'1⟩
  obtain ⟨t, -, ht_eq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (growAlongToReal_continuousOn A j₀) hmem
  refine ⟨growAlong A j₀ t, growAlong_subset A j₀ t, growAlong_measurable hA j₀ t,
    growAlong_cylinderOver hcyl hj₀ t, ?_⟩
  have hEq : ENNReal.ofReal (growAlongToReal A j₀ t) = cubeMeasure m (growAlong A j₀ t) :=
    ENNReal.ofReal_toReal (growAlong_ne_top A j₀ t)
  rw [ht_eq] at hEq
  exact hEq.symm

-- Section 6: Interior is downward closed along a ray, using the extension
-- lemma above. This is the "easy to see" step Lemma 10's proof leans on.

/-- If Interior holds at λ₂•p, it holds at any smaller λ₁•p too (0 < λ₁ ≤
    λ₂), provided λ₂•p stays in (0,1]^n. Grows a witnessing cylinder set at
    λ₁ up to λ₂ coordinate by coordinate via
    exists_cylinder_superset_measure_eq, then transfers positivity from the
    (smaller) complement of the grown set to the (bigger) complement of the
    original. -/
theorem interior_mono_ray (H : Bigraph n m) (p : Fin n → ℝ) (hp : ∀ i, 0 < p i)
    (hHne : ∀ i, (H.dep i).Nonempty) {lam1 lam2 : ℝ} (h1 : 0 < lam1) (h12 : lam1 ≤ lam2)
    (hle1 : ∀ i, lam2 * p i ≤ 1) (h2 : Interior H (fun i => lam2 * p i)) :
    Interior H (fun i => lam1 * p i) := by
  obtain ⟨hdom2, hint2⟩ := h2
  have hdom1 : ∀ i, (fun i => lam1 * p i) i ∈ Set.Ioo (0 : ℝ) 1 := by
    intro i
    refine ⟨mul_pos h1 (hp i), ?_⟩
    calc lam1 * p i ≤ lam2 * p i := mul_le_mul_of_nonneg_right h12 (hp i).le
      _ < 1 := (hdom2 i).2
  refine ⟨hdom1, ?_⟩
  intro A hA hmeas
  choose B hAB hBmeas hBcyl hBmeas_eq using
    fun i => exists_cylinder_superset_measure_eq (hA i).1 (hA i).2
      (hHne i).choose (hHne i).choose_spec (lam1 * p i) (lam2 * p i)
      (hmeas i) (mul_nonneg h1.le (hp i).le) (mul_le_mul_of_nonneg_right h12 (hp i).le) (hle1 i)
  have hBconforms : ConformsWith H B := fun i => ⟨hBmeas i, hBcyl i⟩
  have hpos2 := hint2 B hBconforms hBmeas_eq
  have hsubset : (⋂ i, (B i)ᶜ) ⊆ ⋂ i, (A i)ᶜ :=
    Set.iInter_mono (fun i => Set.compl_subset_compl.mpr (hAB i))
  exact lt_of_lt_of_le hpos2 (measure_mono hsubset)

-- Section 7: Lemma 10 [p.8].

-- The exterior-along-the-ray set: lam is in it when lam*p is already
-- known to be outside the interior. Lemma 10's lam0 is sInf of this set,
-- top-level so the proof can be split into small named lemmas mirroring
-- the granularity used elsewhere in this project.

def Lam_of (H : Bigraph n m) (p : Fin n → ℝ) : Set ℝ :=
  {lam : ℝ | 0 < lam ∧ ¬ Interior H (fun i => lam * p i)}

theorem sum_pos_of_mem_Ioo [Nonempty (Fin n)] {p : Fin n → ℝ}
    (hp : ∀ i, p i ∈ Set.Ioo (0 : ℝ) 1) : 0 < ∑ i, p i :=
  Finset.sum_pos (fun i _ => (hp i).1) Finset.univ_nonempty

theorem Lam_of_nonempty [Nonempty (Fin n)] (H : Bigraph n m) (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Ioo (0 : ℝ) 1) : (Lam_of H p).Nonempty := by
  obtain ⟨i0⟩ := ‹Nonempty (Fin n)›
  refine ⟨1 / p i0, div_pos one_pos (hp i0).1, ?_⟩
  apply not_interior_of_ge_one H _ i0
  show (1 : ℝ) ≤ 1 / p i0 * p i0
  rw [one_div, inv_mul_cancel₀ (hp i0).1.ne']

/-- Small λ (λ·∑p < 1) never lands in Lam_of - the "small λ" half of Lemma
    10's proof [p.8], via interior_of_sum_lt_one, bounds Lam_of below by
    1/∑p. -/
theorem Lam_of_lower_bound [Nonempty (Fin n)] (H : Bigraph n m) (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Ioo (0 : ℝ) 1) : ∀ lam ∈ Lam_of H p, 1 / (∑ i, p i) ≤ lam := by
  have hpsum_pos := sum_pos_of_mem_Ioo hp
  rintro lam ⟨hlam_pos, hlam_ext⟩
  by_contra hcon
  push Not at hcon
  apply hlam_ext
  apply interior_of_sum_lt_one H (fun i => lam * p i) (fun i =>
    ⟨mul_pos hlam_pos (hp i).1, by
      have : lam * p i ≤ lam * ∑ j, p j :=
        mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => (hp j).1.le)
          (Finset.mem_univ i)) hlam_pos.le
      calc lam * p i ≤ lam * ∑ j, p j := this
        _ < 1 := by
          rw [lt_div_iff₀ hpsum_pos] at hcon; linarith⟩)
  rw [← Finset.mul_sum]
  rw [lt_div_iff₀ hpsum_pos] at hcon
  linarith

theorem Lam_of_sInf_pos [Nonempty (Fin n)] (H : Bigraph n m) (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Ioo (0 : ℝ) 1) : 0 < sInf (Lam_of H p) :=
  lt_of_lt_of_le (div_pos one_pos (sum_pos_of_mem_Ioo hp))
    (le_csInf (Lam_of_nonempty H p hp) (Lam_of_lower_bound H p hp))

/-- (1-ε)·λ₀ is strictly below sInf (Lam_of H p), hence not in it, hence
    Interior holds there - the lower half of Boundary's two conjuncts. -/
theorem boundary_lower [Nonempty (Fin n)] (H : Bigraph n m) (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Ioo (0 : ℝ) 1) {eps : ℝ} (heps : eps ∈ Set.Ioo (0 : ℝ) 1) :
    Interior H (fun i => (1 - eps) * sInf (Lam_of H p) * p i) := by
  have hBddBelow : BddBelow (Lam_of H p) := ⟨1 / (∑ i, p i), Lam_of_lower_bound H p hp⟩
  have hlam0_pos := Lam_of_sInf_pos H p hp
  have hnotmem : (1 - eps) * sInf (Lam_of H p) ∉ Lam_of H p := by
    intro hmem
    have hle := csInf_le hBddBelow hmem
    nlinarith [heps.1, heps.2, hlam0_pos]
  have hpos : 0 < (1 - eps) * sInf (Lam_of H p) := by nlinarith [heps.1, heps.2, hlam0_pos]
  rcases not_and_or.mp hnotmem with h | h
  · exact absurd hpos h
  · exact not_not.mp h

/-- (1+ε)·λ₀ is never in the interior: either some coordinate already hits
    1 (immediate), or - since λ₀ is the infimum - a witness λ' < (1+ε)λ₀ in
    Lam_of exists, and interior_mono_ray transports its non-interior-ness
    up to (1+ε)λ₀. -/
theorem boundary_upper [Nonempty (Fin n)] (H : Bigraph n m) (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Ioo (0 : ℝ) 1) (hHne : ∀ i, (H.dep i).Nonempty)
    {eps : ℝ} (heps : eps ∈ Set.Ioo (0 : ℝ) 1) :
    ¬ Interior H (fun i => (1 + eps) * sInf (Lam_of H p) * p i) := by
  have hlam0_pos := Lam_of_sInf_pos H p hp
  by_cases hge1 : ∃ i, (1 + eps) * sInf (Lam_of H p) * p i ≥ 1
  · obtain ⟨i, hi⟩ := hge1
    exact not_interior_of_ge_one H _ i hi
  · push Not at hge1
    have hgt : sInf (Lam_of H p) < (1 + eps) * sInf (Lam_of H p) := by
      nlinarith [heps.1, hlam0_pos]
    obtain ⟨lam', hlam'_mem, hlam'_lt⟩ := exists_lt_of_csInf_lt (Lam_of_nonempty H p hp) hgt
    intro hint
    apply hlam'_mem.2
    exact interior_mono_ray H p (fun i => (hp i).1) hHne hlam'_mem.1 hlam'_lt.le
      (fun i => (hge1 i).le) hint

/-- Lemma 10: for any bigraph H whose events all have nonempty dependency
    sets, and any p ∈ (0,1)^n, there is a unique λ > 0 with λp on the
    boundary of H. (The "nonempty dependency set" side condition is not in
    the paper's statement; it rules out the degenerate case of an event
    depending on no variables at all, needed for interior_mono_ray's
    extension construction to have a coordinate to grow along.) -/
theorem lll_variable_lemma10 [Nonempty (Fin n)] (H : Bigraph n m)
    (hHne : ∀ i, (H.dep i).Nonempty) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ lam : ℝ, 0 < lam ∧ Boundary H (fun i => lam * p i) := by
  refine ⟨sInf (Lam_of H p), Lam_of_sInf_pos H p hp, ?_⟩
  intro eps heps
  simp only [← mul_assoc]
  exact ⟨boundary_lower H p hp heps, boundary_upper H p hp hHne heps⟩

-- Verification

#check @cubeMeasure
#check @measurePreserving_eval_cube
#check @cubeMeasure_slice_eq
#check @IsCylinderOver
#check @ConformsWith
#check @Interior
#check @Exterior
#check @Boundary
#check @not_interior_of_ge_one
#check @interior_of_sum_lt_one
#check @growAlong
#check @growAlong_measurable
#check @growAlong_cylinderOver
#check @growAlong_subset
#check @growAlong_mono
#check @growAlong_ne_top
#check @growAlong_diff_subset_slice
#check @growAlongToReal
#check @growAlong_measure_step_le
#check @growAlongToReal_mono
#check @growAlongToReal_continuousOn
#check @cubeMeasure_eval_Iic_zero
#check @cubeMeasure_eval_Iic_one
#check @growAlongToReal_zero
#check @growAlongToReal_one
#check @exists_cylinder_superset_measure_eq
#check @interior_mono_ray
#check @Lam_of
#check @sum_pos_of_mem_Ioo
#check @Lam_of_nonempty
#check @Lam_of_lower_bound
#check @Lam_of_sInf_pos
#check @boundary_lower
#check @boundary_upper
#check @lll_variable_lemma10

-- Explicit checks for all remaining helper theorems.
#check @IsCylinderOver.mono
#check @IsCylinderOver.union
#check @isCylinderOver_singleton_preimage
