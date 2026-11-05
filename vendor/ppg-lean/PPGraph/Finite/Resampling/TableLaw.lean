/-
  The probability law of adaptive, local-counter table consumption.

  A finite state prefix fixes all consumed counters. Its event reads only
  consumed entries, while the next query reads disjoint unused entries.
  Product-measure independence proves the conditional fresh-input law.
  This does not assert independence of whole draw vectors across time:
  unselected coordinates may query the same unused entry more than once.
-/

module

public import PPGraph.Finite.Resampling.Table
public import PPGraph.MoserTardos.Probability.Probability
public import Mathlib.Probability.ConditionalExpectation

@[expose] public section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Classical
open scoped ENNReal NNReal

namespace FiniteTable

variable {V : Type} [Fintype V] [DecidableEq V] {S : VarSpaces V}
  [∀ v, Fintype (S.space v)] [∀ v, DecidableEq (S.space v)]
  [∀ v, MeasurableSingletonClass (S.space v)]

/-- Keep the existing MTState type explicit at the product-law boundary. -/
noncomputable def productLaw (S : VarSpaces V) : Measure (MTState S) :=
  Measure.pi (fun v => S.measure v)

instance productLaw_probability (S : VarSpaces V) : IsProbabilityMeasure (productLaw S) := by
  have : ∀ v, IsProbabilityMeasure (S.measure v) := S.isProb
  exact (inferInstance : IsProbabilityMeasure
    (Measure.pi (fun v => S.measure v) : Measure (∀ v, S.space v)))

theorem measurable_fixedDraw (c : V → ℕ) :
    Measurable (fun ω : LogSpace S => drawFrom ω c) := by
  apply Measurable.of_eval
  intro v
  exact measurable_pi_apply (c v, v)

theorem fixedDraw_map (c : V → ℕ) :
    (logMeasure S).map (fun ω : LogSpace S => drawFrom ω c) = productLaw S :=
  logMeasure_map_readAt_eq_pi c

def queryBlock (c : V → ℕ) : Finset (ℕ × V) :=
  Finset.univ.image (fun v => (c v + 1, v))

theorem consumed_query_disjoint (c : V → ℕ) :
    Disjoint (consumedBlock c) (queryBlock c) := by
  apply Finset.disjoint_left.mpr
  intro i hi hq
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hq
  have := (mem_consumedBlock c (c v + 1) v).mp hi
  omega

theorem fixed_query_event_depends (c : V → ℕ) (a : MTState S)
    (ω₁ ω₂ : LogSpace S)
    (ha : ∀ i ∈ queryBlock c, ω₁ i = ω₂ i) :
    drawFrom ω₁ (fun v => c v + 1) = a ↔ drawFrom ω₂ (fun v => c v + 1) = a := by
  have he : drawFrom ω₁ (fun v => c v + 1) = drawFrom ω₂ (fun v => c v + 1) := by
    funext v
    exact ha (c v + 1, v) (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩)
  rw [he]

/-- The next unused entries have the product law, conditional on a whole state prefix. -/
theorem prefix_nextDraw_atom (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (hi : Measurable init) (hl : InitialLocal init)
    (n : ℕ) (p : Path S n) (a : MTState S) :
    logMeasure S {ω | statePrefix F init n ω = p ∧ nextDraw F init n ω = a} =
      logMeasure S {ω | statePrefix F init n ω = p} *
        productLaw S {a} := by
  let c := pathCount F p
  have he : {ω | statePrefix F init n ω = p ∧ nextDraw F init n ω = a} =
      {ω | statePrefix F init n ω = p} ∩ {ω | drawFrom ω (fun v => c v + 1) = a} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hp, hd⟩
      have hc := count_of_prefix F init n ω p hp
      exact ⟨hp, by simpa only [nextDraw, hc, c] using hd⟩
    · rintro ⟨hp, hd⟩
      have hc := count_of_prefix F init n ω p hp
      exact ⟨hp, by simpa only [nextDraw, hc, c] using hd⟩
  rw [he]
  have ha := measurable_prefix F init hi n (measurableSet_singleton p)
  have hb := measurable_fixedDraw (S := S) (fun v => c v + 1) (measurableSet_singleton a)
  have hsplit := infinitePi_inter_eq_mul_of_dependsOn (μCoin S)
    (A := {ω | statePrefix F init n ω = p})
    (B := {ω | drawFrom ω (fun v => c v + 1) = a})
    (consumed_query_disjoint c)
    (prefix_event_depends_consumed F init hl n p) ha
    (fixed_query_event_depends c a) hb
  change Measure.infinitePi (μCoin S) _ = _
  rw [hsplit]
  congr 1
  rw [← fixedDraw_map (S := S) (fun v => c v + 1),
    Measure.map_apply (measurable_fixedDraw _) (measurableSet_singleton a)]
  rfl

theorem prefix_nextDraw_joint_law (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (hi : Measurable init) (hl : InitialLocal init)
    (n : ℕ) :
    (logMeasure S).map (fun ω => (statePrefix F init n ω, nextDraw F init n ω)) =
      ((logMeasure S).map (statePrefix F init n)).prod (productLaw S) := by
  have : ∀ v, IsProbabilityMeasure (S.measure v) := S.isProb
  apply Measure.ext_of_singleton
  intro ⟨p, a⟩
  rw [Measure.map_apply ((measurable_prefix F init hi n).prodMk
    (measurable_nextDraw F init hi n)) (measurableSet_singleton (p, a))]
  rw [← Set.singleton_prod_singleton, Measure.prod_prod,
    Measure.map_apply (measurable_prefix F init hi n) (measurableSet_singleton p)]
  rw [Set.mk_preimage_prod]
  convert prefix_nextDraw_atom F init hi hl n p a using 1 <;> congr 1

theorem nextDraw_map (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (hi : Measurable init) (hl : InitialLocal init)
    (n : ℕ) :
    (logMeasure S).map (nextDraw F init n) = productLaw S := by
  have : IsProbabilityMeasure ((logMeasure S).map (statePrefix F init n)) :=
    inferInstance
  have h := congrArg (fun μ : Measure (Path S n × MTState S) => μ.map Prod.snd)
    (prefix_nextDraw_joint_law F init hi hl n)
  rw [Measure.map_map measurable_snd
    ((measurable_prefix F init hi n).prodMk (measurable_nextDraw F init hi n)),
    Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h

theorem nextDraw_independent_prefix (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (hi : Measurable init) (hl : InitialLocal init)
    (n : ℕ) : IndepFun (nextDraw F init n) (statePrefix F init n) (logMeasure S) := by
  apply IndepFun.symm
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_prefix F init hi n).aemeasurable
    (measurable_nextDraw F init hi n).aemeasurable).mpr
  rw [nextDraw_map F init hi hl n]
  exact prefix_nextDraw_joint_law F init hi hl n

noncomputable def history (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (hi : Measurable init) :
    Filtration ℕ (inferInstance : MeasurableSpace (LogSpace S)) where
  seq n := MeasurableSpace.comap (statePrefix F init n) inferInstance
  mono' m n hmn := by
    apply MeasurableSpace.comap_le_comap_of_eq_comp
      (h := fun p : Path S n => fun k : Fin (m + 1) => p ⟨k.val, by omega⟩)
    · exact measurable_of_finite _
    · rfl
  le' n := (measurable_prefix F init hi n).comap_le

theorem trajectory_adapted (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (hi : Measurable init) (n : ℕ) :
    Measurable[history F init hi n] (trajectory F init n) := by
  exact (measurable_pi_apply (⟨n, by omega⟩ : Fin (n + 1))).comp
    (comap_measurable (statePrefix F init n))

theorem nextDraw_fresh (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (hi : Measurable init) (hl : InitialLocal init)
    (n : ℕ) (a : MTState S) :
    (logMeasure S)[FiniteDrift.stateIndicator (nextDraw F init n) a | history F init hi n]
      =ᵐ[logMeasure S] fun _ => (productLaw S {a}).toReal := by
  have hm : MeasurableSet[MeasurableSpace.comap (nextDraw F init n) inferInstance]
      {ω | nextDraw F init n ω = a} :=
    comap_measurable (nextDraw F init n) (measurableSet_singleton a)
  have hf : StronglyMeasurable[MeasurableSpace.comap (nextDraw F init n) inferInstance]
      (FiniteDrift.stateIndicator (nextDraw F init n) a) :=
    stronglyMeasurable_const.indicator hm
  have hc := condExp_indep_eq (measurable_nextDraw F init hi n).comap_le
    ((history F init hi).le n) hf (nextDraw_independent_prefix F init hi hl n)
  have hint : (∫ ω, FiniteDrift.stateIndicator (nextDraw F init n) a ω ∂logMeasure S) =
      (productLaw S {a}).toReal := by
    have he : {ω | nextDraw F init n ω = a} = nextDraw F init n ⁻¹' {a} := by
      ext ω; simp
    rw [FiniteDrift.stateIndicator, he]
    rw [integral_indicator_const (1 : ℝ)
        (measurable_nextDraw F init hi n (measurableSet_singleton a))]
    simp only [smul_eq_mul, mul_one, measureReal_def]
    rw [← Measure.map_apply (measurable_nextDraw F init hi n) (measurableSet_singleton a),
      nextDraw_map F init hi hl n]
  simpa only [hint] using hc

end FiniteTable

#check @FiniteTable.measurable_fixedDraw
#check @FiniteTable.fixedDraw_map
#check @FiniteTable.consumed_query_disjoint
#check @FiniteTable.fixed_query_event_depends
#check @FiniteTable.prefix_nextDraw_atom
#check @FiniteTable.prefix_nextDraw_joint_law
#check @FiniteTable.nextDraw_map
#check @FiniteTable.nextDraw_independent_prefix
#check @FiniteTable.trajectory_adapted
#check @FiniteTable.nextDraw_fresh
