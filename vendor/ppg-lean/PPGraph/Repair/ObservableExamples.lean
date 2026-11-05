/-
  Countermodels and positive examples for observable repair reduction.

  These are exact mathematical examples, not NFER traces or LUCES telemetry.
  A closed deterministic summary can change its observable values. A repair
  reading omitted information need not support that summary. In the stochastic
  example, the signal's conditional mean is always zero, while its square
  reveals a hidden difference. Generator checking alone is insufficient.
-/
module

public import PPGraph.Repair.ObservableKernel

@[expose] public section

set_option autoImplicit false

namespace RepairObservableExamples

open RepairObservable RepairObservableKernel

abbrev PairState := ℚ × ℚ

def firstAlgebra : Subalgebra ℚ (PairState → ℚ) := projectionAlgebra Prod.fst

def increment (s : PairState) : PairState := (s.1 + 1, s.2)

def swap (s : PairState) : PairState := (s.2, s.1)

theorem increment_stable : Stable (fun _ : Unit => increment) firstAlgebra :=
  projection_stable_of_factor _ Prod.fst (fun _ x => x + 1) (fun _ _ => rfl)

theorem increment_not_fixed : ¬ Fixed increment firstAlgebra := by
  intro h
  have hv := congrFun (h (pullback Prod.fst (id : ℚ → ℚ)) ⟨id, rfl⟩)
    ((0, 0) : PairState)
  simp only [pullback_apply, increment] at hv
  norm_num at hv

theorem swap_not_stable : ¬ Stable (fun _ : Unit => swap) firstAlgebra := by
  intro h
  have he : ObsEq firstAlgebra ((0, 0) : PairState) (0, 1) :=
    obsEq_of_projection_eq Prod.fst rfl
  have ha := obsEq_after (fun _ : Unit => swap) firstAlgebra h () he
  have hv := (obsEq_projectionAlgebra_iff (R := ℚ) Prod.fst _ _).mp ha
  norm_num [swap] at hv

/-- Visible values: states 0 and 1 share the central value; 2/3 are its sides. -/
def visible (s : Fin 4) : Fin 3 :=
  if s = 2 then 1 else if s = 3 then 2 else 0

def visibleSignal (a : Fin 3) : ℚ :=
  if a = 1 then -1 else if a = 2 then 1 else 0

def signal : Fin 4 → ℚ := pullback visible visibleSignal

/-- State 1 splits equally to -1/+1; all other rows go to the central value. -/
def demoModel : FiniteDrift.Model (Fin 4) where
  transition s t :=
    if s = 1 then (if t = 2 ∨ t = 3 then 1 / 2 else 0)
    else (if t = 0 then 1 else 0)
  good _ := false

theorem visible_surjective : Function.Surjective visible := by
  intro a
  fin_cases a
  · exact ⟨0, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩

theorem demo_stochastic : FinitePotential.Stochastic demoModel := by
  constructor
  · intro s t
    fin_cases s <;> fin_cases t <;> norm_num +decide [demoModel]
  · intro s
    fin_cases s <;> norm_num +decide [demoModel, Fin.sum_univ_succ]

theorem signal_in_projection : signal ∈ projectionAlgebra visible := ⟨visibleSignal, rfl⟩

/-- Every visible function is a quadratic polynomial in this three-value signal. -/
theorem signal_interpolation (g : Fin 3 → ℚ) :
    pullback visible g = fun s =>
      g 0 + ((g 2 - g 1) / 2) * signal s +
        ((g 2 + g 1) / 2 - g 0) * (signal s * signal s) := by
  funext s
  fin_cases s <;>
    norm_num +decide [signal, pullback_apply, visible, visibleSignal] <;> ring

theorem signal_generates_projection :
    projectionAlgebra visible = Algebra.adjoin ℚ {signal} := by
  apply le_antisymm
  · rintro f ⟨g, rfl⟩
    let B := Algebra.adjoin ℚ {signal}
    have hs : signal ∈ B := Algebra.subset_adjoin (Set.mem_singleton signal)
    have hp := B.add_mem
      (B.add_mem (B.algebraMap_mem (g 0))
        (B.mul_mem (B.algebraMap_mem ((g 2 - g 1) / 2)) hs))
      (B.mul_mem (B.algebraMap_mem ((g 2 + g 1) / 2 - g 0)) (B.mul_mem hs hs))
    change (fun s => g 0 + ((g 2 - g 1) / 2) * signal s +
      ((g 2 + g 1) / 2 - g 0) * (signal s * signal s)) ∈ B at hp
    rw [← signal_interpolation g] at hp
    exact hp
  · apply Algebra.adjoin_le_iff.mpr
    intro f hf
    rw [Set.mem_singleton_iff.mp hf]
    exact signal_in_projection

theorem mean_zero (s : Fin 4) : expectation demoModel signal s = 0 := by
  fin_cases s <;>
    norm_num +decide [expectation, demoModel, signal, pullback_apply, visible, visibleSignal,
      Fin.sum_univ_succ]

theorem generator_image_in_projection :
    expectation demoModel signal ∈ projectionAlgebra visible := by
  have he : expectation demoModel signal = 0 := funext mean_zero
  rw [he]
  exact (projectionAlgebra visible).zero_mem

theorem square_in_projection : signal * signal ∈ projectionAlgebra visible :=
  (projectionAlgebra visible).mul_mem signal_in_projection signal_in_projection

theorem square_after_distinguishes :
    expectation demoModel (signal * signal) 0 ≠
      expectation demoModel (signal * signal) 1 := by
  norm_num +decide [expectation, demoModel, signal, pullback_apply, visible, visibleSignal,
    Fin.sum_univ_succ]

theorem demo_not_kernelClosed : ¬ KernelClosed demoModel (projectionAlgebra visible) := by
  intro h
  have hf := kernelClosed_fiberLocal demoModel visible h
  have he := hf 0 1 (by decide) 1
  norm_num +decide [fiberMass, demoModel, visible, Fin.sum_univ_succ] at he

theorem mean_check_insufficient :
    projectionAlgebra visible = Algebra.adjoin ℚ {signal} ∧
    expectation demoModel signal ∈ projectionAlgebra visible ∧
    ¬ KernelClosed demoModel (projectionAlgebra visible) :=
  ⟨signal_generates_projection, generator_image_in_projection, demo_not_kernelClosed⟩

end RepairObservableExamples

#check @RepairObservableExamples.PairState
#check @RepairObservableExamples.firstAlgebra
#check @RepairObservableExamples.increment
#check @RepairObservableExamples.swap
#check @RepairObservableExamples.increment_stable
#check @RepairObservableExamples.increment_not_fixed
#check @RepairObservableExamples.swap_not_stable
#check @RepairObservableExamples.visible
#check @RepairObservableExamples.visibleSignal
#check @RepairObservableExamples.signal
#check @RepairObservableExamples.demoModel
#check @RepairObservableExamples.visible_surjective
#check @RepairObservableExamples.demo_stochastic
#check @RepairObservableExamples.signal_in_projection
#check @RepairObservableExamples.signal_interpolation
#check @RepairObservableExamples.signal_generates_projection
#check @RepairObservableExamples.mean_zero
#check @RepairObservableExamples.generator_image_in_projection
#check @RepairObservableExamples.square_in_projection
#check @RepairObservableExamples.square_after_distinguishes
#check @RepairObservableExamples.demo_not_kernelClosed
#check @RepairObservableExamples.mean_check_insufficient
