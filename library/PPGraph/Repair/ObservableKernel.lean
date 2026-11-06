/-
  Observable subalgebras and exact finite probabilistic reduction.

  The Markov expectation operator is linear, generally not multiplicative.
  Therefore deterministic algebra-generator checking cannot simply be reused
  for stochastic closure. Full closure of the projection algebra is equivalent
  to equality of aggregate transition masses on every summary fiber.

  A surjective summary supplies representatives only for constructing the
  reduced matrix. The good-state predicate must independently factor through
  the summary. Together these obligations recover FiniteLumping.Compatible,
  so existing probability and first-hit results apply under their stated
  stochastic/realization assumptions. Nothing assumes repair success.
-/
module

public import PPGraph.Repair.ObservableAlgebra
public import PPGraph.Finite.Lumping.Basic

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RepairObservableKernel

open RepairObservable

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

def expectation (M : FiniteDrift.Model S) (f : S → ℚ) (s : S) : ℚ :=
  ∑ t, M.transition s t * f t

def KernelClosed (M : FiniteDrift.Model S) (B : Subalgebra ℚ (S → ℚ)) : Prop :=
  ∀ f, f ∈ B → expectation M f ∈ B

def fiberMass (M : FiniteDrift.Model S) (q : S → A) (s : S) (a : A) : ℚ :=
  ∑ t, if q t = a then M.transition s t else 0

def FiberLocal (M : FiniteDrift.Model S) (q : S → A) : Prop :=
  ∀ s t, q s = q t → ∀ a, fiberMass M q s a = fiberMass M q t a

def GoodLocal (M : FiniteDrift.Model S) (q : S → A) : Prop :=
  ∀ s t, q s = q t → M.good s = M.good t

theorem expectation_projection (M : FiniteDrift.Model S) (q : S → A)
    (f : A → ℚ) (s : S) :
    expectation M (pullback q f) s = ∑ a, fiberMass M q s a * f a := by
  calc
    _ = ∑ t, ∑ a, if q t = a then M.transition s t * f a else 0 := by
      simp [expectation]
    _ = ∑ a, ∑ t, if q t = a then M.transition s t * f a else 0 :=
      Finset.sum_comm
    _ = _ := by simp only [fiberMass, Finset.sum_mul, ite_mul, zero_mul]

theorem kernelClosed_fiberLocal (M : FiniteDrift.Model S) (q : S → A)
    (h : KernelClosed M (projectionAlgebra q)) : FiberLocal M q := by
  intro s t hst a
  let f : A → ℚ := fun b => if b = a then 1 else 0
  obtain ⟨g, hg⟩ := h (pullback q f) ⟨f, rfl⟩
  have hv : expectation M (pullback q f) s =
      expectation M (pullback q f) t := by
    rw [← hg]
    exact congrArg g hst
  simpa only [expectation, pullback_apply, f, mul_ite, mul_one, mul_zero,
    fiberMass] using hv

noncomputable def representative (q : S → A) (hq : Function.Surjective q)
    (a : A) : S := Classical.choose (hq a)

theorem representative_spec (q : S → A) (hq : Function.Surjective q) (a : A) :
    q (representative q hq a) = a := Classical.choose_spec (hq a)

noncomputable def reducedModel (M : FiniteDrift.Model S) (q : S → A)
    (hq : Function.Surjective q) : FiniteDrift.Model A where
  transition a b := fiberMass M q (representative q hq a) b
  good a := M.good (representative q hq a)

theorem fiberLocal_kernelClosed (M : FiniteDrift.Model S) (q : S → A)
    (hq : Function.Surjective q) (h : FiberLocal M q) :
    KernelClosed M (projectionAlgebra q) := by
  rintro f ⟨g, rfl⟩
  refine ⟨expectation (reducedModel M q hq) g, ?_⟩
  funext s
  change expectation (reducedModel M q hq) g (q s) =
    expectation M (pullback q g) s
  rw [expectation_projection]
  apply Finset.sum_congr rfl
  intro a _
  have he := h s (representative q hq (q s))
    (representative_spec q hq (q s)).symm a
  exact congrArg (fun x => x * g a) he.symm

theorem kernelClosed_iff_fiberLocal (M : FiniteDrift.Model S) (q : S → A)
    (hq : Function.Surjective q) :
    KernelClosed M (projectionAlgebra q) ↔ FiberLocal M q :=
  ⟨kernelClosed_fiberLocal M q, fiberLocal_kernelClosed M q hq⟩

theorem reduced_compatible (M : FiniteDrift.Model S) (q : S → A)
    (hq : Function.Surjective q) (hk : FiberLocal M q) (hg : GoodLocal M q) :
    FiniteLumping.Compatible M (reducedModel M q hq) q := by
  constructor
  · intro s
    exact hg s (representative q hq (q s)) (representative_spec q hq (q s)).symm
  · intro s a
    exact hk s (representative q hq (q s))
      (representative_spec q hq (q s)).symm a

theorem compatible_local (M : FiniteDrift.Model S) (N : FiniteDrift.Model A)
    (q : S → A) (h : FiniteLumping.Compatible M N q) :
    FiberLocal M q ∧ GoodLocal M q := by
  constructor
  · intro s t he a
    change (∑ u, if q u = a then M.transition s u else 0) =
      ∑ u, if q u = a then M.transition t u else 0
    rw [h.2 s a, h.2 t a, he]
  · intro s t he
    rw [h.1 s, h.1 t, he]

/-- The independently required Boolean contract is retained explicitly. -/
theorem reduced_compatible_iff (M : FiniteDrift.Model S) (q : S → A)
    (hq : Function.Surjective q) :
    FiniteLumping.Compatible M (reducedModel M q hq) q ↔
      KernelClosed M (projectionAlgebra q) ∧ GoodLocal M q := by
  constructor
  · intro h
    obtain ⟨hk, hg⟩ := compatible_local M _ q h
    exact ⟨fiberLocal_kernelClosed M q hq hk, hg⟩
  · rintro ⟨hk, hg⟩
    exact reduced_compatible M q hq (kernelClosed_fiberLocal M q hk) hg

theorem reduced_stochastic (M : FiniteDrift.Model S) (q : S → A)
    (hq : Function.Surjective q) (hk : KernelClosed M (projectionAlgebra q))
    (hg : GoodLocal M q) (hm : FinitePotential.Stochastic M) :
    FinitePotential.Stochastic (reducedModel M q hq) :=
  FiniteLumping.stochastic_projected M _ q
    ((reduced_compatible_iff M q hq).mpr ⟨hk, hg⟩) hq hm

theorem reduced_survival (M : FiniteDrift.Model S) (q : S → A)
    (hq : Function.Surjective q) (hk : KernelClosed M (projectionAlgebra q))
    (hg : GoodLocal M q) (n : ℕ) (s : S) :
    FinitePotential.survival M n s =
      FinitePotential.survival (reducedModel M q hq) n (q s) :=
  FiniteLumping.survival_projection M _ q
    ((reduced_compatible_iff M q hq).mpr ⟨hk, hg⟩) n s

end RepairObservableKernel

#check @RepairObservableKernel.expectation
#check @RepairObservableKernel.KernelClosed
#check @RepairObservableKernel.fiberMass
#check @RepairObservableKernel.FiberLocal
#check @RepairObservableKernel.GoodLocal
#check @RepairObservableKernel.expectation_projection
#check @RepairObservableKernel.kernelClosed_fiberLocal
#check @RepairObservableKernel.representative
#check @RepairObservableKernel.representative_spec
#check @RepairObservableKernel.reducedModel
#check @RepairObservableKernel.fiberLocal_kernelClosed
#check @RepairObservableKernel.kernelClosed_iff_fiberLocal
#check @RepairObservableKernel.reduced_compatible
#check @RepairObservableKernel.compatible_local
#check @RepairObservableKernel.reduced_compatible_iff
#check @RepairObservableKernel.reduced_stochastic
#check @RepairObservableKernel.reduced_survival
