module

public import PPGraph.All

set_option autoImplicit false

/-!
Availability and reported-axiom inspection of the copied original framework.
The public aggregate import must expose the probabilistic process, adaptive
table law, semantic repair hazard and observable algebra together. Every
theorem below retains its original parameters and hypotheses.

These commands do not instantiate the framework on Kiro Crew, transfer the
registered chain's bounds, or constitute a new independent-kernel audit of
the imported library. They inspect existing declarations without adding new
mathematical claims. The raw chain and its earlier proof receipts are separate.
-/

-- The original process and the actual probabilistic MT expectation bound.
#check @MTProcess
#check @FiniteResampling.Problem
#check @FiniteResampling.Policy
#check @FiniteResampling.firstPolicy
#check @randomInitETLog_le_sum
#print axioms randomInitETLog_le_sum

-- Adaptive local-counter draws have the stated conditional product law.
-- This does not claim whole redraw vectors are independent across time.
#check @FiniteTable.nextDraw_fresh
#print axioms FiniteTable.nextDraw_fresh
#check @FiniteResampling.randomInitETLog_eq_rational_sum_of_equations
#print axioms FiniteResampling.randomInitETLog_eq_rational_sum_of_equations

-- Exact semantic invalidation and checked preservation of protected claims.
#check @RepairSemanticHazard.Invalidates
#check @RepairSemanticHazard.scope
#check @RepairSemanticHazard.CompleteDomain
#check @RepairSemanticHazard.checkExactCommit_iff_fullContract
#print axioms RepairSemanticHazard.checkExactCommit_iff_fullContract
#check @RepairSemanticHazard.checkedExactStep_preserves
#print axioms RepairSemanticHazard.checkedExactStep_preserves

-- Stable retained information supports observations after every allowed word.
#check @RepairObservable.Stable
#check @RepairObservable.Fixed
#check @RepairObservable.projectionAlgebra
#check @RepairObservable.projection_stable_of_factor
#print axioms RepairObservable.projection_stable_of_factor
#check @RepairObservable.obsEq_runWord
#print axioms RepairObservable.obsEq_runWord

-- Probabilistic closure and Good locality are additional quotient obligations.
#check @RepairObservableKernel.KernelClosed
#check @RepairObservableKernel.FiberLocal
#check @RepairObservableKernel.GoodLocal
#check @RepairObservableKernel.kernelClosed_iff_fiberLocal
#print axioms RepairObservableKernel.kernelClosed_iff_fiberLocal
#check @RepairObservableKernel.reduced_survival
#print axioms RepairObservableKernel.reduced_survival
