/-
  PPGraphMoserTardosRandomInitialization.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos)

  Initialize the process from slot zero of the same random table that
  supplies subsequent resamplings. The trajectory is measurable for
  any measurable table-dependent initialization; no independence
  assumption on that initialization is needed for measurability.

  For the witness-tree correspondence, initialStateFromLog provides
  the specific initialization required by the slot-zero hypothesis.
-/

module

public import PPGraph.MoserTardos.Process.RandomTrajectory

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory Classical

variable {V : Type} [DecidableEq V]

/-- The initial assignment reads slot zero for every variable. -/
def initialStateFromLog {S : VarSpaces V} (ω : LogSpace S) : MTState S :=
  freshState ω 0

/-- Slot-zero compatibility required by the real-trajectory
    witness-tree correspondence. -/
theorem initialStateFromLog_eq_atIdx {S : VarSpaces V}
    (ω : LogSpace S) (v : V) :
    initialStateFromLog ω v = atIdx ω v 0 := rfl

theorem measurable_initialStateFromLog {S : VarSpaces V} :
    Measurable (initialStateFromLog (S := S)) :=
  measurable_freshState 0

/-- Both components of the counter-driven trajectory remain measurable
    when the initial assignment is a measurable function of the table.
    The proof follows measurable_randStep, with hinit in the base case. -/
theorem measurable_randStep_of_measurable_init {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (init : LogSpace S → MTState S) (hinit : Measurable init) :
    ∀ t, Measurable (fun ω : LogSpace S => (randStep P (init ω) ω t).1) ∧
         ∀ v, Measurable (fun ω : LogSpace S => (randStep P (init ω) ω t).2 v)
  | 0 => ⟨hinit, fun v => measurable_const⟩
  | (t + 1) => by
      obtain ⟨ihState, ihCount⟩ := measurable_randStep_of_measurable_init P hbad init hinit t
      have hdraw : Measurable (fun ω : LogSpace S =>
          drawFrom ω (fun v => (randStep P (init ω) ω t).2 v + 1)) := by
        apply Measurable.of_eval
        intro v
        exact measurable_eval_bounded v (t + 1) (fun ω => (randStep P (init ω) ω t).2 v + 1)
          ((ihCount v).add_const 1)
          (fun ω => by have := randCount_le P (init ω) ω t v; omega)
      have hpair : Measurable (fun ω : LogSpace S =>
          ((randStep P (init ω) ω t).1,
            drawFrom ω (fun v => (randStep P (init ω) ω t).2 v + 1))) :=
        ihState.prodMk hdraw
      have hpick := measurable_pickFirstViolated P hbad
      have hchain := measurable_resampleChain P (pickFirstViolated P) hpick Finset.univ.toList
      have hcomp : Measurable (fun ω : LogSpace S =>
          resampleChain P (pickFirstViolated P) Finset.univ.toList
            (randStep P (init ω) ω t).1
            (drawFrom ω (fun v => (randStep P (init ω) ω t).2 v + 1))) :=
        hchain.comp hpair
      have heqState : ∀ ω : LogSpace S,
          resampleChain P (pickFirstViolated P) Finset.univ.toList
            (randStep P (init ω) ω t).1
            (drawFrom ω (fun v => (randStep P (init ω) ω t).2 v + 1))
          = resample (P.footprint (pickFirstViolated P (randStep P (init ω) ω t).1))
              (randStep P (init ω) ω t).1
              (drawFrom ω (fun v => (randStep P (init ω) ω t).2 v + 1)) := by
        intro ω
        exact resampleChain_eq_of_mem P (pickFirstViolated P) (randStep P (init ω) ω t).1
          (drawFrom ω (fun v => (randStep P (init ω) ω t).2 v + 1)) Finset.univ.toList
          (Finset.mem_toList.mpr (Finset.mem_univ _))
      have hstate : Measurable (fun ω : LogSpace S => (randStep P (init ω) ω (t + 1)).1) := by
        show Measurable (fun ω : LogSpace S =>
          resample (P.footprint (pickFirstViolated P (randStep P (init ω) ω t).1))
            (randStep P (init ω) ω t).1
            (drawFrom ω (fun v => (randStep P (init ω) ω t).2 v + 1)))
        exact (funext heqState) ▸ hcomp
      have hcount : ∀ v,
          Measurable (fun ω : LogSpace S => (randStep P (init ω) ω (t + 1)).2 v) := by
        intro v
        let : MeasurableSpace ι := ⊤
        have hpickComp : Measurable (fun ω : LogSpace S =>
            pickFirstViolated P (randStep P (init ω) ω t).1) :=
          hpick.comp ihState
        have hcond : MeasurableSet {ω : LogSpace S |
            v ∈ P.footprint (pickFirstViolated P (randStep P (init ω) ω t).1)} := by
          have hset : {ω : LogSpace S |
              v ∈ P.footprint (pickFirstViolated P (randStep P (init ω) ω t).1)}
              = (fun ω => pickFirstViolated P (randStep P (init ω) ω t).1) ⁻¹'
                {i : ι | v ∈ P.footprint i} := rfl
          rw [hset]
          exact hpickComp MeasurableSpace.measurableSet_top
        have hthen : Measurable (fun ω : LogSpace S => (randStep P (init ω) ω t).2 v + 1) :=
          (ihCount v).add_const 1
        show Measurable (fun ω : LogSpace S =>
          if v ∈ P.footprint (pickFirstViolated P (randStep P (init ω) ω t).1)
          then (randStep P (init ω) ω t).2 v + 1 else (randStep P (init ω) ω t).2 v)
        exact Measurable.ite hcond hthen (ihCount v)
      exact ⟨hstate, hcount⟩

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @initialStateFromLog
#check @initialStateFromLog_eq_atIdx
#check @measurable_initialStateFromLog
#check @measurable_randStep_of_measurable_init
