/-
  PPGraphMoserTardosOccurrence.lean

  Step 3: measurable occurrences of canonical witness shapes.
  The random initial state is supplied by slot 0 of the same log.

  A witness at a fixed time depends on finitely many selected labels.
  Factoring through that finite label history proves measurability;
  countability of WTree alone would not prove this fact. An occurrence
  is then a countable union over the active real times, including 0.
-/

module

public import PPGraph.MoserTardos.Probability.RandomInitExpectation
public import PPGraph.MoserTardos.Witness.WTreeCountable

@[expose] public section

open MeasureTheory Classical
open scoped ENNReal

variable {V : Type} {S : VarSpaces V} {ι : Type}

/-- Construction at root time `t` depends only on labels at indices
    at most `t`, even when the backward-step count is unrestricted. -/
theorem τBuild_congr_of_eq_upto (P : MTProcess S ι) (C D : ℕ → ι) (t : ℕ)
    (h : ∀ i, i ≤ t → C i = D i) :
    ∀ n : ℕ, τBuild P C t n = τBuild P D t n := by
  intro n
  induction n with
  | zero => simp only [τBuild, h t (Nat.le_refl t)]
  | succ n ih =>
      simp only [τBuild, ih, h (t - 1 - n) (by omega)]

theorem τC_congr_of_eq_upto (P : MTProcess S ι) (C D : ℕ → ι) (t : ℕ)
    (h : ∀ i, i ≤ t → C i = D i) : τC P C t = τC P D t := by
  exact τBuild_congr_of_eq_upto P C D t h (t - 1)

variable [DecidableEq V] [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The canonical witness at real time `s`, initialized from slot 0.
    Activity of the time is imposed separately by `witnessOccurrence`. -/
noncomputable def randomInitWitness (P : MTProcess S ι) (ω : LogSpace S)
    (s : ℕ) : WTree ι :=
  resamplingWitness P (initialStateFromLog ω) ω s

theorem randomInitWitness_label (P : MTProcess S ι) (ω : LogSpace S) (s : ℕ) :
    (randomInitWitness P ω s).label = realC P (initialStateFromLog ω) ω s := by
  exact resamplingWitness_label P (initialStateFromLog ω) ω s

/-- At each fixed time, the canonical witness is a measurable function
    into the discrete space of trees. No measurable structure on the
    raw address-indexed GrowingTree is needed. -/
theorem measurable_randomInitWitness (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (s : ℕ) :
    letI : MeasurableSpace (WTree ι) := ⊤
    Measurable (fun ω : LogSpace S => randomInitWitness P ω s) := by
  let : MeasurableSpace ι := ⊤
  let : MeasurableSpace (WTree ι) := ⊤
  let history : LogSpace S → (Fin (s + 2) → ι) :=
    fun ω k => shiftedC P (initialStateFromLog ω) ω k.val
  have hhistory : Measurable history := by
    apply Measurable.of_eval
    intro k
    exact measurable_realC_of_measurable_init P hbad initialStateFromLog
      measurable_initialStateFromLog (k.val - 1)
  let decode : (Fin (s + 2) → ι) → WTree ι := fun a =>
    WTree.canonicalize ((τC P
      (fun k => a ⟨min k (s + 1), by omega⟩) (s + 1)).toWTree [])
  have hdecode : Measurable decode := measurable_of_countable decode
  have heq : (fun ω : LogSpace S => randomInitWitness P ω s) =
      decode ∘ history := by
    funext ω
    change WTree.canonicalize
        ((τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)).toWTree []) =
      WTree.canonicalize ((τC P
        (fun k => shiftedC P (initialStateFromLog ω) ω (min k (s + 1)))
        (s + 1)).toWTree [])
    apply congrArg WTree.canonicalize
    apply congrArg (fun T : GrowingTree ι => T.toWTree [])
    apply τC_congr_of_eq_upto
    intro i hi
    rw [min_eq_left hi]
  rw [heq]
  exact hdecode.comp hhistory

theorem measurableSet_randomInitWitness_eq (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (s : ℕ) (U : WTree ι) :
    MeasurableSet {ω : LogSpace S | randomInitWitness P ω s = U} := by
  let : MeasurableSpace (WTree ι) := ⊤
  exact (measurable_randomInitWitness P hbad s) (measurableSet_singleton U)

/-- A canonical shape occurs when it belongs to an active resampling
    of `α`. The witness depends on the same log as that resampling. -/
def witnessOccurrence (P : MTProcess S ι) (α : ι) (U : WTree ι) :
    Set (LogSpace S) :=
  {ω | ∃ s : ℕ, ω ∈ randomInitResamplingEvent P α s ∧ randomInitWitness P ω s = U}

theorem witnessOccurrence_eq_iUnion (P : MTProcess S ι) (α : ι) (U : WTree ι) :
    witnessOccurrence P α U = ⋃ s : ℕ,
      (randomInitResamplingEvent P α s ∩
        {ω : LogSpace S | randomInitWitness P ω s = U}) := by
  ext ω
  simp only [witnessOccurrence, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]

theorem measurableSet_witnessOccurrence (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (α : ι) (U : WTree ι) :
    MeasurableSet (witnessOccurrence P α U) := by
  rw [witnessOccurrence_eq_iUnion]
  exact MeasurableSet.iUnion (fun s =>
    (measurableSet_randomInitResamplingEvent P hbad α s).inter
      (measurableSet_randomInitWitness_eq P hbad s U))

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @τBuild_congr_of_eq_upto
#check @τC_congr_of_eq_upto
#check @randomInitWitness
#check @randomInitWitness_label
#check @measurable_randomInitWitness
#check @measurableSet_randomInitWitness_eq
#check @witnessOccurrence
#check @witnessOccurrence_eq_iUnion
#check @measurableSet_witnessOccurrence
