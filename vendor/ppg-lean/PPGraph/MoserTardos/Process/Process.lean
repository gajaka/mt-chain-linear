/-
  PPGraphMoserTardosProcess.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos)

  Layer 2: the resample-until-fixed algorithm as a process.
  Builds on PPGraphMoserTardos.lean (VarSpaces, MTState, resample,
  depends_only_on, resample_preserves_disjoint).

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import PPGraph.MoserTardos.Process.Basic

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- Layer 2: The Moser-Tardos process (resample-until-fixed algorithm)
-- -------------------------------------------------------------------

/-- A Moser-Tardos instance: a family of bad events indexed by `ι`,
    each with a declared footprint and a proof that the event really
    depends only on that footprint (so "resample its footprint" is a
    meaningful operation with respect to it). -/
structure MTProcess (S : VarSpaces V) (ι : Type) where
  bad : ι → Set (MTState S)
  footprint : ι → Finset V
  dep : ∀ i, depends_only_on (bad i) (footprint i)

/-- The events violated at a state ω. The algorithm's job is to drive
    this set to ∅. -/
def violated {S : VarSpaces V} {ι : Type} (P : MTProcess S ι) (ω : MTState S) : Set ι :=
  {i | ω ∈ P.bad i}

/-- A log records, at every time step, which event index was chosen for
    resampling and which fresh state supplied the new coordinate
    values. All the randomness of the real algorithm lives in the log;
    the trajectory it produces is a deterministic function of it (a
    probability measure on logs belongs to a later layer). -/
def mtTrajectory {S : VarSpaces V} {ι : Type} (P : MTProcess S ι)
    (log : ℕ → ι × MTState S) (ω0 : MTState S) : ℕ → MTState S
  | 0 => ω0
  | (t + 1) => resample (P.footprint (log t).1) (mtTrajectory P log ω0 t) (log t).2

/-- A log is *faithful* to P if it only ever resamples an event that is
    actually violated at the time -- this is what distinguishes a real
    execution of the algorithm from an arbitrary sequence of resamples. -/
def faithful {S : VarSpaces V} {ι : Type} (P : MTProcess S ι)
    (log : ℕ → ι × MTState S) (ω0 : MTState S) : Prop :=
  ∀ t, (log t).1 ∈ violated P (mtTrajectory P log ω0 t)

/-- The process has converged by time T once no event is violated there
    -- the algorithm's halting condition. -/
def mt_converged {S : VarSpaces V} {ι : Type} (P : MTProcess S ι)
    (log : ℕ → ι × MTState S) (ω0 : MTState S) (T : ℕ) : Prop :=
  violated P (mtTrajectory P log ω0 T) = ∅

/-- The structural fact the witness-tree argument (Layer 3) is built
    on: resampling event `c` cannot change whether an unrelated event
    `j` (one whose footprint doesn't overlap `c`'s) is violated. -/
theorem mt_step_preserves_unrelated {S : VarSpaces V} {ι : Type} (P : MTProcess S ι)
    (log : ℕ → ι × MTState S) (ω0 : MTState S) (t : ℕ) (j : ι)
    (h_disj : Disjoint (P.footprint (log t).1) (P.footprint j)) :
    mtTrajectory P log ω0 t ∈ P.bad j ↔ mtTrajectory P log ω0 (t + 1) ∈ P.bad j :=
  resample_preserves_disjoint (P.bad j) (P.footprint (log t).1) (P.footprint j)
    (P.dep j) h_disj (mtTrajectory P log ω0 t) (log t).2

/-- Contrapositive, phrased the way the witness-tree argument actually
    uses it: if `j` was not violated before a step but IS violated
    right after, then `j`'s footprint must intersect the footprint of
    whatever was just resampled. New violations only ever appear
    "next to" the last resample. -/
theorem mt_new_violation_overlaps {S : VarSpaces V} {ι : Type} (P : MTProcess S ι)
    (log : ℕ → ι × MTState S) (ω0 : MTState S) (t : ℕ) (j : ι)
    (h_new : mtTrajectory P log ω0 t ∉ P.bad j)
    (h_now : mtTrajectory P log ω0 (t + 1) ∈ P.bad j) :
    ¬ Disjoint (P.footprint (log t).1) (P.footprint j) := by
  intro h_disj
  exact h_new ((mt_step_preserves_unrelated P log ω0 t j h_disj).mpr h_now)

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @MTProcess
#check @violated
#check @mtTrajectory
#check @faithful
#check @mt_converged
#check @mt_step_preserves_unrelated
#check @mt_new_violation_overlaps
