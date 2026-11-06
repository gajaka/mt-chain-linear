/-
  PPGraphMoserTardosPastIndependence.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos)

  Layer 4, Part D: the bridging fact Theorem 5.7.2 needs -- that "which
  draw gets used" and "the draw's own value" are independent, since the
  decision of what to resample at step t never looks at a coordinate
  it hasn't consumed yet. Now proved directly in terms of `randStep`'s
  own per-variable local counters (Alon-Spencer's C[v,n], p.84,
  PPGraphMoserTardosRandomTrajectory.lean), via `randCount_le`: the
  slot a variable's counter actually points to after t steps is always
  < t (once t > 0), so "agree on all coordinates (n,v) with n < t"
  already pins down the ONE slot each variable's next draw could read.

  Stated in the same style as `depends_only_on`
  (PPGraphMoserTardos.lean), not via an abstract sub-σ-algebra /
  `MeasurableSpace.comap` construction. The PUBLIC statement
  (`randTraj_depends_on_past`) is unchanged from the original
  global-time version -- same hypothesis shape, same conclusion; only
  the proof internals changed, routed through the new counter-based
  `randStep_depends_on_past` first.

  Builds on PPGraphMoserTardosRandomTrajectory.lean (randStep, randTraj,
  randCount_le, drawFrom, atIdx, pickFirstViolated).

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import PPGraph.MoserTardos.Process.RandomTrajectory

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical

variable {V : Type} [DecidableEq V]

/-- `randStep`'s value (state AND counter together) at step t depends
    only on the log's coordinates at LOCAL slots AT MOST t, for every
    variable -- `≤ t`, not `< t`, since `randStep` now reads each
    variable's draw at `counter + 1` (slot 0 is reserved for `ω0`,
    matching Moser-Tardos's own convention -- see `randStep`'s
    docstring), so the counter reaching its bound `t` (`randCount_le`)
    means the read can land exactly on slot `t`. Induction on t: the
    base case is the constant `(ω0, 0)`; the step uses the IH
    (restricting `hagree` from `n ≤ t+1` to `n ≤ t`) to identify the
    state/counter both sides resample from, then `randCount_le` to see
    that each variable's counter value after t steps is itself ≤ t, so
    `counter + 1 ≤ t + 1` -- exactly the slot `hagree` already covers
    -- so `drawFrom` agrees on both sides too, and both full steps
    reduce to the identical pair. -/
theorem randStep_depends_on_past {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (P : MTProcess S ι) (ω0 : MTState S) :
    ∀ (t : ℕ) (ω1 ω2 : LogSpace S), (∀ v, ∀ n ≤ t, ω1 (n, v) = ω2 (n, v)) →
      randStep P ω0 ω1 t = randStep P ω0 ω2 t
  | 0, _, _, _ => rfl
  | (t + 1), ω1, ω2, hagree => by
      have ih : randStep P ω0 ω1 t = randStep P ω0 ω2 t :=
        randStep_depends_on_past P ω0 t ω1 ω2 (fun v n hn => hagree v n (by omega))
      have hdraw : drawFrom ω1 (fun v => (randStep P ω0 ω2 t).2 v + 1)
          = drawFrom ω2 (fun v => (randStep P ω0 ω2 t).2 v + 1) := by
        funext v
        show ω1 ((randStep P ω0 ω2 t).2 v + 1, v) = ω2 ((randStep P ω0 ω2 t).2 v + 1, v)
        exact hagree v ((randStep P ω0 ω2 t).2 v + 1) (by have := randCount_le P ω0 ω2 t v; omega)
      show (resample (P.footprint (pickFirstViolated P (randStep P ω0 ω1 t).1))
              (randStep P ω0 ω1 t).1 (drawFrom ω1 (fun v => (randStep P ω0 ω1 t).2 v + 1)),
            fun v => if v ∈ P.footprint (pickFirstViolated P (randStep P ω0 ω1 t).1)
                     then (randStep P ω0 ω1 t).2 v + 1 else (randStep P ω0 ω1 t).2 v)
          = (resample (P.footprint (pickFirstViolated P (randStep P ω0 ω2 t).1))
              (randStep P ω0 ω2 t).1 (drawFrom ω2 (fun v => (randStep P ω0 ω2 t).2 v + 1)),
            fun v => if v ∈ P.footprint (pickFirstViolated P (randStep P ω0 ω2 t).1)
                     then (randStep P ω0 ω2 t).2 v + 1 else (randStep P ω0 ω2 t).2 v)
      rw [ih, hdraw]

/-- Public-facing corollary, same name/statement shape as the original
    global-time version, EXCEPT the bound is now `s ≤ t` (not `s < t`)
    to match `randStep_depends_on_past`'s own shifted bound: `randTraj`
    at time t depends only on the log's coordinates at times AT MOST
    t. -/
theorem randTraj_depends_on_past {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (P : MTProcess S ι) (ω0 : MTState S) (t : ℕ) (ω1 ω2 : LogSpace S)
    (hagree : ∀ s ≤ t, ∀ v, ω1 (s, v) = ω2 (s, v)) :
    randTraj P ω0 ω1 t = randTraj P ω0 ω2 t :=
  congrArg Prod.fst (randStep_depends_on_past P ω0 t ω1 ω2 (fun v n hn => hagree n hn v))

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @randStep_depends_on_past
#check @randTraj_depends_on_past
