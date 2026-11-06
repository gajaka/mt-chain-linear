/-
  PPGraphMoserTardosCounting.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos)

  Layer 4, Part C: the counting half of Theorem 5.7.1 (Alon-Spencer
  §5.7, p.83) -- "the number of times event A is resampled among the
  first T steps equals the number of DISTINCT proper witness trees
  rooted at A that occur as τ_C(t) for some genuine (actually-violated)
  t < T" -- built directly from the already-proved injectivity
  (`τC_injective_on_occurrences`, PPGraphMoserTardosInjectivity.lean)
  via `Finset.card_image_of_injOn`.

  SCOPE, stated honestly: this file gives the COUNTING identity only.
  It does NOT attempt Theorem 5.7.2 (Pr[T occurs] ≤ p(T), the
  "injective encoding of independent coin-flips" probability argument)
  -- that is the hardest, most technical part of the whole
  Moser-Tardos proof, a substantial undertaking on its own, and is left
  for a dedicated follow-up. Taking expectations of the identity proved
  here, once 5.7.2 exists, is what would finally connect
  `sum_mtWeight_le` (PPGraphMoserTardosConvergence.lean) to an actual
  E[TLOG] bound.

  Also fixes a real gap surfaced while designing this file:
  `pickFirstViolated` (PPGraphMoserTardosRandomTrajectory.lean) was
  proved MEASURABLE but never proved to actually behave like a
  resampling policy should -- that it picks a genuinely violated event
  whenever one exists. `pickFirstViolated_mem_violated` below closes
  that gap; TLOG (below) is defined in terms of "genuinely violated"
  steps precisely because of it.

  Builds on PPGraphMoserTardosRandomTrajectory.lean (pickFirstViolated,
  pickFromList, randTraj) and PPGraphMoserTardosInjectivity.lean
  (τC, τC_injective_on_occurrences).

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import PPGraph.MoserTardos.Process.RandomTrajectory
public import PPGraph.MoserTardos.Witness.Injectivity

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- pickFirstViolated genuinely picks a violated event, when one exists
-- -------------------------------------------------------------------

/-- If some event in `l` is violated at `ω'`, `pickFromList` returns a
    violated one (not necessarily the same `j` that witnessed
    nonemptiness -- whichever comes first in `l` -- but violated
    regardless). Induction on `l`, mirroring `pickFromList`'s own
    recursion. -/
theorem pickFromList_spec {S : VarSpaces V} {ι : Type} (P : MTProcess S ι)
    (default : ι) (ω' : MTState S) :
    ∀ l : List ι, (∃ j ∈ l, ω' ∈ P.bad j) → ω' ∈ P.bad (pickFromList P default l ω') := by
  intro l
  induction l with
  | nil => rintro ⟨j, hj, _⟩; exact absurd hj List.not_mem_nil
  | cons i rest ih =>
      rintro ⟨j, hj, hjbad⟩
      simp only [pickFromList]
      by_cases h : ω' ∈ P.bad i
      · rw [ite_eq_left h]; exact h
      · rw [ite_eq_right h]
        apply ih
        refine ⟨j, ?_, hjbad⟩
        rcases List.mem_cons.mp hj with hje | hje
        · exact absurd (hje ▸ hjbad) h
        · exact hje

/-- The concrete policy is faithful: whenever some event is violated,
    the one it picks IS violated. This is the correctness property
    `pickFirstViolated`'s earlier measurability proof never addressed. -/
theorem pickFirstViolated_mem_violated {S : VarSpaces V} {ι : Type} [Fintype ι] [Nonempty ι]
    (P : MTProcess S ι) (ω' : MTState S) (h : violated P ω' ≠ ∅) :
    ω' ∈ P.bad (pickFirstViolated P ω') := by
  obtain ⟨j, hj⟩ := Set.nonempty_iff_ne_empty.mpr h
  exact pickFromList_spec P (Classical.arbitrary ι) ω' Finset.univ.toList
    ⟨j, Finset.mem_toList.mpr (Finset.mem_univ j), hj⟩

-- -------------------------------------------------------------------
-- TLOG: the number of GENUINE resample steps among the first T
-- -------------------------------------------------------------------

/-- The random log's own decision sequence: which event `pickFirstViolated`
    would fix at time t, given the trajectory so far. This is the
    concrete instantiation of the abstract `C : ℕ → ι` that
    `τC`/`τC_injective_on_occurrences` (PPGraphMoserTardosGrowing.lean /
    PPGraphMoserTardosInjectivity.lean) were stated for. -/
noncomputable def randC {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) : ℕ → ι :=
  fun t => pickFirstViolated P (randTraj P ω0 ω t)

/-- Number of GENUINELY violated steps (not counting steps where
    nothing was violated and `pickFirstViolated` fell back to its
    default) among the first T. This is what the book calls TLOG. -/
noncomputable def TLOG {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) (T : ℕ) : ℕ :=
  ((Finset.range T).filter (fun t => violated P (randTraj P ω0 ω t) ≠ ∅)).card

-- -------------------------------------------------------------------
-- The counting identity: genuine occurrences of label A ↔ distinct
-- witness trees rooted at A (Theorem 5.7.1's counting half)
-- -------------------------------------------------------------------

/-- The set of times, among `1 ≤ t < T` (t = 0 excluded: `τC_injective_
    on_occurrences` needs `0 < t`, and a single boundary step changes
    nothing about the counting argument itself), where the step was
    genuine AND fixed label A. -/
noncomputable def genuineAt {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) (A : ι) (T : ℕ) : Finset ℕ :=
  (Finset.range T).filter
    (fun t => 0 < t ∧ violated P (randTraj P ω0 ω t) ≠ ∅ ∧ randC P ω0 ω t = A)

/-- Theorem 5.7.1, counting half: the number of times among `1 ≤ t < T`
    that event A is genuinely resampled equals the number of DISTINCT
    proper witness trees rooted at A occurring as `τC (randC ...) t`
    over exactly those times. Pure counting, via
    `Finset.card_image_of_injOn` and the already-proved
    `τC_injective_on_occurrences` -- no probability anywhere in this
    proof. -/
theorem card_genuineAt_eq_card_trees {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) (A : ι) (T : ℕ) :
    (genuineAt P ω0 ω A T).card
      = ((genuineAt P ω0 ω A T).image (fun t => τC P (randC P ω0 ω) t)).card := by
  symm
  apply Finset.card_image_of_injOn
  intro t1 h1 t2 h2 heq
  rw [Finset.mem_coe] at h1 h2
  unfold genuineAt at h1 h2
  rw [Finset.mem_filter, Finset.mem_range] at h1 h2
  obtain ⟨_, ht1pos, _, hA1⟩ := h1
  obtain ⟨_, ht2pos, _, hA2⟩ := h2
  have hAeq : randC P ω0 ω t1 = randC P ω0 ω t2 := hA1.trans hA2.symm
  rcases lt_trichotomy t1 t2 with hlt | heq' | hgt
  · exact absurd heq (τC_injective_on_occurrences P (randC P ω0 ω) t1 t2 ht1pos ht2pos hlt hAeq)
  · exact heq'
  · exact absurd heq.symm
      (τC_injective_on_occurrences P (randC P ω0 ω) t2 t1 ht2pos ht1pos hgt hAeq.symm)

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @pickFromList_spec
#check @pickFirstViolated_mem_violated
#check @randC
#check @TLOG
#check @genuineAt
#check @card_genuineAt_eq_card_trees
