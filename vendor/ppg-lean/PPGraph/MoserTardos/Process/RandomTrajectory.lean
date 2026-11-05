/-
  PPGraphMoserTardosRandomTrajectory.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos)

  Layer 4, Part B: the actual random trajectory, built from `LogSpace`
  (PPGraphMoserTardosLogSpace.lean) instead of an arbitrary log, and
  its measurability at each fixed time step -- the fact Theorems 5.7.1
  /5.7.2 (Alon-Spencer §5.7) need before "the probability that witness
  tree T occurs" is even a well-posed question.

  The "which violated event to fix next" policy is NOT left as an
  abstract hypothesis: it is built concretely (`pickFirstViolated`,
  scanning a fixed enumeration of ι and taking the first violated
  event), and its measurability is PROVED, not assumed. The one
  genuinely new standing hypothesis is `hbad : ∀ i, MeasurableSet
  (P.bad i)` on the MTProcess -- structurally necessary for "is event
  i violated" to be a meaningful measurable question at all; nothing
  in PPGraphMoserTardosProcess.lean's own definition of MTProcess
  guarantees it.

  Builds on PPGraphMoserTardosLogSpace.lean (LogSpace, freshState,
  measurable_freshState) and PPGraphMoserTardosProcess.lean (MTProcess,
  resample from PPGraphMoserTardos.lean).

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import PPGraph.MoserTardos.Process.LogSpace
public import PPGraph.MoserTardos.Process.Process

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory Classical

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- A concrete, measurable "which event to fix" policy
-- -------------------------------------------------------------------

/-- First event in the list `l` violated at `ω'`, or `default` if none
    of `l` is. Recursion on a plain list (not `List.find?`) so its own
    measurability is a direct structural induction, not dependent on
    `find?`'s internal implementation. -/
noncomputable def pickFromList {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (default : ι) : List ι → MTState S → ι
  | [], _ => default
  | (i :: rest), ω' => if ω' ∈ P.bad i then i else pickFromList P default rest ω'

/-- `pickFromList` is measurable in ω' for any fixed list, given each
    `P.bad i` is measurable. Induction on the list: the base case is a
    constant function; the step is `Measurable.ite` on the (measurable,
    by `hbad i`) condition `ω' ∈ P.bad i`, with the "then" branch
    constant and the "else" branch the induction hypothesis. -/
theorem measurable_pickFromList {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (default : ι) (l : List ι) :
    letI : MeasurableSpace ι := ⊤
    Measurable (pickFromList P default l) := by
  let : MeasurableSpace ι := ⊤
  induction l with
  | nil => exact measurable_const
  | cons i rest ih =>
      simp only [pickFromList]
      exact Measurable.ite (hbad i) measurable_const ih

/-- Membership is preserved down the recursion: whatever `pickFromList`
    returns on `l`, if that value isn't the `default`, it must actually
    occur in `l`. (Needed below to connect `pickFromList` back to a
    direct `resample` once we know the picked event really is in the
    scanned list.) -/
theorem pickFromList_mem_or_default {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (default : ι) (ω' : MTState S) :
    ∀ l : List ι, pickFromList P default l ω' ∈ l ∨ pickFromList P default l ω' = default := by
  intro l
  induction l with
  | nil => exact Or.inr rfl
  | cons i rest ih =>
      simp only [pickFromList]
      by_cases h : ω' ∈ P.bad i
      · rw [ite_eq_left h]; exact Or.inl List.mem_cons_self
      · rw [ite_eq_right h]
        rcases ih with ih | ih
        · exact Or.inl (List.mem_cons_of_mem i ih)
        · exact Or.inr ih

/-- The concrete policy: scan `Finset.univ` (ι finite) in its own
    canonical list order, fix the first violated event, or a fixed
    default (`Classical.arbitrary`, ι nonempty) if none is violated. -/
noncomputable def pickFirstViolated {S : VarSpaces V} {ι : Type} [Fintype ι] [Nonempty ι]
    (P : MTProcess S ι) : MTState S → ι :=
  pickFromList P (Classical.arbitrary ι) Finset.univ.toList

theorem measurable_pickFirstViolated {S : VarSpaces V} {ι : Type} [Fintype ι] [Nonempty ι]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) :
    letI : MeasurableSpace ι := ⊤
    Measurable (pickFirstViolated P) :=
  measurable_pickFromList P hbad (Classical.arbitrary ι) Finset.univ.toList

-- -------------------------------------------------------------------
-- Resampling with a footprint chosen by a finite-valued function of
-- the current state, rather than a single fixed footprint
-- -------------------------------------------------------------------

/-- `resample`, jointly measurable in both state arguments, for one
    FIXED footprint F. Each coordinate v is either "always take it
    from the second state" or "always take it from the first" -- a
    fixed (not state-dependent) case split on `v ∈ F`, so this needs
    no `Measurable.ite`-style hypothesis of its own. -/
theorem measurable_resample_fixed {S : VarSpaces V} (F : Finset V) :
    Measurable (fun p : MTState S × MTState S => resample F p.1 p.2) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v ∈ F
  · simp only [resample, ite_eq_left hv]; fun_prop
  · simp only [resample, ite_eq_right hv]; fun_prop

/-- Resample where the footprint tracks `P.footprint (pick_fn ω)`
    rather than a single fixed footprint: chain through a list `l` of
    candidate events, taking the `resample`-branch for whichever one
    `pick_fn ω` actually equals. Same shape as `pickFromList` one level
    up (branch bodies are full states, not single events). -/
noncomputable def resampleChain {S : VarSpaces V} {ι : Type} (P : MTProcess S ι)
    (pick_fn : MTState S → ι) : List ι → MTState S → MTState S → MTState S
  | [], ω, _ => ω
  | (i :: rest), ω, ω' =>
      if pick_fn ω = i then resample (P.footprint i) ω ω' else resampleChain P pick_fn rest ω ω'

theorem measurable_resampleChain {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (pick_fn : MTState S → ι)
    (hpick : letI : MeasurableSpace ι := ⊤; Measurable pick_fn) (l : List ι) :
    Measurable (fun p : MTState S × MTState S => resampleChain P pick_fn l p.1 p.2) := by
  let : MeasurableSpace ι := ⊤
  induction l with
  | nil => exact measurable_fst
  | cons i rest ih =>
      simp only [resampleChain]
      have hcond : MeasurableSet {p : MTState S × MTState S | pick_fn p.1 = i} :=
        (hpick.comp measurable_fst) (measurableSet_singleton i)
      exact Measurable.ite hcond (measurable_resample_fixed (P.footprint i)) ih

/-- If `pick_fn ω` actually occurs in `l`, chaining through `l` gives
    exactly the same result as directly resampling with
    `P.footprint (pick_fn ω)` -- the branch the chain settles on IS
    the direct one, regardless of what (non-matching) events precede
    it in the list. -/
theorem resampleChain_eq_of_mem {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (pick_fn : MTState S → ι) (ω ω' : MTState S) :
    ∀ l : List ι, pick_fn ω ∈ l →
      resampleChain P pick_fn l ω ω' = resample (P.footprint (pick_fn ω)) ω ω' := by
  intro l
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons i rest ih =>
      intro hmem
      simp only [resampleChain]
      by_cases heq : pick_fn ω = i
      · rw [ite_eq_left heq, heq]
      · rw [ite_eq_right heq]
        apply ih
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h heq
        · exact h

-- -------------------------------------------------------------------
-- Reading a state with a PER-VARIABLE local counter (Alon-Spencer's
-- C[v,n], p.84) instead of a single shared global time. See the
-- 2026-09-14 planning notes: the book's own construction makes "the
-- n-th time v is used" a fact about a witness tree ALONE once n is
-- fixed, which a global-time index cannot give directly.
-- -------------------------------------------------------------------

/-- `ω`'s own coordinates at variable v, as v's time index n varies --
    a PLAIN (non-dependent-looking, once v is fixed) function `ℕ →
    S.space v`, rather than `ω` applied directly to a pair `(n, v)`.
    `ω (n, v) : S.space (n, v).2` does not reduce to `S.space v`
    automatically in every elaboration context (hit as a real compile
    error below when `measurable_eval_bounded` was first stated
    directly over `ω (idx a, v)`); routing every use through this one
    definition fixes the type once, here, instead of at every call
    site. -/
def atIdx {S : VarSpaces V} (ω : LogSpace S) (v : V) : ℕ → S.space v :=
  fun n => ω (n, v)

/-- Read a state where each variable v uses its OWN counter value
    `cnt v` as the LogSpace index, rather than every variable sharing
    one global time -- `LogSpace`'s TYPE (ℕ × V) doesn't change, only
    which coordinate gets consumed for a given variable's use. -/
def drawFrom {S : VarSpaces V} (ω : LogSpace S) (cnt : V → ℕ) : MTState S :=
  fun v => atIdx ω v (cnt v)

/-- Reading a single coordinate v at an index that is itself a
    measurable, BOUNDED (by some fixed N) function of another
    parameter a is measurable -- proved by chaining over the finitely
    many possible index values 0..N, the same technique as
    `pickFromList`'s chaining over ι. Induction on N: the base case
    N=0 forces `idx a = 0` everywhere, giving a constant function; the
    step splits on `idx a = N+1` (giving the constant `ω (N+1,v)`) vs.
    `idx a ≤ N` (handled by the IH applied to the "clamped" index
    `min (idx a) N`, which agrees with `idx` exactly where the split
    puts us). This is the tool `drawFrom ω (cnt ω)`'s measurability in
    ω needs below, since `cnt ω v` depends on the whole run so far but
    is always bounded by the number of steps taken. -/
theorem measurable_eval_bounded {S : VarSpaces V} (v : V) :
    ∀ (N : ℕ) (idx : LogSpace S → ℕ), Measurable idx → (∀ ω, idx ω ≤ N) →
    Measurable (fun ω : LogSpace S => atIdx ω v (idx ω))
  | 0, idx, hidx, hbound => by
      have heq : (fun ω : LogSpace S => atIdx ω v (idx ω)) = fun ω => atIdx ω v 0 := by
        funext ω; congr 1; exact Nat.le_zero.mp (hbound ω)
      rw [heq]
      exact measurable_pi_apply (0, v)
  | (N + 1), idx, hidx, hbound => by
      have hcond : MeasurableSet {ω : LogSpace S | idx ω = N + 1} :=
        hidx (measurableSet_singleton (N + 1))
      have hmin_meas : Measurable (fun ω => min (idx ω) N) := hidx.min measurable_const
      have hmin_bound : ∀ ω, min (idx ω) N ≤ N := fun ω => min_le_right _ _
      have ih := measurable_eval_bounded v N (fun ω => min (idx ω) N) hmin_meas hmin_bound
      have key : (fun ω : LogSpace S => atIdx ω v (idx ω)) =
          fun ω => if idx ω = N + 1 then atIdx ω v (N + 1) else atIdx ω v (min (idx ω) N) := by
        funext ω
        by_cases h : idx ω = N + 1
        · simp [h]
        · have hle : idx ω ≤ N := by have := hbound ω; omega
          simp [h, min_eq_left hle]
      rw [key]
      exact Measurable.ite hcond (measurable_pi_apply (N + 1, v)) ih

-- -------------------------------------------------------------------
-- The counter-driven step: state AND per-variable use-counts together
-- (kept alongside the OLD global-time `randTraj` below for now, while
-- this new machinery is being built up and verified piece by piece;
-- the old one is retired once this is confirmed working end to end).
-- -------------------------------------------------------------------

/-- One step of the counter-driven trajectory: `pickFirstViolated`
    decides which footprint to fix from the CURRENT state (never from
    the fresh draw about to be used, matching
    `randTraj_depends_on_past`'s reasoning); the fresh draw for that
    footprint comes from EACH variable's OWN counter via `drawFrom`,
    read at `counter + 1` rather than `counter` directly -- slot `0` of
    each variable's log is reserved for the INITIAL value `ω0`
    (matching Moser-Tardos's own convention, arXiv:0903.0544v3 p.5:
    "P was sampled at the beginning of the algorithm [slot 0] and then
    at the steps q(w) < q(v) for w ∈ S(P) [slots 1, 2, ...]"), so the
    FIRST actual resample of a variable must consume slot 1, not slot
    0. Every variable actually in the footprint has its counter bumped
    by one afterward (its own use just consumed that slot), everyone
    else keeps their counter unchanged. -/
noncomputable def randStep {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) : ℕ → MTState S × (V → ℕ)
  | 0 => (ω0, fun _ => 0)
  | (t + 1) =>
      let prev := randStep P ω0 ω t
      let F := P.footprint (pickFirstViolated P prev.1)
      (resample F prev.1 (drawFrom ω (fun v => prev.2 v + 1)),
        fun v => if v ∈ F then prev.2 v + 1 else prev.2 v)

/-- Every variable's counter after t steps is at most t: it can only
    ever be bumped once per step, and there are only t steps. Needed
    to invoke `measurable_eval_bounded` (with N := t) on the counter
    below. -/
theorem randCount_le {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) :
    ∀ (t : ℕ) (v : V), (randStep P ω0 ω t).2 v ≤ t
  | 0, v => le_refl 0
  | (t + 1), v => by
      show (if v ∈ P.footprint (pickFirstViolated P (randStep P ω0 ω t).1)
              then (randStep P ω0 ω t).2 v + 1 else (randStep P ω0 ω t).2 v) ≤ t + 1
      have ih := randCount_le P ω0 ω t v
      split_ifs <;> omega

/-- `randStep` is jointly measurable in ω, at every fixed t: both the
    state component and, for each v, the counter component. Induction
    on t, reusing the exact `resampleChain`/`resampleChain_eq_of_mem`
    argument `measurable_randTraj` uses below for the state half (with
    `drawFrom ω prev.2` standing in for `freshState ω t`), and
    `measurable_eval_bounded` (bound `t`, via `randCount_le`) for
    `drawFrom`'s own measurability; the counter half is a single
    `Measurable.ite` on "is v in the footprint", which is a pullback
    through `pickFirstViolated ∘ prev.1` of an ARBITRARY subset of ι --
    trivially measurable since ι carries `⊤`. -/
theorem measurable_randStep {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (ω0 : MTState S) :
    ∀ t, Measurable (fun ω : LogSpace S => (randStep P ω0 ω t).1) ∧
         ∀ v, Measurable (fun ω : LogSpace S => (randStep P ω0 ω t).2 v)
  | 0 => ⟨measurable_const, fun v => measurable_const⟩
  | (t + 1) => by
      obtain ⟨ihState, ihCount⟩ := measurable_randStep P hbad ω0 t
      have hdraw : Measurable (fun ω : LogSpace S =>
          drawFrom ω (fun v => (randStep P ω0 ω t).2 v + 1)) := by
        apply Measurable.of_eval
        intro v
        exact measurable_eval_bounded v (t + 1) (fun ω => (randStep P ω0 ω t).2 v + 1)
          ((ihCount v).add_const 1)
          (fun ω => by have := randCount_le P ω0 ω t v; omega)
      have hpair : Measurable (fun ω : LogSpace S =>
          ((randStep P ω0 ω t).1, drawFrom ω (fun v => (randStep P ω0 ω t).2 v + 1))) :=
        ihState.prodMk hdraw
      have hpick := measurable_pickFirstViolated P hbad
      have hchain := measurable_resampleChain P (pickFirstViolated P) hpick Finset.univ.toList
      have hcomp : Measurable (fun ω : LogSpace S =>
          resampleChain P (pickFirstViolated P) Finset.univ.toList
            (randStep P ω0 ω t).1 (drawFrom ω (fun v => (randStep P ω0 ω t).2 v + 1))) :=
        hchain.comp hpair
      have heqState : ∀ ω : LogSpace S,
          resampleChain P (pickFirstViolated P) Finset.univ.toList
            (randStep P ω0 ω t).1 (drawFrom ω (fun v => (randStep P ω0 ω t).2 v + 1))
          = resample (P.footprint (pickFirstViolated P (randStep P ω0 ω t).1))
              (randStep P ω0 ω t).1 (drawFrom ω (fun v => (randStep P ω0 ω t).2 v + 1)) := by
        intro ω
        exact resampleChain_eq_of_mem P (pickFirstViolated P) (randStep P ω0 ω t).1
          (drawFrom ω (fun v => (randStep P ω0 ω t).2 v + 1)) Finset.univ.toList
          (Finset.mem_toList.mpr (Finset.mem_univ _))
      have hstate : Measurable (fun ω : LogSpace S => (randStep P ω0 ω (t + 1)).1) := by
        show Measurable (fun ω : LogSpace S =>
          resample (P.footprint (pickFirstViolated P (randStep P ω0 ω t).1))
            (randStep P ω0 ω t).1 (drawFrom ω (fun v => (randStep P ω0 ω t).2 v + 1)))
        exact (funext heqState) ▸ hcomp
      have hcount : ∀ v, Measurable (fun ω : LogSpace S => (randStep P ω0 ω (t + 1)).2 v) := by
        intro v
        let : MeasurableSpace ι := ⊤
        have hpickComp : Measurable (fun ω : LogSpace S => pickFirstViolated P (randStep P ω0 ω t).1) :=
          hpick.comp ihState
        have hcond : MeasurableSet {ω : LogSpace S |
            v ∈ P.footprint (pickFirstViolated P (randStep P ω0 ω t).1)} := by
          have hset : {ω : LogSpace S |
              v ∈ P.footprint (pickFirstViolated P (randStep P ω0 ω t).1)}
              = (fun ω => pickFirstViolated P (randStep P ω0 ω t).1) ⁻¹'
                {i : ι | v ∈ P.footprint i} := rfl
          rw [hset]
          exact hpickComp MeasurableSpace.measurableSet_top
        have hthen : Measurable (fun ω : LogSpace S => (randStep P ω0 ω t).2 v + 1) :=
          (ihCount v).add_const 1
        show Measurable (fun ω : LogSpace S =>
          if v ∈ P.footprint (pickFirstViolated P (randStep P ω0 ω t).1)
          then (randStep P ω0 ω t).2 v + 1 else (randStep P ω0 ω t).2 v)
        exact Measurable.ite hcond hthen (ihCount v)
      exact ⟨hstate, hcount⟩

-- -------------------------------------------------------------------
-- The random trajectory and its measurability
-- -------------------------------------------------------------------

/-- The trajectory driven by a genuinely random log ω : LogSpace S --
    now just the state half of `randStep`, which reads each variable's
    fresh coordinates off its OWN local counter (Alon-Spencer's C[v,n],
    p.84) rather than a single shared global time. Kept as its own
    name/signature (state only, no counter in the return type) since
    that is the object every other file in this development actually
    wants: `pickFirstViolated P (randTraj ...)`, `violated P (randTraj
    ...)`, and so on never cared how the fresh draws were indexed
    internally. -/
noncomputable def randTraj {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) (t : ℕ) : MTState S :=
  (randStep P ω0 ω t).1

/-- `randTraj` is measurable in ω, at every fixed time t -- immediate
    from `measurable_randStep`'s state half. -/
theorem measurable_randTraj {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (ω0 : MTState S) (t : ℕ) :
    Measurable (fun ω : LogSpace S => randTraj P ω0 ω t) :=
  (measurable_randStep P hbad ω0 t).1

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @atIdx
#check @drawFrom
#check @measurable_eval_bounded
#check @randStep
#check @randCount_le
#check @measurable_randStep
#check @pickFromList
#check @measurable_pickFromList
#check @pickFromList_mem_or_default
#check @pickFirstViolated
#check @measurable_pickFirstViolated
#check @measurable_resample_fixed
#check @resampleChain
#check @measurable_resampleChain
#check @resampleChain_eq_of_mem
#check @randTraj
#check @measurable_randTraj
