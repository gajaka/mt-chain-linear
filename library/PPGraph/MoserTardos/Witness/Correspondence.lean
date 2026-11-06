/-
  PPGraphMoserTardosCorrespondence.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), Theorem 5.7.2, Lemma 2.1(ii).

  Connects the abstract witness-tree machinery (PPGraphMoserTardosGrowing,
  PPGraphMoserTardosCheckOrder, PPGraphMoserTardosCheckBirth) to the REAL
  random trajectory (PPGraphMoserTardosRandomTrajectory): specializes the
  scheduling function `C` to `realC`, the event actually picked at each
  real step, and proves the counting fact underlying Lemma 2.1(ii) --
  `localCount`'s tree-based count of deeper same-variable vertices should
  equal the REAL per-variable counter `randStep`'s `.2 v` at a vertex's
  own birth time.

  THIS FILE, so far: `realC` itself, and `randStep_count_eq_filter_card`
  -- rewriting `randStep`'s running counter as a `Finset.filter.card`, the
  form needed to eventually match it against `localCount` (also a
  `Finset.filter.card`, PPGraphMoserTardosCheck.lean) via a card-bijection
  argument. The bijection itself (using `birthStep_lt_iff_length_lt`,
  `candidates_nonempty_of_var_used`, `birthStep_eq_succ_of_new_attach`
  from PPGraphMoserTardosCheckBirth.lean to build the witness map) is the
  NEXT increment, not yet attempted here.

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.MoserTardos.Witness.CheckBirth
public import PPGraph.MoserTardos.Process.RandomTrajectory

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- realC: the scheduling function actually realized by the random
-- trajectory -- at real time s, the event `pickFirstViolated` picks
-- against the state AFTER s steps, matching `randStep`'s own step
-- indexing (`randStep (s+1)` resamples against `pickFirstViolated
-- (randStep s).1`).
-- -------------------------------------------------------------------

noncomputable def realC {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) (s : ℕ) : ι :=
  pickFirstViolated P (randStep P ω0 ω s).1

theorem realC_def {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) (s : ℕ) :
    realC P ω0 ω s = pickFirstViolated P (randStep P ω0 ω s).1 := rfl

-- -------------------------------------------------------------------
-- The piece Option A (see project memory) needs: `pickFirstViolated`
-- failing to land in its own pick's bad set is NOT a coincidence that
-- could also happen while something else is still violated -- it is
-- EXACTLY the same as nothing being violated anywhere. `pickFromList`'s
-- recursion has exactly two exhaustive, mutually exclusive outcomes: it
-- finds a genuine hit via `if_pos` (in which case membership in that
-- hit's bad set is guaranteed, whatever its value happens to be), or it
-- falls through the ENTIRE list without any hit (in which case every
-- element checked along the way -- and for `pickFirstViolated`, the
-- list is `Finset.univ.toList`, i.e. literally every element of ι --
-- failed the check). So there is no third case where the fallthrough
-- value happens to coincide with a genuine hit elsewhere: the two
-- outcomes are definitionally distinguished by which branch of the
-- recursion is taken, not by comparing values.
-- -------------------------------------------------------------------

/-- General form, before specializing to `Finset.univ.toList`: scanning
    `l` with `pickFromList`, the result avoids its OWN bad set iff every
    element of `l` avoided its bad set AND the `default` itself avoids
    its bad set (the latter conjunct is what the fallthrough case
    ultimately returns). -/
theorem pickFromList_notMem_bad_iff {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (default : ι) (ω' : MTState S) :
    ∀ l : List ι, ω' ∉ P.bad (pickFromList P default l ω')
      ↔ (∀ i ∈ l, ω' ∉ P.bad i) ∧ ω' ∉ P.bad default := by
  intro l
  induction l with
  | nil => simp [pickFromList]
  | cons i rest ih =>
      simp only [pickFromList]
      by_cases h : ω' ∈ P.bad i
      · rw [ite_eq_left h]
        constructor
        · intro hcontra; exact absurd h hcontra
        · rintro ⟨hall, _⟩; exact absurd h (hall i List.mem_cons_self)
      · rw [ite_eq_right h, ih]
        constructor
        · rintro ⟨hrest, hdef⟩
          refine ⟨fun j hj => ?_, hdef⟩
          rcases List.mem_cons.mp hj with hji | hj'
          · rw [hji]; exact h
          · exact hrest j hj'
        · rintro ⟨hall, hdef⟩
          exact ⟨fun j hj => hall j (List.mem_cons_of_mem i hj), hdef⟩

/-- Specialized to `pickFirstViolated`: since it scans `Finset.univ.toList`
    (literally every element of ι, `default` included), the `default`
    conjunct above is subsumed by the "every element" conjunct -- so
    avoiding one's own picked bad set is EXACTLY "nothing is violated
    anywhere", with no residual edge case. -/
theorem pickFirstViolated_notMem_bad_iff {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω' : MTState S) :
    ω' ∉ P.bad (pickFirstViolated P ω') ↔ ∀ i : ι, ω' ∉ P.bad i := by
  unfold pickFirstViolated
  rw [pickFromList_notMem_bad_iff]
  constructor
  · rintro ⟨hall, _⟩ i
    exact hall i (Finset.mem_toList.mpr (Finset.mem_univ i))
  · intro hall
    exact ⟨fun i _ => hall i, hall _⟩

/-- The form actually needed downstream: at real step `s`, the running
    trajectory's state avoids the bad set of whatever `realC` picked iff
    it satisfies the invariant everywhere (`∀ i, ... ∉ P.bad i`) -- i.e.
    `RunningUntil` failing at step `s` (see below) is exactly the process
    having reached a fully invariant-satisfying state, not a coincidental
    value clash. -/
theorem randStep_notMem_bad_realC_iff {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) (s : ℕ) :
    (randStep P ω0 ω s).1 ∉ P.bad (realC P ω0 ω s)
      ↔ ∀ i : ι, (randStep P ω0 ω s).1 ∉ P.bad i := by
  unfold realC
  exact pickFirstViolated_notMem_bad_iff P (randStep P ω0 ω s).1

-- -------------------------------------------------------------------
-- The real counter, restated as a Finset cardinality -- the shape
-- `localCount` already has, so the two can eventually be matched via a
-- card-bijection argument.
-- -------------------------------------------------------------------

/-- `randStep`'s running per-variable counter at real time `s` counts
    exactly the earlier real steps `s' < s` whose picked event's
    footprint used `v` -- unwinding `randStep`'s own recursive counter
    update one step at a time. -/
theorem randStep_count_eq_filter_card {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) (v : V) :
    ∀ s, (randStep P ω0 ω s).2 v =
      ((Finset.range s).filter (fun s' => v ∈ P.footprint (realC P ω0 ω s'))).card
  | 0 => by
      show (0 : ℕ) =
        ((Finset.range 0).filter (fun s' => v ∈ P.footprint (realC P ω0 ω s'))).card
      simp
  | (s + 1) => by
      have ih := randStep_count_eq_filter_card P ω0 ω v s
      show (if v ∈ P.footprint (pickFirstViolated P (randStep P ω0 ω s).1)
            then (randStep P ω0 ω s).2 v + 1 else (randStep P ω0 ω s).2 v) =
        ((Finset.range (s + 1)).filter (fun s' => v ∈ P.footprint (realC P ω0 ω s'))).card
      rw [← realC_def P ω0 ω s, Finset.range_add_one, Finset.filter_insert]
      by_cases h : v ∈ P.footprint (realC P ω0 ω s)
      · rw [ite_eq_left h, ite_eq_left h,
          Finset.card_insert_of_notMem (by simp), ih]
      · rw [ite_eq_right h, ite_eq_right h, ih]

-- -------------------------------------------------------------------
-- shiftedC: `realC` re-indexed to match `τC`'s 1-indexed scanning
-- convention (Moser-Tardos's own `C_1, C_2, ...` -- see
-- PPGraphMoserTardosCheckBirth.lean's `exists_birth_of_earlier_real_time`
-- docstring). `realC` itself is 0-indexed (`realC 0` is the trajectory's
-- very FIRST real resample), so `shiftedC (i+1) = realC i` aligns them:
-- feeding `shiftedC` as `τC`'s scheduling function makes the root
-- (`shiftedC t`) the trajectory's `(t-1)`-th resample, and the scanned
-- range `shiftedC 1 .. shiftedC (t-1)` become `realC 0 .. realC (t-2)`
-- -- EVERY earlier real resample, with no gap at the bottom.
-- -------------------------------------------------------------------

noncomputable def shiftedC {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) : ℕ → ι :=
  fun i => realC P ω0 ω (i - 1)

theorem shiftedC_succ {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) (s : ℕ) :
    shiftedC P ω0 ω (s + 1) = realC P ω0 ω s := rfl

-- -------------------------------------------------------------------
-- The central counting fact for Lemma 2.1(ii): the tree-based
-- `localCount` (deeper vertices sharing a variable) equals the real
-- per-variable counter `randStep` reaches at a vertex's own birth
-- time. Built as a `Finset.card_bij` between the tree side and the
-- real-time side, using `birthStep_lt_iff_length_lt` (injectivity /
-- the map lands in range) and `exists_birth_of_earlier_real_time`
-- (surjectivity), both from PPGraphMoserTardosCheckBirth.lean.
-- -------------------------------------------------------------------

theorem localCount_eq_randStep_count {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) (t : ℕ) (w : List ℕ)
    (hw : w ∈ (τC P (shiftedC P ω0 ω) t).dom) (v : V)
    (hwv : v ∈ P.footprint ((τC P (shiftedC P ω0 ω) t).lab w)) :
    localCount P (τC P (shiftedC P ω0 ω) t) w v =
      (randStep P ω0 ω (birthTime P (shiftedC P ω0 ω) t w hw - 1)).2 v := by
  show (((τC P (shiftedC P ω0 ω) t).dom).filter
      (fun w' => w.length < w'.length ∧ v ∈ P.footprint ((τC P (shiftedC P ω0 ω) t).lab w'))).card
    = (randStep P ω0 ω (birthTime P (shiftedC P ω0 ω) t w hw - 1)).2 v
  rw [randStep_count_eq_filter_card P ω0 ω v (birthTime P (shiftedC P ω0 ω) t w hw - 1)]
  refine Finset.card_bij
    (fun w' (hw'mem : w' ∈ ((τC P (shiftedC P ω0 ω) t).dom).filter
      (fun w' => w.length < w'.length ∧ v ∈ P.footprint ((τC P (shiftedC P ω0 ω) t).lab w'))) =>
      birthTime P (shiftedC P ω0 ω) t w' (Finset.mem_filter.mp hw'mem).1 - 1)
    ?_ ?_ ?_
  · intro w' hw'mem
    obtain ⟨hw'dom, hw'len, hw'v⟩ := Finset.mem_filter.mp hw'mem
    have hne : w ≠ w' := fun h => by rw [h] at hw'len; omega
    have hbslt : birthStep P (shiftedC P ω0 ω) t w hw
        < birthStep P (shiftedC P ω0 ω) t w' hw'dom :=
      (birthStep_lt_iff_length_lt P (shiftedC P ω0 ω) t w w' hw hw'dom hne v hwv hw'v).mpr hw'len
    have hb1 : birthStep P (shiftedC P ω0 ω) t w hw ≤ t - 1 :=
      birthStep_le_pred P (shiftedC P ω0 ω) t w hw
    have hb2 : birthStep P (shiftedC P ω0 ω) t w' hw'dom ≤ t - 1 :=
      birthStep_le_pred P (shiftedC P ω0 ω) t w' hw'dom
    have hbt'1 : 1 ≤ birthTime P (shiftedC P ω0 ω) t w' hw'dom := by
      unfold birthTime; omega
    have hbtlt : birthTime P (shiftedC P ω0 ω) t w' hw'dom
        < birthTime P (shiftedC P ω0 ω) t w hw := by
      unfold birthTime; omega
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have hlbl := birth_label P (shiftedC P ω0 ω) t w' hw'dom
    have hsucc : birthTime P (shiftedC P ω0 ω) t w' hw'dom
        = (birthTime P (shiftedC P ω0 ω) t w' hw'dom - 1) + 1 := by omega
    have hshift : shiftedC P ω0 ω (birthTime P (shiftedC P ω0 ω) t w' hw'dom)
        = realC P ω0 ω (birthTime P (shiftedC P ω0 ω) t w' hw'dom - 1) := by
      rw [hsucc]; exact shiftedC_succ P ω0 ω _
    rw [hlbl, hshift] at hw'v
    exact hw'v
  · intro w'1 hw'1mem w'2 hw'2mem heq
    obtain ⟨hw'1dom, hw'1len, hw'1v⟩ := Finset.mem_filter.mp hw'1mem
    obtain ⟨hw'2dom, hw'2len, hw'2v⟩ := Finset.mem_filter.mp hw'2mem
    have hne1 : w ≠ w'1 := fun h => by rw [h] at hw'1len; omega
    have hne2 : w ≠ w'2 := fun h => by rw [h] at hw'2len; omega
    have hbslt1 : birthStep P (shiftedC P ω0 ω) t w hw
        < birthStep P (shiftedC P ω0 ω) t w'1 hw'1dom :=
      (birthStep_lt_iff_length_lt P (shiftedC P ω0 ω) t w w'1 hw hw'1dom hne1 v hwv hw'1v).mpr
        hw'1len
    have hbslt2 : birthStep P (shiftedC P ω0 ω) t w hw
        < birthStep P (shiftedC P ω0 ω) t w'2 hw'2dom :=
      (birthStep_lt_iff_length_lt P (shiftedC P ω0 ω) t w w'2 hw hw'2dom hne2 v hwv hw'2v).mpr
        hw'2len
    have hbw1 : birthStep P (shiftedC P ω0 ω) t w'1 hw'1dom ≤ t - 1 :=
      birthStep_le_pred P (shiftedC P ω0 ω) t w'1 hw'1dom
    have hbw2 : birthStep P (shiftedC P ω0 ω) t w'2 hw'2dom ≤ t - 1 :=
      birthStep_le_pred P (shiftedC P ω0 ω) t w'2 hw'2dom
    have hb1 : 1 ≤ birthTime P (shiftedC P ω0 ω) t w'1 hw'1dom := by
      unfold birthTime; omega
    have hb2 : 1 ≤ birthTime P (shiftedC P ω0 ω) t w'2 hw'2dom := by
      unfold birthTime; omega
    have heq' : birthTime P (shiftedC P ω0 ω) t w'1 hw'1dom
        = birthTime P (shiftedC P ω0 ω) t w'2 hw'2dom := by omega
    exact birthTime_inj P (shiftedC P ω0 ω) t w'1 w'2 hw'1dom hw'2dom heq'
  · intro b hbmem
    rw [Finset.mem_filter, Finset.mem_range] at hbmem
    obtain ⟨hblt, hbv⟩ := hbmem
    have hrv : v ∈ P.footprint (shiftedC P ω0 ω (b + 1)) := by
      rw [shiftedC_succ]; exact hbv
    obtain ⟨w', hw'dom, hlabel, hbtime, hlen⟩ :=
      exists_birth_of_earlier_real_time P (shiftedC P ω0 ω) t w hw v hwv (b + 1)
        (by omega) (by omega) hrv
    have hw'v : v ∈ P.footprint ((τC P (shiftedC P ω0 ω) t).lab w') := by
      rw [hlabel]; exact hrv
    have hmem : w' ∈ ((τC P (shiftedC P ω0 ω) t).dom).filter
        (fun w' => w.length < w'.length ∧
          v ∈ P.footprint ((τC P (shiftedC P ω0 ω) t).lab w')) := by
      rw [Finset.mem_filter]
      exact ⟨hw'dom, hlen, hw'v⟩
    exact ⟨w', hmem, by rw [hbtime]; omega⟩

-- -------------------------------------------------------------------
-- The real trajectory's own state, restated via `atIdx` directly --
-- UNCONDITIONALLY (no case split on the counter being 0), given the
-- one hypothesis this needs: `ω0` itself agrees with the log's own
-- slot 0 for every variable (Moser-Tardos's own convention -- see
-- `randStep`'s docstring, PPGraphMoserTardosRandomTrajectory.lean).
-- Under that hypothesis, `ω0 v = atIdx ω v 0` already matches the
-- "counter = 0" case of what a resample would produce, so no
-- if-then-else is needed at all.
-- -------------------------------------------------------------------

theorem randStep_state_eq_atIdx {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S)
    (hω0 : ∀ v, ω0 v = atIdx ω v 0) :
    ∀ n v, (randStep P ω0 ω n).1 v = atIdx ω v ((randStep P ω0 ω n).2 v)
  | 0, v => hω0 v
  | (n + 1), v => by
      have ih := randStep_state_eq_atIdx P ω0 ω hω0 n v
      by_cases hv : v ∈ P.footprint (pickFirstViolated P (randStep P ω0 ω n).1)
      · show resample (P.footprint (pickFirstViolated P (randStep P ω0 ω n).1))
              (randStep P ω0 ω n).1 (drawFrom ω (fun v => (randStep P ω0 ω n).2 v + 1)) v
            = atIdx ω v (if v ∈ P.footprint (pickFirstViolated P (randStep P ω0 ω n).1)
                          then (randStep P ω0 ω n).2 v + 1 else (randStep P ω0 ω n).2 v)
        rw [ite_eq_left hv,
          resample_agrees_on (P.footprint (pickFirstViolated P (randStep P ω0 ω n).1))
            (randStep P ω0 ω n).1 (drawFrom ω (fun v => (randStep P ω0 ω n).2 v + 1)) v hv]
        rfl
      · show resample (P.footprint (pickFirstViolated P (randStep P ω0 ω n).1))
              (randStep P ω0 ω n).1 (drawFrom ω (fun v => (randStep P ω0 ω n).2 v + 1)) v
            = atIdx ω v (if v ∈ P.footprint (pickFirstViolated P (randStep P ω0 ω n).1)
                          then (randStep P ω0 ω n).2 v + 1 else (randStep P ω0 ω n).2 v)
        rw [ite_eq_right hv,
          resample_fixes_outside (P.footprint (pickFirstViolated P (randStep P ω0 ω n).1))
            (randStep P ω0 ω n).1 (drawFrom ω (fun v => (randStep P ω0 ω n).2 v + 1)) v hv]
        exact ih

-- -------------------------------------------------------------------
-- "The process hasn't converged before time t": at every real step
-- strictly before t, the event `pickFirstViolated` picks really IS
-- violated at that state -- the hypothesis that distinguishes a
-- genuine, still-running execution from one that already found a
-- fully satisfying assignment (in which case `pickFirstViolated`
-- would just be returning the arbitrary default, not a real
-- violation).
-- -------------------------------------------------------------------

def RunningUntil {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) (t : ℕ) : Prop :=
  ∀ s < t, (randStep P ω0 ω s).1 ∈ P.bad (realC P ω0 ω s)

-- -------------------------------------------------------------------
-- Lemma 2.1(ii): the witness tree built from
-- a genuine (still-running) real trajectory passes its own τ-check --
-- `checkState` (tree-reconstructed, via `localCount_eq_randStep_count`
-- + `randStep_state_eq_atIdx`) agrees with the real state
-- `(randStep s).1` on every variable that matters (the label's own
-- footprint), and that real state is bad there (`hrun`), so
-- `depends_only_on` (`P.dep`) carries the bad-membership across.
-- -------------------------------------------------------------------

theorem τCheck_holds_of_real_trajectory {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) (t : ℕ) (ht : 1 ≤ t)
    (hω0 : ∀ v, ω0 v = atIdx ω v 0)
    (hrun : RunningUntil P ω0 ω t) :
    τCheck P (τC P (shiftedC P ω0 ω) t) ω := by
  intro w hw
  have hble : birthStep P (shiftedC P ω0 ω) t w hw ≤ t - 1 :=
    birthStep_le_pred P (shiftedC P ω0 ω) t w hw
  have hbge : 1 ≤ birthTime P (shiftedC P ω0 ω) t w hw := by
    unfold birthTime; omega
  have hslt : birthTime P (shiftedC P ω0 ω) t w hw - 1 < t := by
    unfold birthTime at hbge ⊢; omega
  have hsucc : (birthTime P (shiftedC P ω0 ω) t w hw - 1) + 1
      = birthTime P (shiftedC P ω0 ω) t w hw := by omega
  have hlab : (τC P (shiftedC P ω0 ω) t).lab w
      = realC P ω0 ω (birthTime P (shiftedC P ω0 ω) t w hw - 1) := by
    have hbl := birth_label P (shiftedC P ω0 ω) t w hw
    rw [← hsucc, shiftedC_succ] at hbl
    exact hbl
  have hagree : ∀ v ∈ P.footprint (realC P ω0 ω (birthTime P (shiftedC P ω0 ω) t w hw - 1)),
      checkState P (τC P (shiftedC P ω0 ω) t) ω w v
        = (randStep P ω0 ω (birthTime P (shiftedC P ω0 ω) t w hw - 1)).1 v := by
    intro v hv
    rw [← hlab] at hv
    show atIdx ω v (localCount P (τC P (shiftedC P ω0 ω) t) w v)
      = (randStep P ω0 ω (birthTime P (shiftedC P ω0 ω) t w hw - 1)).1 v
    rw [localCount_eq_randStep_count P ω0 ω t w hw v hv]
    exact (randStep_state_eq_atIdx P ω0 ω hω0 (birthTime P (shiftedC P ω0 ω) t w hw - 1) v).symm
  have hviol : (randStep P ω0 ω (birthTime P (shiftedC P ω0 ω) t w hw - 1)).1
      ∈ P.bad (realC P ω0 ω (birthTime P (shiftedC P ω0 ω) t w hw - 1)) :=
    hrun (birthTime P (shiftedC P ω0 ω) t w hw - 1) hslt
  show checkState P (τC P (shiftedC P ω0 ω) t) ω w ∈ P.bad ((τC P (shiftedC P ω0 ω) t).lab w)
  rw [hlab]
  exact (P.dep (realC P ω0 ω (birthTime P (shiftedC P ω0 ω) t w hw - 1))
    (checkState P (τC P (shiftedC P ω0 ω) t) ω w)
    (randStep P ω0 ω (birthTime P (shiftedC P ω0 ω) t w hw - 1)).1
    hagree).mpr hviol

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @realC
#check @realC_def
#check @randStep_count_eq_filter_card
#check @shiftedC
#check @shiftedC_succ
#check @localCount_eq_randStep_count
#check @randStep_state_eq_atIdx
#check @RunningUntil
#check @τCheck_holds_of_real_trajectory

-- Explicit checks for all remaining helper theorems.
#check @pickFirstViolated_notMem_bad_iff
#check @pickFromList_notMem_bad_iff
#check @randStep_notMem_bad_realC_iff
