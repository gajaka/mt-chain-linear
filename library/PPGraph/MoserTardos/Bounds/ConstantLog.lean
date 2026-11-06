/-
  PPGraphMoserTardosConstantLog.lean

  Once a good target state exists, a constant resampling table gives
  an existential MT path to a good state from every initial state.
  The number of active steps is bounded by the number of coordinates
  initially different from the target. No probability claim is made
  about this particular table.
-/

module

public import PPGraph.MoserTardos.Bounds.Termination

@[expose] public section

variable {V : Type} {S : VarSpaces V}

/-- Every slot of every coordinate contains its value in the target. -/
def constantLog (z : MTState S) : LogSpace S := fun p => z p.2

@[simp] theorem drawFrom_constantLog (z : MTState S) (cnt : V → ℕ) :
    drawFrom (constantLog z) cnt = z := rfl

/-- The finite set of coordinates that do not yet match the target. -/
noncomputable def mtMismatch [Fintype V] (s z : MTState S) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => s v ≠ z v)

@[simp] theorem mem_mtMismatch [Fintype V] (s z : MTState S) (v : V) :
    v ∈ mtMismatch s z ↔ s v ≠ z v := by
  classical
  simp [mtMismatch]

/-- Drawing from the target cannot spoil a coordinate already equal to it. -/
theorem resample_eq_target_of_eq [DecidableEq V] (F : Finset V)
    (s z : MTState S) (v : V) (hv : s v = z v) :
    resample F s z v = z v := by
  by_cases hF : v ∈ F
  · simp only [resample, ite_eq_left hF]
  · simp only [resample, ite_eq_right hF, hv]

theorem mtMismatch_resample_subset [Fintype V] [DecidableEq V]
    (F : Finset V) (s z : MTState S) :
    mtMismatch (resample F s z) z ⊆ mtMismatch s z := by
  intro v hv
  apply (mem_mtMismatch s z v).mpr
  intro heq
  exact ((mem_mtMismatch (resample F s z) z v).mp hv)
    (resample_eq_target_of_eq F s z v heq)

/-- A violated event must contain a coordinate differing from a good target.
    Resampling its footprint therefore removes at least one mismatch. -/
theorem mtMismatch_resample_ssubset [Fintype V] [DecidableEq V] {ι : Type}
    (P : MTProcess S ι) (z : MTState S) (hz : MTGood P z)
    (s : MTState S) (i : ι) (hs : s ∈ P.bad i) :
    mtMismatch (resample (P.footprint i) s z) z ⊂ mtMismatch s z := by
  classical
  have hdiff : ∃ v ∈ P.footprint i, s v ≠ z v := by
    by_contra hnone
    have hagree : ∀ v ∈ P.footprint i, s v = z v := by
      intro v hv
      by_contra hne
      exact hnone ⟨v, hv, hne⟩
    exact hz i ((P.dep i s z hagree).mp hs)
  obtain ⟨v, hvF, hvne⟩ := hdiff
  refine Finset.ssubset_iff_subset_ne.mpr
    ⟨mtMismatch_resample_subset (P.footprint i) s z, ?_⟩
  intro heq
  have hvnew : v ∈ mtMismatch (resample (P.footprint i) s z) z := by
    rw [heq]
    exact (mem_mtMismatch s z v).mpr hvne
  exact ((mem_mtMismatch (resample (P.footprint i) s z) z v).mp hvnew)
    (by simp only [resample, ite_eq_left hvF])

section Trajectory

variable [DecidableEq V] {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- With a constant table, all local-counter reads give the same target. -/
theorem randTraj_constantLog_succ (P : MTProcess S ι) (ω0 z : MTState S) (t : ℕ) :
    randTraj P ω0 (constantLog z) (t + 1) =
      resample (P.footprint (pickFirstViolated P (randTraj P ω0 (constantLog z) t)))
        (randTraj P ω0 (constantLog z) t) z := rfl

/-- The mismatch rank strictly decreases at each time before success. -/
theorem mtMismatch_card_randTraj_constantLog_lt [Fintype V]
    (P : MTProcess S ι) (z : MTState S) (hz : MTGood P z)
    (ω0 : MTState S) (t : ℕ)
    (hnot : ¬ MTGood P (randTraj P ω0 (constantLog z) t)) :
    (mtMismatch (randTraj P ω0 (constantLog z) (t + 1)) z).card <
      (mtMismatch (randTraj P ω0 (constantLog z) t) z).card := by
  classical
  have hbad : randTraj P ω0 (constantLog z) t ∈
      P.bad (pickFirstViolated P (randTraj P ω0 (constantLog z) t)) := by
    by_contra havoid
    exact hnot ((pickFirstViolated_notMem_bad_iff P
      (randTraj P ω0 (constantLog z) t)).mp havoid)
  rw [randTraj_constantLog_succ]
  exact Finset.card_lt_card (mtMismatch_resample_ssubset P z hz
    (randTraj P ω0 (constantLog z) t) _ hbad)

/-- A good state is reached within the initial number of mismatches.
    The proof only uses active steps before the first good state. -/
theorem exists_good_randTraj_constantLog_le_mismatch [Fintype V]
    (P : MTProcess S ι) (z : MTState S) (hz : MTGood P z) (ω0 : MTState S) :
    ∃ T : ℕ, T ≤ (mtMismatch ω0 z).card ∧
      MTGood P (randTraj P ω0 (constantLog z) T) := by
  classical
  let r : ℕ → ℕ := fun t => (mtMismatch (randTraj P ω0 (constantLog z) t) z).card
  let N : ℕ := (mtMismatch ω0 z).card
  have hr0 : r 0 = N := rfl
  by_contra hnone
  have hdrop : ∀ t : ℕ, t ≤ N → r (t + 1) < r t := by
    intro t ht
    apply mtMismatch_card_randTraj_constantLog_lt P z hz ω0 t
    intro hgood
    exact hnone ⟨t, ht, hgood⟩
  have hrank : ∀ t : ℕ, t ≤ N + 1 → r t + t ≤ N := by
    intro t
    induction t with
    | zero =>
        intro _
        simpa only [Nat.add_zero, hr0] using (le_refl N)
    | succ t ih =>
        intro ht
        have htN : t ≤ N := by omega
        have hprev := ih (by omega)
        have hlt := hdrop t htN
        omega
  have hlast := hrank (N + 1) (le_refl _)
  omega

/-- Existential MT reachability from every start, bounded by the number
    of variables. The witnessing constant table need not have positive measure. -/
theorem exists_good_randTraj_constantLog [Fintype V]
    (P : MTProcess S ι) (z : MTState S) (hz : MTGood P z) (ω0 : MTState S) :
    ∃ T : ℕ, T ≤ Fintype.card V ∧
      MTGood P (randTraj P ω0 (constantLog z) T) := by
  obtain ⟨T, hT, hgood⟩ := exists_good_randTraj_constantLog_le_mismatch P z hz ω0
  exact ⟨T, hT.trans (Finset.card_le_univ (mtMismatch ω0 z)), hgood⟩

end Trajectory

-- Verification

#check @constantLog
#check @drawFrom_constantLog
#check @mtMismatch
#check @mem_mtMismatch
#check @resample_eq_target_of_eq
#check @mtMismatch_resample_subset
#check @mtMismatch_resample_ssubset
#check @randTraj_constantLog_succ
#check @mtMismatch_card_randTraj_constantLog_lt
#check @exists_good_randTraj_constantLog_le_mismatch
#check @exists_good_randTraj_constantLog
