/-
  Checkable closed bad classes for a finite rational transition kernel.

  A nonempty set of bad states with zero mass on every outgoing edge is
  a certificate of failure of global positive-mass accessibility. Every
  member has no positive-mass path to good. This does not exclude repair
  under another kernel or policy, or success from states outside the set.
  No external reachability computation is trusted by the checker.
-/

module

public import PPGraph.Finite.Potential.Basic

@[expose] public section

set_option linter.unusedSectionVars false

namespace FinitePotential

variable {S : Type*} [Fintype S] [DecidableEq S]

def ClosedBad (M : FiniteDrift.Model S) (U : S → Bool) : Prop :=
  (∃ s, U s = true) ∧
  (∀ s, U s = true → M.good s = false) ∧
  ∀ s t, U s = true → U t = false → M.transition s t = 0

instance closedBadDecidable (M : FiniteDrift.Model S) (U : S → Bool) :
    Decidable (ClosedBad M U) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def checkClosedBad (M : FiniteDrift.Model S) (U : S → Bool) : Bool :=
  decide (ClosedBad M U)

theorem checkClosedBad_iff (M : FiniteDrift.Model S) (U : S → Bool) :
    checkClosedBad M U = true ↔ ClosedBad M U := decide_eq_true_iff

theorem closedBad_step (M : FiniteDrift.Model S) (U : S → Bool)
    (h : ClosedBad M U) (s t : S) (hs : U s = true)
    (hp : 0 < M.transition s t) : U t = true := by
  cases ht : U t
  · have hz := h.2.2 s t hs ht
    rw [hz] at hp
    exact False.elim (lt_irrefl _ hp)
  · rfl

theorem closedBad_path (M : FiniteDrift.Model S) (U : S → Bool)
    (h : ClosedBad M U) (s t : S) (hs : U s = true)
    (hp : Relation.ReflTransGen (fun a b => 0 < M.transition a b) s t) :
    U t = true := by
  induction hp with
  | refl => exact hs
  | @tail b c _ hedge ih => exact closedBad_step M U h b c ih hedge

theorem closedBad_not_reachesGood (M : FiniteDrift.Model S) (U : S → Bool)
    (h : ClosedBad M U) (s : S) (hs : U s = true) : ¬ ReachesGood M s := by
  rintro ⟨g, hg, hp⟩
  have hb := h.2.1 g (closedBad_path M U h s g hs hp)
  exact Bool.false_ne_true (hb.symm.trans hg)

theorem checkedClosedBad_not_reachesGood (M : FiniteDrift.Model S) (U : S → Bool)
    (hc : checkClosedBad M U = true) (s : S) (hs : U s = true) :
    ¬ ReachesGood M s :=
  closedBad_not_reachesGood M U ((checkClosedBad_iff M U).mp hc) s hs

theorem closedBad_not_accessible (M : FiniteDrift.Model S) (U : S → Bool)
    (h : ClosedBad M U) : ¬ Accessible M := by
  obtain ⟨s, hs⟩ := h.1
  exact fun hr => closedBad_not_reachesGood M U h s hs (hr s)

theorem checkedClosedBad_no_global_witness (M : FiniteDrift.Model S) (U : S → Bool)
    (hc : checkClosedBad M U = true) :
    ¬ ∃ W, FiniteDrift.check M W = true := by
  rintro ⟨W, hW⟩
  exact closedBad_not_accessible M U ((checkClosedBad_iff M U).mp hc)
    (checked_accessible M W hW)

theorem checkedClosedBad_synthesize_none (M : FiniteDrift.Model S) (U : S → Bool)
    (hm : Stochastic M) (ha : Absorbing M) (hc : checkClosedBad M U = true) :
    synthesize M = none :=
  (synthesize_none_iff_not_accessible M hm ha).mpr
    (closedBad_not_accessible M U ((checkClosedBad_iff M U).mp hc))

theorem checkedClosedBad_det_zero (M : FiniteDrift.Model S) (U : S → Bool)
    (hm : Stochastic M) (ha : Absorbing M) (hc : checkClosedBad M U = true) :
    (systemMatrix M).det = 0 := by
  by_contra hn
  exact closedBad_not_accessible M U ((checkClosedBad_iff M U).mp hc)
    ((det_ne_zero_iff_accessible M hm ha).mp hn)

/-- Completeness is logical; the emitted finite membership vector is still checked. -/
theorem exists_checkedClosedBad_iff (M : FiniteDrift.Model S) (hm : Stochastic M) :
    (∃ U, checkClosedBad M U = true) ↔ ¬ Accessible M := by
  classical
  constructor
  · rintro ⟨U, hU⟩
    exact closedBad_not_accessible M U ((checkClosedBad_iff M U).mp hU)
  · intro hn
    let U : S → Bool := fun s => decide (¬ ReachesGood M s)
    refine ⟨U, (checkClosedBad_iff M U).mpr ?_⟩
    obtain ⟨s, hs⟩ := not_forall.mp hn
    refine ⟨⟨s, by simpa [U] using hs⟩, ?_, ?_⟩
    · intro t ht
      have hnr : ¬ ReachesGood M t := by simpa [U] using ht
      exact Bool.eq_false_iff.mpr (fun hg => hnr (good_reachesGood M t hg))
    · intro s t hs ht
      have hns : ¬ ReachesGood M s := by simpa [U] using hs
      have hrt : ReachesGood M t := by simpa [U] using ht
      by_contra hk
      have hp : 0 < M.transition s t := lt_of_le_of_ne (hm.1 s t) (Ne.symm hk)
      exact hns (reachesGood_of_step M s t hp hrt)

end FinitePotential

#check @FinitePotential.checkClosedBad_iff
#check @FinitePotential.closedBad_step
#check @FinitePotential.closedBad_path
#check @FinitePotential.closedBad_not_reachesGood
#check @FinitePotential.checkedClosedBad_not_reachesGood
#check @FinitePotential.closedBad_not_accessible
#check @FinitePotential.checkedClosedBad_no_global_witness
#check @FinitePotential.checkedClosedBad_synthesize_none
#check @FinitePotential.checkedClosedBad_det_zero
#check @FinitePotential.exists_checkedClosedBad_iff
