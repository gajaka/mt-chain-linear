/-
  The remaining half of MUS/MCS hitting-set duality.
  Liffiton--Sakallah, Algorithms for Computing Minimal Unsatisfiable Subsets
  of Constraints, JAR 40 (2008), Theorem 1(ii).
  These correction sets change the obligation family, not system states.
-/
module

public import PPGraph.Decision.UnsatisfiableCore

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RepairFeasibility

variable {State C : Type} [DecidableEq C]
variable (allowed : State → Prop) (sat : C → State → Prop)

theorem correctionSet_mono {B R T : Finset C} (hRT : R ⊆ T) (hTB : T ⊆ B)
    (hR : CorrectionSet allowed sat B R) : CorrectionSet allowed sat B T :=
  ⟨hTB, satisfiable_mono_obligations allowed sat (Finset.sdiff_subset_sdiff_right B hRT) hR.2⟩

theorem minimalCorrection_exists {B R : Finset C} (hR : CorrectionSet allowed sat B R) :
    ∃ M, M ⊆ R ∧ MinimalCorrectionSet allowed sat B M := by
  classical
  let corrections := R.powerset.filter (CorrectionSet allowed sat B)
  have hne : corrections.Nonempty := ⟨R, by simp [corrections, hR]⟩
  obtain ⟨M, hM, hmin⟩ := Finset.exists_min_image corrections Finset.card hne
  have hMR : M ⊆ R := Finset.mem_powerset.mp (Finset.mem_filter.mp hM).1
  have hMC := (Finset.mem_filter.mp hM).2
  refine ⟨M, hMR, hMC, ?_⟩
  intro c hc hbad
  have hm : M.erase c ∈ corrections := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr ((Finset.erase_subset c M).trans hMR), hbad⟩
  have hle := hmin (M.erase c) hm
  have hlt := Finset.card_erase_lt_of_mem hc
  omega

def HitsAllMinimalCorrections (B K : Finset C) : Prop :=
  ∀ M, MinimalCorrectionSet allowed sat B M → (K ∩ M).Nonempty

theorem infeasible_hits_correction {B K R : Finset C} (hKB : K ⊆ B)
    (hK : Infeasible allowed sat K) (hR : CorrectionSet allowed sat B R) :
    (K ∩ R).Nonempty := by
  classical
  by_contra hn
  apply hK
  apply satisfiable_mono_obligations allowed sat (B := B \ R) _ hR.2
  intro c hc
  refine Finset.mem_sdiff.mpr ⟨hKB hc, ?_⟩
  intro hr
  exact hn ⟨c, Finset.mem_inter.mpr ⟨hc, hr⟩⟩

theorem infeasible_iff_hitsAllMinimalCorrections {B K : Finset C} (hKB : K ⊆ B) :
    Infeasible allowed sat K ↔ HitsAllMinimalCorrections allowed sat B K := by
  classical
  constructor
  · intro h M hM
    exact infeasible_hits_correction allowed sat hKB h hM.1
  · intro hh hs
    have hr : CorrectionSet allowed sat B (B \ K) := by
      refine ⟨Finset.sdiff_subset, ?_⟩
      rw [Finset.sdiff_sdiff_eq_self hKB]
      exact hs
    obtain ⟨M, hMR, hM⟩ := minimalCorrection_exists allowed sat hr
    obtain ⟨c, hc⟩ := hh M hM
    exact (Finset.mem_sdiff.mp (hMR (Finset.mem_inter.mp hc).2)).2
      (Finset.mem_inter.mp hc).1

def MinimalCorrectionHittingSet (B K : Finset C) : Prop :=
  HitsAllMinimalCorrections allowed sat B K ∧
    ∀ c ∈ K, ¬ HitsAllMinimalCorrections allowed sat B (K.erase c)

theorem minimalCore_iff_minimalCorrectionHittingSet {B K : Finset C} (hKB : K ⊆ B) :
    MinimalCore allowed sat K ↔ MinimalCorrectionHittingSet allowed sat B K := by
  classical
  have hmain := infeasible_iff_hitsAllMinimalCorrections allowed sat hKB
  have herase : ∀ c, Infeasible allowed sat (K.erase c) ↔
      HitsAllMinimalCorrections allowed sat B (K.erase c) :=
    fun c => infeasible_iff_hitsAllMinimalCorrections allowed sat ((Finset.erase_subset c K).trans hKB)
  constructor
  · rintro ⟨hu, hm⟩
    refine ⟨hmain.mp hu, ?_⟩
    intro c hc hh
    exact (herase c).mpr hh (hm c hc)
  · rintro ⟨hh, hm⟩
    refine ⟨hmain.mpr hh, ?_⟩
    intro c hc
    by_contra hn
    exact hm c hc ((herase c).mp hn)

end RepairFeasibility

#check @RepairFeasibility.correctionSet_mono
#check @RepairFeasibility.minimalCorrection_exists
#check @RepairFeasibility.infeasible_hits_correction
#check @RepairFeasibility.infeasible_iff_hitsAllMinimalCorrections
#check @RepairFeasibility.minimalCore_iff_minimalCorrectionHittingSet
