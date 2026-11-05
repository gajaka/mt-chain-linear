/-
  Minimal unsatisfiable subsets (MUS), and correction/hitting-set duality.
  Liffiton--Sakallah, JAR 40 (2008), Definitions 2--3 and Theorem 1(i):
  https://sun.iwu.edu/~mliffito/publications/jar_liffiton_CAMUS.pdf
  A correction set removes specification obligations. It is a relaxation,
  not a state repair with the original specification held fixed.
-/
module

public import PPGraph.Decision.Infeasibility

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RepairFeasibility

variable {State C : Type} [DecidableEq C]
variable (allowed : State → Prop) (sat : C → State → Prop)

def MinimalCore (K : Finset C) : Prop :=
  Infeasible allowed sat K ∧ ∀ c ∈ K, Satisfiable allowed sat (K.erase c)

theorem minimalCore_infeasible (K : Finset C) (h : MinimalCore allowed sat K) :
    Infeasible allowed sat K := h.1

theorem minimalCore_blocks_superset {K B : Finset C} (hKB : K ⊆ B)
    (h : MinimalCore allowed sat K) : Infeasible allowed sat B :=
  infeasible_mono_obligations allowed sat hKB h.1

theorem minimalCore_nonempty (K : Finset C) (ha : ∃ z, allowed z)
    (h : MinimalCore allowed sat K) : K.Nonempty :=
  infeasible_nonempty allowed sat K ha h.1

theorem minimalCore_exists (B : Finset C) (hB : Infeasible allowed sat B) :
    ∃ K, K ⊆ B ∧ MinimalCore allowed sat K := by
  classical
  let cores := B.powerset.filter (Infeasible allowed sat)
  have hcores : cores.Nonempty := ⟨B, by simp [cores, hB]⟩
  obtain ⟨K, hK, hmin⟩ := Finset.exists_min_image cores Finset.card hcores
  have hKB : K ⊆ B := Finset.mem_powerset.mp (Finset.mem_filter.mp hK).1
  have hKU : Infeasible allowed sat K := (Finset.mem_filter.mp hK).2
  refine ⟨K, hKB, hKU, ?_⟩
  intro c hc
  by_contra hn
  have hm : K.erase c ∈ cores := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.Subset.trans (Finset.erase_subset c K) hKB), hn⟩
  have hle := hmin (K.erase c) hm
  have hlt := Finset.card_erase_lt_of_mem hc
  omega

theorem minimalCore_proper_subset_satisfiable {A K : Finset C}
    (hAK : A ⊂ K) (hK : MinimalCore allowed sat K) :
    Satisfiable allowed sat A := by
  obtain ⟨c, hcK, hcA⟩ := Finset.exists_of_ssubset hAK
  apply satisfiable_mono_obligations allowed sat (B := K.erase c) _ (hK.2 c hcK)
  intro a ha
  exact Finset.mem_erase.mpr ⟨fun he => hcA (he ▸ ha), hAK.1 ha⟩

def CorrectionSet (B R : Finset C) : Prop :=
  R ⊆ B ∧ Satisfiable allowed sat (B \ R)

def HitsAllMinimalCores (B R : Finset C) : Prop :=
  R ⊆ B ∧ ∀ K, K ⊆ B → MinimalCore allowed sat K → (K ∩ R).Nonempty

theorem correctionSet_hits_core {B R K : Finset C}
    (hR : CorrectionSet allowed sat B R) (hKB : K ⊆ B)
    (hK : MinimalCore allowed sat K) : (K ∩ R).Nonempty := by
  classical
  by_contra hn
  apply hK.1
  apply satisfiable_mono_obligations allowed sat (B := B \ R) _ hR.2
  intro c hc
  refine Finset.mem_sdiff.mpr ⟨hKB hc, ?_⟩
  intro hr
  exact hn ⟨c, Finset.mem_inter.mpr ⟨hc, hr⟩⟩

theorem correctionSet_iff_hitsAllMinimalCores (B R : Finset C) :
    CorrectionSet allowed sat B R ↔ HitsAllMinimalCores allowed sat B R := by
  classical
  constructor
  · intro h
    exact ⟨h.1, fun K hKB hK => correctionSet_hits_core allowed sat h hKB hK⟩
  · rintro ⟨hRB, hh⟩
    refine ⟨hRB, ?_⟩
    by_contra hn
    obtain ⟨K, hKBR, hK⟩ := minimalCore_exists allowed sat (B \ R) hn
    obtain ⟨c, hc⟩ := hh K (hKBR.trans (Finset.sdiff_subset)) hK
    exact (Finset.mem_sdiff.mp (hKBR (Finset.mem_inter.mp hc).1)).2
      (Finset.mem_inter.mp hc).2

def MinimalCorrectionSet (B R : Finset C) : Prop :=
  CorrectionSet allowed sat B R ∧
    ∀ c ∈ R, ¬ CorrectionSet allowed sat B (R.erase c)

def MinimalCoreHittingSet (B R : Finset C) : Prop :=
  HitsAllMinimalCores allowed sat B R ∧
    ∀ c ∈ R, ¬ HitsAllMinimalCores allowed sat B (R.erase c)

theorem minimalCorrectionSet_iff_minimalCoreHittingSet (B R : Finset C) :
    MinimalCorrectionSet allowed sat B R ↔ MinimalCoreHittingSet allowed sat B R := by
  simp only [MinimalCorrectionSet, MinimalCoreHittingSet,
    correctionSet_iff_hitsAllMinimalCores]

theorem correctionSet_empty_iff (B : Finset C) :
    CorrectionSet allowed sat B ∅ ↔ Satisfiable allowed sat B := by
  simp [CorrectionSet]

theorem infeasible_requires_nonempty_correction (B R : Finset C)
    (hB : Infeasible allowed sat B) (hR : CorrectionSet allowed sat B R) :
    R.Nonempty := by
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  exact hB ((correctionSet_empty_iff allowed sat B).mp (he ▸ hR))

end RepairFeasibility

#check @RepairFeasibility.minimalCore_infeasible
#check @RepairFeasibility.minimalCore_blocks_superset
#check @RepairFeasibility.minimalCore_nonempty
#check @RepairFeasibility.minimalCore_exists
#check @RepairFeasibility.minimalCore_proper_subset_satisfiable
#check @RepairFeasibility.correctionSet_hits_core
#check @RepairFeasibility.correctionSet_iff_hitsAllMinimalCores
#check @RepairFeasibility.minimalCorrectionSet_iff_minimalCoreHittingSet
#check @RepairFeasibility.correctionSet_empty_iff
#check @RepairFeasibility.infeasible_requires_nonempty_correction
