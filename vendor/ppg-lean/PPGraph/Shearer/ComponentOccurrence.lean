/-
  PPGraphShearerComponentOccurrence.lean

  A stable sequence rooted inside one BDD component stays in that component.
  Hence the expected number of resamplings of an event in the existing global
  MT run is bounded by its component's Shearer budget, assuming the strict
  criterion only on that full component.

  The runtime statement uses components of the entire event family. It bounds
  work actually performed in the component; it does not assert that the global
  selector eventually services that component or that the global run terminates.
-/

module

public import PPGraph.Shearer.Expectation

@[expose] public section

set_option autoImplicit false
-- CertVars is the existing alias for a family of variable footprints.
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Classical
open scoped ENNReal

namespace Shearer

variable {C V : Type} [DecidableEq C] [DecidableEq V]

/-- The closed neighborhood of roots in a component remains in that component. -/
theorem closed_compOf (vars : CertVars C V) (B : Finset C) (c : C)
    (J : Finset C) (hJ : J ⊆ compOf vars B c) :
    closed (dependencyGraph vars) B J =
      closed (dependencyGraph vars) (compOf vars B c) J := by
  ext b
  simp only [closed, Finset.mem_filter]
  constructor
  · rintro ⟨hb, hnear⟩
    refine ⟨?_, hnear⟩
    rcases hnear with hbJ | ⟨a, haJ, hab⟩
    · exact hJ hbJ
    · by_contra hbK
      exact not_adj_compOf_sdiff vars B c a (hJ haJ) b
        (Finset.mem_sdiff.mpr ⟨hb, hbK⟩) hab
  · rintro ⟨hb, hnear⟩
    exact ⟨compOf_subset vars B c hb, hnear⟩

theorem successors_compOf (vars : CertVars C V) (B : Finset C) (c : C)
    (J : Finset C) (hJ : J ⊆ compOf vars B c) :
    successors (dependencyGraph vars) B J =
      successors (dependencyGraph vars) (compOf vars B c) J := by
  unfold successors
  rw [closed_compOf vars B c J hJ]

/-- The full and component-local enumerations contain exactly the same
stable sequences when their initial layer is inside the component. -/
theorem stableSequences_compOf (vars : CertVars C V) (B : Finset C) (c : C)
    (d : ℕ) (J : Finset C) (hJ : J ⊆ compOf vars B c) :
    stableSequences (dependencyGraph vars) B d J =
      stableSequences (dependencyGraph vars) (compOf vars B c) d J := by
  induction d generalizing J with
  | zero => rfl
  | succ d ih =>
    simp only [stableSequences]
    rw [successors_compOf vars B c J hJ]
    apply Finset.biUnion_congr rfl
    intro K hK
    have hKsub : K ⊆ compOf vars B c :=
      ((mem_successors (dependencyGraph vars) (compOf vars B c) J K).mp hK).1.trans
        (closed_subset (dependencyGraph vars) (compOf vars B c) J)
    rw [ih K hKsub]

/-- Confinement does not require a depth bound or a probability criterion. -/
theorem properFamily_compOf (vars : CertVars C V) (B : Finset C) (c : C)
    (J : Finset C) (hJ : J ⊆ compOf vars B c) :
    properFamily (dependencyGraph vars) B J =
      properFamily (dependencyGraph vars) (compOf vars B c) J := by
  ext L
  constructor
  · rintro ⟨⟨d, hd⟩, hproper⟩
    refine ⟨⟨d, ?_⟩, hproper⟩
    rwa [← stableSequences_compOf vars B c d J hJ]
  · rintro ⟨⟨d, hd⟩, hproper⟩
    refine ⟨⟨d, ?_⟩, hproper⟩
    rwa [stableSequences_compOf vars B c d J hJ]

theorem properFamilyWeight_compOf (vars : CertVars C V) (p : C → ℝ)
    (B : Finset C) (c : C) (J : Finset C) (hJ : J ⊆ compOf vars B c)
    (L : List (Finset C)) :
    properFamilyWeight (dependencyGraph vars) p B J L =
      properFamilyWeight (dependencyGraph vars) p (compOf vars B c) J L := by
  unfold properFamilyWeight
  rw [properFamily_compOf vars B c J hJ]

variable {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The local strict criterion controls work on this full component even
when no Shearer criterion is assumed for any other component. -/
theorem randomInitExpectedResamplingCount_le_componentBudget [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ)
    (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (c α : ι) (hα : α ∈ compOf P.footprint Finset.univ c)
    (hcriterion : StrictCriterion (dependencyGraph P.footprint) p
      (compOf P.footprint Finset.univ c)) :
    randomInitExpectedResamplingCount P α ≤ ENNReal.ofReal
      (stableBudget (dependencyGraph P.footprint) p (compOf P.footprint Finset.univ c) {α}) := by
  obtain ⟨hn, hm⟩ := event_prob_bounds P p hp
  have hsingleton : Independent (dependencyGraph P.footprint) {α} := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a
    subst b
    exact (dependencyGraph P.footprint).irrefl
  have hsub : {α} ⊆ compOf P.footprint Finset.univ c :=
    Finset.singleton_subset_iff.mpr hα
  calc
    randomInitExpectedResamplingCount P α ≤ ∑' L : List (Finset ι),
        properFamilyWeight (dependencyGraph P.footprint) p Finset.univ {α} L :=
      randomInitExpectedResamplingCount_le_tsum_properFamilyWeight P hbad p hn hm α
    _ = ∑' L : List (Finset ι),
        properFamilyWeight (dependencyGraph P.footprint) p
          (compOf P.footprint Finset.univ c) {α} L := by
      apply tsum_congr
      intro L
      exact properFamilyWeight_compOf P.footprint p Finset.univ c {α} hsub L
    _ ≤ ENNReal.ofReal
        (stableBudget (dependencyGraph P.footprint) p
          (compOf P.footprint Finset.univ c) {α}) :=
      tsum_properFamilyWeight_le (dependencyGraph P.footprint) p
        (compOf P.footprint Finset.univ c) {α} hsub hsingleton
        (fun i _ => hn i) hcriterion

end Shearer

#check @Shearer.closed_compOf
#check @Shearer.successors_compOf
#check @Shearer.stableSequences_compOf
#check @Shearer.properFamily_compOf
#check @Shearer.properFamilyWeight_compOf
#check @Shearer.randomInitExpectedResamplingCount_le_componentBudget
