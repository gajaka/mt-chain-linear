/-
  Kolipaka--Szegedy weighted counting for canonical proper witness DAGs.
  An injective, weight-preserving stable-sequence encoding gives the
  existing Shearer coefficient budget. No assumption about runtime or
  probabilistic occurrence is used in this combinatorial theorem.
-/
module

public import PPGraph.HLS.Encoding.CanonicalEncoding
public import PPGraph.Shearer.Slack

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical
open scoped ENNReal

namespace HLS.WitnessDAG

variable {ι : Type*} [DecidableEq ι]

def IsProperCanonical (G : SimpleGraph ι) (B : Finset ι) (α : ι)
    (D : HLS.WitnessDAG ι) : Prop :=
  D.Valid G ∧ D.Canonical ∧ (∀ u ∈ D.nodes, u.1 ∈ B) ∧
    ∃ r ∈ D.nodes, r.1 = α ∧ ∀ u ∈ D.nodes, D.Reach u r

abbrev ProperFamily (G : SimpleGraph ι) (B : Finset ι) (α : ι) :=
  {D : HLS.WitnessDAG ι // IsProperCanonical G B α D}

noncomputable def familyEncoding (G : SimpleGraph ι) (B : Finset ι) (α : ι)
    (D : ProperFamily G B α) : List (Finset ι) := stableEncoding G D.1 D.2.1

noncomputable def weight (p : ι → ℝ) (D : HLS.WitnessDAG ι) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ u ∈ D.nodes, p u.1)

theorem familyEncoding_mem (G : SimpleGraph ι) (B : Finset ι) (α : ι)
    (D : ProperFamily G B α) :
    familyEncoding G B α D ∈ Shearer.properFamily G B {α} := by
  obtain ⟨r, hr, hlabel, hroot⟩ := D.2.2.2.2
  simpa only [familyEncoding, hlabel] using
    stableEncoding_mem_properFamily G D.1 D.2.1 B D.2.2.2.1 r hr hroot

theorem familyEncoding_injective (G : SimpleGraph ι) (B : Finset ι) (α : ι) :
    Function.Injective (familyEncoding G B α) := by
  intro D E h
  apply Subtype.ext
  exact eq_of_stableEncoding_eq G D.1 E.1 D.2.1 E.2.1 D.2.2.1 E.2.2.1 h

theorem weight_eq_properFamilyWeight (G : SimpleGraph ι) (p : ι → ℝ)
    (B : Finset ι) (α : ι) (D : ProperFamily G B α) :
    weight p D.1 = Shearer.properFamilyWeight G p B {α} (familyEncoding G B α D) := by
  rw [Shearer.properFamilyWeight, Set.indicator_of_mem (familyEncoding_mem G B α D)]
  exact congrArg ENNReal.ofReal (sequenceWeight_stableEncoding G D.1 D.2.1 p).symm

theorem tsum_weight_le_tsum_properFamilyWeight (G : SimpleGraph ι) (p : ι → ℝ)
    (B : Finset ι) (α : ι) :
    (∑' D : ProperFamily G B α, weight p D.1) ≤
      ∑' L : List (Finset ι), Shearer.properFamilyWeight G p B {α} L := by
  simp_rw [weight_eq_properFamilyWeight G p B α]
  exact ENNReal.tsum_comp_le_tsum_of_injective (familyEncoding_injective G B α) _

/-- Weighted proper DAG enumeration is bounded by the singleton q-ratio. -/
theorem tsum_weight_le_stableBudget (G : SimpleGraph ι) (p : ι → ℝ)
    (B : Finset ι) (α : ι) (hα : α ∈ B) (hp : ∀ i ∈ B, 0 ≤ p i)
    (hc : Shearer.StrictCriterion G p B) :
    (∑' D : ProperFamily G B α, weight p D.1) ≤
      ENNReal.ofReal (Shearer.stableBudget G p B {α}) := by
  have hi : Shearer.Independent G {α} := by simp [Shearer.Independent]
  exact (tsum_weight_le_tsum_properFamilyWeight G p B α).trans
    (Shearer.tsum_properFamilyWeight_le G p B {α} (Finset.singleton_subset_iff.mpr hα)
      hi hp hc)

theorem tsum_weight_lt_top (G : SimpleGraph ι) (p : ι → ℝ)
    (B : Finset ι) (α : ι) (hα : α ∈ B) (hp : ∀ i ∈ B, 0 ≤ p i)
    (hc : Shearer.StrictCriterion G p B) :
    (∑' D : ProperFamily G B α, weight p D.1) < ⊤ :=
  (tsum_weight_le_stableBudget G p B α hα hp hc).trans_lt ENNReal.ofReal_lt_top

theorem tsum_weight_le_inv_slack (G : SimpleGraph ι) (p : ι → ℝ)
    (B : Finset ι) (α : ι) (hα : α ∈ B) (hp : ∀ i ∈ B, 0 ≤ p i)
    (ε : ℝ) (hε : 0 < ε)
    (hslack : Shearer.StrictCriterion G (fun i => (1 + ε) * p i) B) :
    (∑' D : ProperFamily G B α, weight p D.1) ≤ ENNReal.ofReal (1 / ε) := by
  have hc := Shearer.strictCriterion_mono_weights G p _ B
    (fun i hi => by nlinarith [hp i hi]) hslack
  exact (tsum_weight_le_stableBudget G p B α hα hp hc).trans
    (ENNReal.ofReal_le_ofReal
      (Shearer.stableBudget_singleton_le_inv_slack G p B α hα ε hε hp hslack))

end HLS.WitnessDAG

#check @HLS.WitnessDAG.familyEncoding_mem
#check @HLS.WitnessDAG.familyEncoding_injective
#check @HLS.WitnessDAG.weight_eq_properFamilyWeight
#check @HLS.WitnessDAG.tsum_weight_le_tsum_properFamilyWeight
#check @HLS.WitnessDAG.tsum_weight_le_stableBudget
#check @HLS.WitnessDAG.tsum_weight_lt_top
#check @HLS.WitnessDAG.tsum_weight_le_inv_slack
