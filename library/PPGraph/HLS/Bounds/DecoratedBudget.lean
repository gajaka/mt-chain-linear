/-
  Split-label witness DAGs are represented by an ordinary canonical DAG
  with an up/down decoration of its nodes. Summing all decorations gives
  exactly the ordinary DAG weight at up+down, as in HLS Proposition 3.9.
-/
module

public import PPGraph.HLS.Bounds.WitnessBudget
public import PPGraph.HLS.DAG.Matching

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical
open scoped ENNReal

namespace HLS.WitnessDAG

variable {ι : Type} [DecidableEq ι]

abbrev DecoratedFamily (G : SimpleGraph ι) (B : Finset ι) (α : ι) :=
  Σ D : ProperFamily G B α, ↥(D.val.nodes.powerset)

noncomputable def decorationWeight (up down : ι → ℝ≥0∞) (D : HLS.WitnessDAG ι)
    (R : Finset (WNode ι)) : ℝ≥0∞ :=
  (∏ u ∈ R, down u.1) * ∏ u ∈ D.nodes \ R, up u.1

theorem sum_decorationWeight (up down : ι → ℝ≥0∞) (D : HLS.WitnessDAG ι) :
    (∑ R ∈ D.nodes.powerset, decorationWeight up down D R) =
      ∏ u ∈ D.nodes, (up u.1 + down u.1) := by
  simpa only [decorationWeight, add_comm] using
    (Finset.prod_add (fun u : WNode ι => down u.1) (fun u => up u.1) D.nodes).symm

theorem tsum_decorationWeight (up down : ι → ℝ≥0∞) (D : HLS.WitnessDAG ι) :
    (∑' R : ↥(D.nodes.powerset), decorationWeight up down D R.val) =
      ∏ u ∈ D.nodes, (up u.1 + down u.1) := by
  rw [tsum_fintype, Finset.sum_coe_sort]
  exact sum_decorationWeight up down D

theorem tsum_decoratedFamily_eq (G : SimpleGraph ι) (B : Finset ι) (α : ι)
    (up down : ι → ℝ≥0∞) :
    (∑' C : DecoratedFamily G B α, decorationWeight up down C.1.val C.2.val) =
      ∑' D : ProperFamily G B α, ∏ u ∈ D.val.nodes, (up u.1 + down u.1) := by
  calc
    _ = ∑' D : ProperFamily G B α, ∑' R : ↥(D.val.nodes.powerset),
        decorationWeight up down D.val R.val := ENNReal.tsum_sigma _
    _ = _ := tsum_congr (fun D => tsum_decorationWeight up down D.val)

theorem split_weights_add (G : SimpleGraph ι) (p : ι → ℝ) (O : OverlapBounds G p)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1) (i : ι) :
    ENNReal.ofReal (O.splitUp i) + ENNReal.ofReal (O.splitDown i) =
      ENNReal.ofReal (O.reduced i) := by
  have hup : 0 ≤ O.splitUp i := le_of_lt (O.prime_pos hp i)
  rw [← ENNReal.ofReal_add hup (O.splitDown_nonneg hp hp1 i),
    O.split_sum i]

theorem tsum_split_decoratedFamily_eq (G : SimpleGraph ι) (p : ι → ℝ)
    (O : OverlapBounds G p) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1)
    (B : Finset ι) (α : ι) :
    (∑' C : DecoratedFamily G B α,
      decorationWeight (fun i => ENNReal.ofReal (O.splitUp i))
        (fun i => ENNReal.ofReal (O.splitDown i)) C.1.val C.2.val) =
      ∑' D : ProperFamily G B α, weight O.reduced D.val := by
  rw [tsum_decoratedFamily_eq]
  apply tsum_congr
  intro D
  simp_rw [split_weights_add G p O hp hp1]
  exact (ENNReal.ofReal_prod_of_nonneg
    (fun u _ => le_of_lt (O.reduced_pos hp hp1 u.1))).symm

theorem tsum_split_decoratedFamily_le_budget (G : SimpleGraph ι) (p : ι → ℝ)
    (O : OverlapBounds G p) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1)
    (B : Finset ι) (α : ι) (hα : α ∈ B) (hc : Shearer.StrictCriterion G O.reduced B) :
    (∑' C : DecoratedFamily G B α,
      decorationWeight (fun i => ENNReal.ofReal (O.splitUp i))
        (fun i => ENNReal.ofReal (O.splitDown i)) C.1.val C.2.val) ≤
      ENNReal.ofReal (Shearer.stableBudget G O.reduced B {α}) := by
  rw [tsum_split_decoratedFamily_eq G p O hp hp1]
  exact tsum_weight_le_stableBudget G O.reduced B α hα
    (fun i _ => le_of_lt (O.reduced_pos hp hp1 i)) hc

end HLS.WitnessDAG

#check @HLS.WitnessDAG.sum_decorationWeight
#check @HLS.WitnessDAG.tsum_decorationWeight
#check @HLS.WitnessDAG.tsum_decoratedFamily_eq
#check @HLS.WitnessDAG.split_weights_add
#check @HLS.WitnessDAG.tsum_split_decoratedFamily_eq
#check @HLS.WitnessDAG.tsum_split_decoratedFamily_le_budget
