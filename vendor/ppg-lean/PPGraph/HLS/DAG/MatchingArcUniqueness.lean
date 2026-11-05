/- A reversible matching arc has a unique matching successor. -/
module

public import PPGraph.HLS.DAG.PairKeys

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HLS.WitnessDAG

variable {ι : Type} [DecidableEq ι] {G : SimpleGraph ι}

theorem reversible_matching_target_unique (M : DependencyMatching G)
    (D : HLS.WitnessDAG ι) (hD : D.Valid G) (u v w : WNode ι)
    (huv : D.Edge u v) (huw : D.Edge u w)
    (hrv : Acyclic (reverseArc D.Edge u v)) (hrw : Acyclic (reverseArc D.Edge u w))
    (hmv : M.mate u.1 = v.1) (hmw : M.mate u.1 = w.1) : v = w := by
  have hvJ : v.1 ∈ M.pair u.1 := hmv ▸ M.mem_pair_mate u.1
  have hwJ : w.1 ∈ M.pair u.1 := hmw ▸ M.mem_pair_mate u.1
  have hv := cliqueRank_reversible_consecutive G D hD _ (M.pair_is_clique u.1)
    u v huv hrv (M.mem_pair_self u.1) hvJ
  have hw := cliqueRank_reversible_consecutive G D hD _ (M.pair_is_clique u.1)
    u w huw hrw (M.mem_pair_self u.1) hwJ
  exact eq_of_cliqueRank_eq G D hD _ (M.pair_is_clique u.1) v w
    (hD.supported _ _ huv).2 (hD.supported _ _ huw).2 hvJ hwJ (hv.trans hw.symm)

end HLS.WitnessDAG

#check @HLS.WitnessDAG.reversible_matching_target_unique
