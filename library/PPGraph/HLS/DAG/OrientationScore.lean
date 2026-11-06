/-
  A finite preference score for the auxiliary orientation table. Reversing
  an inconsistent matching arc on a fixed node set strictly increases
  this score. Powers of two express lexicographic preference along each
  matching-pair chain; they are not probability bounds.
-/
module

public import PPGraph.HLS.DAG.PairKeys
public import PPGraph.HLS.DAG.FiniteDAG

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [DecidableEq ι] {G : SimpleGraph ι}

noncomputable def preferenceTerm (M : DependencyMatching G)
    (Y : Finset ι × ℕ → ι) (N : ℕ) (D : HLS.WitnessDAG ι) (u : WNode ι) : ℕ :=
  if Y (M.pair u.1, D.cliqueRank (M.pair u.1) u) = u.1
    then 2 ^ (N - D.cliqueRank (M.pair u.1) u) else 0

noncomputable def orientationScore (M : DependencyMatching G)
    (Y : Finset ι × ℕ → ι) (N : ℕ) (D : HLS.WitnessDAG ι) : ℕ :=
  ∑ u ∈ D.nodes, preferenceTerm M Y N D u

theorem preferenceTerm_reverse_other (M : DependencyMatching G)
    (Y : Finset ι × ℕ → ι) (N : ℕ) (D : HLS.WitnessDAG ι)
    (u v w : WNode ι) (hwu : w ≠ u) (hwv : w ≠ v) :
    preferenceTerm M Y N (D.reverse u v) w = preferenceTerm M Y N D w := by
  simp only [preferenceTerm, cliqueRank, cliquePrior_reverse_other D _ u v w hwu hwv]

theorem sum_erase_two (s : Finset (WNode ι)) (f : WNode ι → ℕ)
    (u v : WNode ι) (hu : u ∈ s) (hv : v ∈ s) (hne : u ≠ v) :
    (∑ w ∈ s, f w) = (∑ w ∈ (s.erase u).erase v, f w) + f u + f v := by
  have hv' : v ∈ s.erase u := Finset.mem_erase.mpr ⟨hne.symm, hv⟩
  have h₁ := Finset.sum_erase_add s f hu
  have h₂ := Finset.sum_erase_add (s.erase u) f hv'
  omega

theorem rank_power_strict (N k : ℕ) (h : k + 1 ≤ N) :
    2 ^ (N - (k + 1)) < (2 : ℕ) ^ (N - k) := by
  have heq : N - k = (N - (k + 1)) + 1 := by omega
  rw [heq, pow_succ]
  have hpos : 0 < (2 : ℕ) ^ (N - (k + 1)) := pow_pos (by omega) _
  omega

/-- The changed pair gains at its earlier index; any loss is later and smaller. -/
theorem orientationScore_reverse_strict (M : DependencyMatching G)
    (Y : Finset ι × ℕ → ι) (N : ℕ) (D : HLS.WitnessDAG ι) (hD : D.Valid G)
    (hN : D.nodes.card ≤ N) (u v : WNode ι) (he : D.Edge u v)
    (hrev : Acyclic (reverseArc D.Edge u v)) (hm : M.mate u.1 = v.1)
    (hl : u.1 ≠ v.1)
    (hY : Y (M.pair u.1, D.cliqueRank (M.pair u.1) u) = v.1) :
    orientationScore M Y N D < orientationScore M Y N (D.reverse u v) := by
  have hu := (hD.supported _ _ he).1
  have hv := (hD.supported _ _ he).2
  have hne := edge_ne G D hD u v he
  have hpair : M.pair v.1 = M.pair u.1 := by rw [← hm]; exact M.pair_mate u.1
  have huJ := M.mem_pair_self u.1
  have hvJ : v.1 ∈ M.pair u.1 := hm ▸ M.mem_pair_mate u.1
  have hclique := M.pair_is_clique u.1
  have hcon := cliqueRank_reversible_consecutive G D hD _ hclique u v he hrev huJ hvJ
  have hs := cliqueRank_reverse_source G D hD _ hclique u v he hrev huJ hvJ
  have ht := cliqueRank_reverse_target G D hD _ hclique u v he hrev huJ hvJ
  let k := D.cliqueRank (M.pair u.1) u
  have hkN : k + 1 ≤ N := by
    have hvlt := cliqueRank_lt_card G D hD (M.pair u.1) v hv
    omega
  have holdU : preferenceTerm M Y N D u = 0 := by
    simp only [preferenceTerm, hY, Ne.symm hl, ite_false]
  have hnewV : preferenceTerm M Y N (D.reverse u v) v = 2 ^ (N - k) := by
    simp only [preferenceTerm, hpair, ht, hY, ite_true]
    rfl
  have holdV : preferenceTerm M Y N D v ≤ 2 ^ (N - (k + 1)) := by
    dsimp only [k]
    simp only [preferenceTerm, hpair, hcon]
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _
  have hgain := rank_power_strict N k hkN
  have hrest : (∑ w ∈ (D.nodes.erase u).erase v, preferenceTerm M Y N (D.reverse u v) w) =
      ∑ w ∈ (D.nodes.erase u).erase v, preferenceTerm M Y N D w := by
    apply Finset.sum_congr rfl
    intro w hw
    have hwv := (Finset.mem_erase.mp hw).1
    have hwu := (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
    exact preferenceTerm_reverse_other M Y N D u v w hwu hwv
  have hsumOld := sum_erase_two D.nodes (preferenceTerm M Y N D) u v hu hv hne
  have hsumNew := sum_erase_two D.nodes (preferenceTerm M Y N (D.reverse u v)) u v hu hv hne
  change (∑ w ∈ D.nodes, preferenceTerm M Y N D w) <
    ∑ w ∈ D.nodes, preferenceTerm M Y N (D.reverse u v) w
  omega

end HLS.WitnessDAG

#check @HLS.WitnessDAG.preferenceTerm_reverse_other
#check @HLS.WitnessDAG.sum_erase_two
#check @HLS.WitnessDAG.rank_power_strict
#check @HLS.WitnessDAG.orientationScore_reverse_strict
