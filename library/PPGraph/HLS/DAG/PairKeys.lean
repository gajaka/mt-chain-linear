/- Unordered keys for the independent auxiliary coin tables. -/
module

public import PPGraph.HLS.DAG.CliqueRanks

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical

namespace HLS.DependencyMatching

variable {ι : Type} [DecidableEq ι] {G : SimpleGraph ι}

def pair (M : DependencyMatching G) (i : ι) : Finset ι := {i, M.mate i}

theorem mem_pair_self (M : DependencyMatching G) (i : ι) : i ∈ M.pair i := by simp [pair]

theorem mem_pair_mate (M : DependencyMatching G) (i : ι) : M.mate i ∈ M.pair i := by simp [pair]

theorem pair_mate (M : DependencyMatching G) (i : ι) : M.pair (M.mate i) = M.pair i := by
  simp only [pair, M.involutive i]
  exact Finset.pair_comm _ _

theorem pair_eq_of_mem (M : DependencyMatching G) (i j : ι) (h : j ∈ M.pair i) :
    M.pair j = M.pair i := by
  rcases Finset.mem_insert.mp h with h | h
  · simp only [h]
  · exact (Finset.mem_singleton.mp h) ▸ M.pair_mate i

theorem pair_disjoint_of_ne (M : DependencyMatching G) (i j : ι)
    (h : M.pair i ≠ M.pair j) : Disjoint (M.pair i) (M.pair j) := by
  apply Finset.disjoint_left.mpr
  intro k hki hkj
  exact h ((M.pair_eq_of_mem i k hki).symm.trans (M.pair_eq_of_mem j k hkj))

theorem pair_is_clique (M : DependencyMatching G) (i : ι) :
    WitnessDAG.LabelClique G (M.pair i) := by
  intro a ha b hb
  by_cases hi : M.mate i = i
  · have ha' : a = i := by simpa [pair, hi] using ha
    have hb' : b = i := by simpa [pair, hi] using hb
    exact Or.inl (ha'.trans hb'.symm)
  · have hadj := M.adjacent i hi
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hadj
    · exact Or.inr (G.adj_symm hadj)
    · exact Or.inl rfl

end HLS.DependencyMatching

#check @HLS.DependencyMatching.mem_pair_self
#check @HLS.DependencyMatching.mem_pair_mate
#check @HLS.DependencyMatching.pair_mate
#check @HLS.DependencyMatching.pair_eq_of_mem
#check @HLS.DependencyMatching.pair_disjoint_of_ne
#check @HLS.DependencyMatching.pair_is_clique
