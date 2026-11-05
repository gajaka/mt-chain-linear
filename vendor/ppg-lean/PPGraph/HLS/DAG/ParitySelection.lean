/-
  Reversible matching arcs lie along a chain. Splitting their source
  positions by parity gives two disjoint edge sets; the larger contains
  at least half the arcs. This proves the selection estimate behind
  He--Li--Sun Proposition 3.2 without assuming a maximal matching bound.
-/
module

public import PPGraph.HLS.DAG.CliqueRanks

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical

namespace HLS

variable {ν : Type} [DecidableEq ν]

noncomputable def parityEdges (E : Finset (ν × ν)) (rank : ν → ℕ) (b : ℕ) :
    Finset (ν × ν) := E.filter (fun e => rank e.1 % 2 = b)

noncomputable def largerParity (E : Finset (ν × ν)) (rank : ν → ℕ) : Finset (ν × ν) :=
  if (parityEdges E rank 0).card ≤ (parityEdges E rank 1).card
    then parityEdges E rank 1 else parityEdges E rank 0

theorem parityEdges_partition (E : Finset (ν × ν)) (rank : ν → ℕ) :
    parityEdges E rank 0 ∪ parityEdges E rank 1 = E := by
  ext e
  simp only [parityEdges, Finset.mem_union, Finset.mem_filter]
  have hmod : rank e.1 % 2 < 2 := Nat.mod_lt _ (by omega)
  have hcases : rank e.1 % 2 = 0 ∨ rank e.1 % 2 = 1 := by omega
  tauto

theorem parityEdges_disjoint (E : Finset (ν × ν)) (rank : ν → ℕ) :
    Disjoint (parityEdges E rank 0) (parityEdges E rank 1) := by
  apply Finset.disjoint_left.mpr
  intro e h₀ h₁
  have h₀ := (Finset.mem_filter.mp h₀).2
  have h₁ := (Finset.mem_filter.mp h₁).2
  omega

theorem largerParity_subset (E : Finset (ν × ν)) (rank : ν → ℕ) :
    largerParity E rank ⊆ E := by
  unfold largerParity
  split_ifs <;> exact Finset.filter_subset _ _

theorem largerParity_half (E : Finset (ν × ν)) (rank : ν → ℕ) :
    E.card ≤ 2 * (largerParity E rank).card := by
  have hcard := Finset.card_union_of_disjoint (parityEdges_disjoint E rank)
  rw [parityEdges_partition E rank] at hcard
  unfold largerParity
  split_ifs <;> omega

/-- Within one parity, distinct consecutive arcs cannot share an endpoint. -/
theorem parityEdges_endpoints_disjoint (E : Finset (ν × ν)) (rank : ν → ℕ)
    (hinj : ∀ u ∈ E.biUnion (fun e => {e.1, e.2}),
      ∀ v ∈ E.biUnion (fun e => {e.1, e.2}), rank u = rank v → u = v)
    (hcon : ∀ e ∈ E, rank e.2 = rank e.1 + 1) (b : ℕ)
    (e : ν × ν) (he : e ∈ parityEdges E rank b)
    (f : ν × ν) (hf : f ∈ parityEdges E rank b) (hne : e ≠ f) :
    Disjoint ({e.1, e.2} : Finset ν) {f.1, f.2} := by
  obtain ⟨heE, heb⟩ := Finset.mem_filter.mp he
  obtain ⟨hfE, hfb⟩ := Finset.mem_filter.mp hf
  have hecon := hcon e heE
  have hfcon := hcon f hfE
  have he₁ : e.1 ∈ E.biUnion (fun e => {e.1, e.2}) :=
    Finset.mem_biUnion.mpr ⟨e, heE, by simp⟩
  have he₂ : e.2 ∈ E.biUnion (fun e => {e.1, e.2}) :=
    Finset.mem_biUnion.mpr ⟨e, heE, by simp⟩
  have hf₁ : f.1 ∈ E.biUnion (fun e => {e.1, e.2}) :=
    Finset.mem_biUnion.mpr ⟨f, hfE, by simp⟩
  have hf₂ : f.2 ∈ E.biUnion (fun e => {e.1, e.2}) :=
    Finset.mem_biUnion.mpr ⟨f, hfE, by simp⟩
  apply Finset.disjoint_left.mpr
  intro w hwe hwf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hwe hwf
  rcases hwe with hwe | hwe <;> rcases hwf with hwf | hwf
  · have hleft : e.1 = f.1 := hwe.symm.trans hwf
    have hright : e.2 = f.2 := hinj _ he₂ _ hf₂ (by rw [hecon, hfcon, hleft])
    exact hne (Prod.ext hleft hright)
  · have hcross : e.1 = f.2 := hwe.symm.trans hwf
    have hmod := Nat.add_mod (rank f.1) 1 2
    rw [← hfcon, ← hcross] at hmod
    omega
  · have hcross : e.2 = f.1 := hwe.symm.trans hwf
    have hmod := Nat.add_mod (rank e.1) 1 2
    rw [← hecon, hcross] at hmod
    omega
  · have hright : e.2 = f.2 := hwe.symm.trans hwf
    have hrank := congrArg rank hright
    have hleft : e.1 = f.1 := hinj _ he₁ _ hf₁ (by omega)
    exact hne (Prod.ext hleft hright)

theorem largerParity_endpoints_disjoint (E : Finset (ν × ν)) (rank : ν → ℕ)
    (hinj : ∀ u ∈ E.biUnion (fun e => {e.1, e.2}),
      ∀ v ∈ E.biUnion (fun e => {e.1, e.2}), rank u = rank v → u = v)
    (hcon : ∀ e ∈ E, rank e.2 = rank e.1 + 1)
    (e : ν × ν) (he : e ∈ largerParity E rank)
    (f : ν × ν) (hf : f ∈ largerParity E rank) (hne : e ≠ f) :
    Disjoint ({e.1, e.2} : Finset ν) {f.1, f.2} := by
  unfold largerParity at he hf
  split_ifs at he hf <;> exact parityEdges_endpoints_disjoint E rank hinj hcon _ e he f hf hne

end HLS

#check @HLS.parityEdges_partition
#check @HLS.parityEdges_disjoint
#check @HLS.largerParity_subset
#check @HLS.largerParity_half
#check @HLS.parityEdges_endpoints_disjoint
#check @HLS.largerParity_endpoints_disjoint
