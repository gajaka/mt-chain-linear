/-
  Deterministic content of He--Li--Sun Lemma 3.1: for every fixed
  auxiliary table, a consistent proper DAG can be replaced by one that
  satisfies all augmented orientation tests, keeping the same root.

  Instead of excluding cycles in the flip procedure, minimize node count
  and maximize the finite orientation score. A permitted flip would
  either shrink the graph or strictly improve its score. Both contradict
  extremality. Thus this proof does not assume algorithm termination.
-/
module

public import PPGraph.HLS.DAG.OrientationScore
public import PPGraph.HLS.Encoding.PrefixCheck

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {V : Type} [DecidableEq V] {S : VarSpaces V}
    {ι : Type} [Fintype ι] [DecidableEq ι]

def AugmentedCheck (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (Y : Finset ι × ℕ → ι) (r : WNode ι) (D : HLS.WitnessDAG ι) (ω : LogSpace S) : Prop :=
  ω ∈ tableCheck P D ∧
    ∀ u v, D.Edge u v → Acyclic (reverseArc D.Edge u v) →
      M.mate u.1 = v.1 → u.1 ≠ v.1 →
      Y (M.pair u.1, D.cliqueRank (M.pair u.1) u) = v.1 →
      ω ∉ tableCheck P ((D.reverse u v).ancestorPrefix r)

theorem exists_augmented_same_root (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (Y : Finset ι × ℕ → ι) (r : WNode ι) (D₀ : HLS.WitnessDAG ι)
    (hD₀ : RootedCanonical (Shearer.dependencyGraph P.footprint) r D₀)
    (ω : LogSpace S) (hω₀ : ω ∈ tableCheck P D₀) :
    ∃ D : HLS.WitnessDAG ι,
      RootedCanonical (Shearer.dependencyGraph P.footprint) r D ∧
        D.nodes.card ≤ D₀.nodes.card ∧ AugmentedCheck P M Y r D ω := by
  let G := Shearer.dependencyGraph P.footprint
  let N := D₀.nodes.card
  let F := (boundedDAGs (ι := ι) N).filter
    (fun D => RootedCanonical G r D ∧ D.nodes.card ≤ N ∧ ω ∈ tableCheck P D)
  have hF₀ : D₀ ∈ F := Finset.mem_filter.mpr
    ⟨mem_boundedDAGs_of_canonical G D₀ hD₀.1 hD₀.2.1 N le_rfl, hD₀, le_rfl, hω₀⟩
  obtain ⟨E, hE, hmin⟩ := F.exists_min_image (fun D => D.nodes.card) ⟨D₀, hF₀⟩
  let H := F.filter (fun D => D.nodes.card = E.nodes.card)
  have hH : H.Nonempty := ⟨E, Finset.mem_filter.mpr ⟨hE, rfl⟩⟩
  obtain ⟨D, hDH, hmax⟩ := H.exists_max_image (orientationScore M Y N) hH
  obtain ⟨hDF, hDE⟩ := Finset.mem_filter.mp hDH
  obtain ⟨_, hDr, hDN, hωD⟩ := Finset.mem_filter.mp hDF
  refine ⟨D, hDr, hDN, hωD, ?_⟩
  intro u v he hrev hm hl hY hωFlip
  let K := (D.reverse u v).ancestorPrefix r
  have hKr : RootedCanonical G r K := hDr.flippedPrefix u v he hrev hl
  have hsub : K.nodes ⊆ D.nodes := Finset.filter_subset _ _
  have hcard : K.nodes.card ≤ D.nodes.card := Finset.card_le_card hsub
  have hKN : K.nodes.card ≤ N := hcard.trans hDN
  have hKF : K ∈ F := Finset.mem_filter.mpr
    ⟨mem_boundedDAGs_of_canonical G K hKr.1 hKr.2.1 N hKN, hKr, hKN, hωFlip⟩
  have hreverseCard : D.nodes.card ≤ K.nodes.card := hDE ▸ hmin K hKF
  have hcards : K.nodes.card = D.nodes.card := le_antisymm hcard hreverseCard
  have hnodes : K.nodes = D.nodes := Finset.eq_of_subset_of_card_le hsub hreverseCard
  have hKrev : K = D.reverse u v :=
    prefix_eq_of_nodes_eq G _ (reverse_valid G D hDr.1 u v he hrev) r hnodes
  have hKH : K ∈ H := Finset.mem_filter.mpr ⟨hKF, hcards.trans hDE⟩
  have hscore := hmax K hKH
  rw [hKrev] at hscore
  exact (Nat.not_lt_of_ge hscore)
    (orientationScore_reverse_strict M Y N D hDr.1 hDN u v he hrev hm hl hY)

/-- Auxiliary-table augmentation leaves the union of consistent graphs unchanged. -/
theorem exists_tableCheck_iff_exists_augmented (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (Y : Finset ι × ℕ → ι) (r : WNode ι) (ω : LogSpace S) :
    (∃ D : HLS.WitnessDAG ι,
      RootedCanonical (Shearer.dependencyGraph P.footprint) r D ∧ ω ∈ tableCheck P D) ↔
    (∃ D : HLS.WitnessDAG ι,
      RootedCanonical (Shearer.dependencyGraph P.footprint) r D ∧ AugmentedCheck P M Y r D ω) := by
  constructor
  · rintro ⟨D, hD, hω⟩
    obtain ⟨E, hE, _, haug⟩ := exists_augmented_same_root P M Y r D hD ω hω
    exact ⟨E, hE, haug⟩
  · rintro ⟨D, hD, haug⟩
    exact ⟨D, hD, haug.1⟩

end HLS.WitnessDAG

#check @HLS.WitnessDAG.exists_augmented_same_root
#check @HLS.WitnessDAG.exists_tableCheck_iff_exists_augmented
