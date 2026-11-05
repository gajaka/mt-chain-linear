/-
  The depth labels of a real Moser--Tardos witness form a proper stable
  sequence. Same-depth independence makes each layer an independent set;
  parent-child compatibility gives the closed-neighborhood transition.
-/
module

public import PPGraph.Shearer.Stable
public import PPGraph.Shearer.BDD
public import PPGraph.MoserTardos.Witness.LabelsAtDepthBridge

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace Shearer

variable {ι : Type} [DecidableEq ι]

/-- The distinct event labels at one address depth. -/
noncomputable def treeLayer (T : GrowingTree ι) (d : ℕ) : Finset ι :=
  (T.dom.filter (fun w => w.length = d)).image T.lab

/-- The greatest address depth, with zero as the value for an empty domain. -/
def treeDepth (T : GrowingTree ι) : ℕ := T.dom.sup List.length

/-- Root-first layers, ending at the last nonempty depth of a valid tree. -/
noncomputable def treeLayers (T : GrowingTree ι) : List (Finset ι) :=
  (List.range (treeDepth T + 1)).map (treeLayer T)

@[simp]
theorem mem_treeLayer (T : GrowingTree ι) (d : ℕ) (a : ι) :
    a ∈ treeLayer T d ↔ ∃ w ∈ T.dom, w.length = d ∧ T.lab w = a := by
  simp only [treeLayer, Finset.mem_image, Finset.mem_filter]
  aesop

theorem treeLayer_zero (T : GrowingTree ι) (hT : T.Valid) :
    treeLayer T 0 = {T.lab []} := by
  ext a
  rw [mem_treeLayer, Finset.mem_singleton]
  constructor
  · rintro ⟨w, _, hw, hwa⟩
    have hw0 : w = [] := List.length_eq_zero_iff.mp hw
    simpa [hw0] using hwa.symm
  · intro ha
    exact ⟨[], hT.1, rfl, ha.symm⟩

theorem length_le_treeDepth (T : GrowingTree ι) (w : List ℕ) (hw : w ∈ T.dom) :
    w.length ≤ treeDepth T := Finset.le_sup hw

theorem treeLayer_eq_empty_of_depth_lt (T : GrowingTree ι) (d : ℕ)
    (hd : treeDepth T < d) : treeLayer T d = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨w, hw, hwd, _⟩ := (mem_treeLayer T d a).mp ha
  have := length_le_treeDepth T w hw
  omega

theorem treeLayer_nonempty (T : GrowingTree ι) (hT : T.Valid) (d : ℕ)
    (hd : d ≤ treeDepth T) : (treeLayer T d).Nonempty := by
  obtain ⟨w, hw, hmax⟩ := Finset.exists_mem_eq_sup T.dom ⟨[], hT.1⟩ List.length
  have hdw : d ≤ w.length := by simpa only [treeDepth, hmax] using hd
  have htake : w.take d ∈ T.dom :=
    GrowingTree.Valid.prefix_mem T hT w hw (w.take d) (List.take_prefix d w)
  exact ⟨T.lab (w.take d), (mem_treeLayer T d _).mpr
    ⟨w.take d, htake, by simp [List.length_take, Nat.min_eq_left hdw], rfl⟩⟩

theorem treeLayers_nonempty_layers (T : GrowingTree ι) (hT : T.Valid) :
    ∀ J ∈ treeLayers T, J ≠ ∅ := by
  intro J hJ
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hJ
  have hd' := List.mem_range.mp hd
  exact (treeLayer_nonempty T hT d (by omega)).ne_empty

variable {V : Type} [DecidableEq V] {S : VarSpaces V}

theorem dependencyGraph_adj_neighbor (P : MTProcess S ι) (a b : ι) :
    (dependencyGraph P.footprint).Adj a b ↔ a ≠ b ∧ neighbor P a b := by
  rw [dependencyGraph_adj_iff]
  simp only [dependent, neighbor, Finset.not_disjoint_iff_nonempty_inter]

theorem treeLayer_independent (P : MTProcess S ι) (T : GrowingTree ι)
    (hSDI : SameDepthIndependent P T) (d : ℕ) :
    Independent (dependencyGraph P.footprint) (treeLayer T d) := by
  intro a ha b hb hadj
  obtain ⟨w, hw, hwd, hwa⟩ := (mem_treeLayer T d a).mp ha
  obtain ⟨v, hv, hvd, hvb⟩ := (mem_treeLayer T d b).mp hb
  obtain ⟨hne, hn⟩ := (dependencyGraph_adj_neighbor P a b).mp hadj
  have hwv : w ≠ v := by
    intro heq
    exact hne (hwa.symm.trans (heq ▸ hvb))
  exact (hSDI w v hw hv (hwd.trans hvd.symm) hwv).2 (by simpa [hwa, hvb] using hn)

theorem treeLayer_succ_subset_closed [Fintype ι] (P : MTProcess S ι)
    (T : GrowingTree ι) (hT : T.Valid)
    (hwf : ∀ u k, u ∈ T.dom → u ++ [k] ∈ T.dom →
      T.lab u = T.lab (u ++ [k]) ∨ neighbor P (T.lab u) (T.lab (u ++ [k])))
    (d : ℕ) :
    treeLayer T (d + 1) ⊆ closed (dependencyGraph P.footprint) Finset.univ (treeLayer T d) := by
  intro a ha
  obtain ⟨w, hw, hwd, hwa⟩ := (mem_treeLayer T (d + 1) a).mp ha
  have hwne : w ≠ [] := by intro h; simp [h] at hwd
  let u := w.dropLast
  let k := w.getLast hwne
  have huk : u ++ [k] = w := List.dropLast_append_getLast hwne
  have hchild : u ++ [k] ∈ T.dom := huk.symm ▸ hw
  have hu : u ∈ T.dom := hT.2 u k hchild
  have hud : u.length = d := by
    have hlen := congrArg List.length huk
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  have hulayer : T.lab u ∈ treeLayer T d := (mem_treeLayer T d _).mpr ⟨u, hu, hud, rfl⟩
  have hcompat := hwf u k hu hchild
  rw [huk, hwa] at hcompat
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases eq_or_ne (T.lab u) a with heq | hne
  · exact Or.inl (heq ▸ hulayer)
  · refine Or.inr ⟨T.lab u, hulayer, (dependencyGraph_adj_neighbor P _ _).mpr ⟨hne, ?_⟩⟩
    exact hcompat.resolve_left hne

theorem treeLayer_succ_mem_successors [Fintype ι] (P : MTProcess S ι)
    (T : GrowingTree ι) (hT : T.Valid) (hSDI : SameDepthIndependent P T)
    (hwf : ∀ u k, u ∈ T.dom → u ++ [k] ∈ T.dom →
      T.lab u = T.lab (u ++ [k]) ∨ neighbor P (T.lab u) (T.lab (u ++ [k])))
    (d : ℕ) :
    treeLayer T (d + 1) ∈ successors (dependencyGraph P.footprint) Finset.univ (treeLayer T d) :=
  (mem_successors _ _ _ _).mpr ⟨treeLayer_succ_subset_closed P T hT hwf d,
    treeLayer_independent P T hSDI (d + 1)⟩

theorem layer_window_mem_stableSequences (G : SimpleGraph ι) (B : Finset ι)
    (f : ℕ → Finset ι) (hnext : ∀ d, f (d + 1) ∈ successors G B (f d)) :
    ∀ n d, ((List.range (n + 1)).map (fun k => f (d + k))) ∈ stableSequences G B n (f d) := by
  intro n
  induction n with
  | zero => intro d; simp [stableSequences]
  | succ n ih =>
    intro d
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.add_zero]
    apply Finset.mem_biUnion.mpr
    refine ⟨f (d + 1), hnext d, Finset.mem_image.mpr ⟨_, ih (d + 1), ?_⟩⟩
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    congr 1
    omega

/-- Real witness trees have proper stable depth sequences rooted at their event label. -/
theorem treeLayers_mem_properFamily [Fintype ι] (P : MTProcess S ι)
    (C : ℕ → ι) (t : ℕ) :
    treeLayers (τC P C t) ∈
      properFamily (dependencyGraph P.footprint) Finset.univ {C t} := by
  have hT := τC_valid P C t
  have hSDI := τBuild_sameDepthIndependent P C t (t - 1)
  have hnext := treeLayer_succ_mem_successors P (τC P C t) hT hSDI
    (τC_child_wellformed P C t)
  refine ⟨⟨treeDepth (τC P C t), ?_⟩, treeLayers_nonempty_layers _ hT⟩
  have h := layer_window_mem_stableSequences (dependencyGraph P.footprint) Finset.univ
    (treeLayer (τC P C t)) hnext (treeDepth (τC P C t)) 0
  simpa only [Nat.zero_add, treeLayers, treeLayer_zero _ hT, τC_root_label] using h

end Shearer

#check @Shearer.mem_treeLayer
#check @Shearer.treeLayer_zero
#check @Shearer.length_le_treeDepth
#check @Shearer.treeLayer_eq_empty_of_depth_lt
#check @Shearer.treeLayer_nonempty
#check @Shearer.treeLayers_nonempty_layers
#check @Shearer.dependencyGraph_adj_neighbor
#check @Shearer.treeLayer_independent
#check @Shearer.treeLayer_succ_subset_closed
#check @Shearer.treeLayer_succ_mem_successors
#check @Shearer.layer_window_mem_stableSequences
#check @Shearer.treeLayers_mem_properFamily
