/-
  Finite witness DAGs and their ancestor prefixes. Nodes carry their label
  and an occurrence index, so the representation is countable when labels
  are countable. The validity conditions are the standard ones in
  He--Li--Sun, arXiv:2111.06527, Definitions 2.1--2.4.
  https://arxiv.org/abs/2111.06527
-/
module

public import PPGraph.HLS.Encoding.Reversal
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Logic.Equiv.List

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical

namespace HLS

abbrev WNode (ι : Type*) := ι × ℕ

structure WitnessDAG (ι : Type*) where
  nodes : Finset (WNode ι)
  arcs : Finset (WNode ι × WNode ι)

namespace WitnessDAG

variable {ι : Type*} [DecidableEq ι]

instance [Countable ι] : Countable (WitnessDAG ι) :=
  Function.Injective.countable (f := fun D : WitnessDAG ι => (D.nodes, D.arcs)) (by
    intro D E h
    cases D
    cases E
    cases h
    rfl)

def Edge (D : WitnessDAG ι) (u v : WNode ι) : Prop := (u, v) ∈ D.arcs

def Reach (D : WitnessDAG ι) := Relation.ReflTransGen D.Edge

structure Valid (G : SimpleGraph ι) (D : WitnessDAG ι) : Prop where
  supported : ∀ u v, D.Edge u v → u ∈ D.nodes ∧ v ∈ D.nodes
  acyclic : Acyclic D.Edge
  oriented : ∀ u ∈ D.nodes, ∀ v ∈ D.nodes, u ≠ v →
    ((D.Edge u v ∨ D.Edge v u) ↔ (u.1 = v.1 ∨ G.Adj u.1 v.1))

/-- A root reachable from every node is the unique sink of a finite DAG. -/
def Proper (D : WitnessDAG ι) : Prop :=
  ∃ r ∈ D.nodes, ∀ u ∈ D.nodes, D.Reach u r

def Sink (D : WitnessDAG ι) (u : WNode ι) : Prop :=
  u ∈ D.nodes ∧ ∀ v, ¬ D.Edge u v

/-- Canonical indices follow the order within each chain of equal labels. -/
def Canonical (D : WitnessDAG ι) : Prop :=
  (∀ i n, (i, n + 1) ∈ D.nodes → (i, n) ∈ D.nodes) ∧
  ∀ i m n, (i, m) ∈ D.nodes → (i, n) ∈ D.nodes → m < n →
    D.Edge (i, m) (i, n)

theorem edge_ne (G : SimpleGraph ι) (D : WitnessDAG ι) (hD : D.Valid G)
    (u v : WNode ι) (h : D.Edge u v) : u ≠ v := by
  intro huv
  subst v
  exact hD.acyclic.irrefl _ _ h

theorem edge_dependent (G : SimpleGraph ι) (D : WitnessDAG ι) (hD : D.Valid G)
    (u v : WNode ι) (h : D.Edge u v) : u.1 = v.1 ∨ G.Adj u.1 v.1 :=
  (hD.oriented u (hD.supported u v h).1 v (hD.supported u v h).2
    (edge_ne G D hD u v h)).mp (Or.inl h)

theorem transGen_supported (G : SimpleGraph ι) (D : WitnessDAG ι) (hD : D.Valid G)
    (u v : WNode ι) (h : Relation.TransGen D.Edge u v) :
    u ∈ D.nodes ∧ v ∈ D.nodes := by
  induction h with
  | single h => exact hD.supported _ _ h
  | tail _ h ih => exact ⟨ih.1, (hD.supported _ _ h).2⟩

theorem proper_root_sink (G : SimpleGraph ι) (D : WitnessDAG ι) (hD : D.Valid G)
    (r : WNode ι) (hr : r ∈ D.nodes) (hroot : ∀ u ∈ D.nodes, D.Reach u r) :
    D.Sink r := by
  refine ⟨hr, fun v hv => ?_⟩
  have hvr := hroot v (hD.supported r v hv).2
  exact hD.acyclic r ((Relation.TransGen.single hv).trans_left hvr)

theorem sink_eq_root (D : WitnessDAG ι) (r u : WNode ι)
    (hroot : ∀ v ∈ D.nodes, D.Reach v r) (hu : D.Sink u) : u = r := by
  have h := hroot u hu.1
  rcases Relation.ReflTransGen.cases_head h with h | ⟨v, huv, _⟩
  · exact h
  · exact False.elim (hu.2 v huv)

theorem proper_unique_sink (G : SimpleGraph ι) (D : WitnessDAG ι)
    (hD : D.Valid G) (hproper : D.Proper) : ∃! r, D.Sink r := by
  obtain ⟨r, hr, hroot⟩ := hproper
  exact ⟨r, proper_root_sink G D hD r hr hroot,
    fun u hu => sink_eq_root D r u hroot hu⟩

noncomputable def reverse (D : WitnessDAG ι) (u v : WNode ι) : WitnessDAG ι where
  nodes := D.nodes
  arcs := insert (v, u) (D.arcs.erase (u, v))

theorem reverse_edge_iff (D : WitnessDAG ι) (u v x y : WNode ι) :
    (D.reverse u v).Edge x y ↔ reverseArc D.Edge u v x y := by
  simp only [Edge, reverse, Finset.mem_insert, Finset.mem_erase,
    Prod.mk.injEq, reverseArc, addArc, eraseArc]
  simp only [ne_eq, Prod.mk.injEq]
  tauto

/-- Fact 2.6: a reversible arc changes the orientation, preserving the
underlying dependency graph and the witness-DAG conditions. -/
theorem reverse_valid (G : SimpleGraph ι) (D : WitnessDAG ι) (hD : D.Valid G)
    (u v : WNode ι) (hedge : D.Edge u v)
    (hrev : Acyclic (reverseArc D.Edge u v)) : (D.reverse u v).Valid G := by
  have heq : (D.reverse u v).Edge = reverseArc D.Edge u v := by
    funext x y
    exact propext (reverse_edge_iff D u v x y)
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    rw [heq] at hxy
    rcases hxy with ⟨h, _⟩ | ⟨rfl, rfl⟩
    · exact hD.supported _ _ h
    · exact ⟨(hD.supported _ _ hedge).2, (hD.supported _ _ hedge).1⟩
  · rw [heq]
    exact hrev
  · intro x hx y hy hxy
    rw [heq, reverseArc_oriented D.Edge u v x y hedge]
    exact hD.oriented x hx y hy hxy

theorem reverse_canonical (D : WitnessDAG ι) (hD : D.Canonical)
    (u v : WNode ι) (hlabels : u.1 ≠ v.1) : (D.reverse u v).Canonical := by
  refine ⟨hD.1, ?_⟩
  intro i m n hm hn hmn
  apply (reverse_edge_iff D u v _ _).mpr
  apply Or.inl
  refine ⟨hD.2 i m n hm hn hmn, ?_⟩
  rintro ⟨hu, hv⟩
  have hu₁ := congrArg Prod.fst hu
  have hv₁ := congrArg Prod.fst hv
  exact hlabels (hu₁.symm.trans hv₁)

noncomputable def ancestorPrefix (D : WitnessDAG ι) (r : WNode ι) : WitnessDAG ι where
  nodes := D.nodes.filter (fun u => D.Reach u r)
  arcs := D.arcs.filter (fun e => D.Reach e.2 r)

@[simp]
theorem prefix_node_iff (D : WitnessDAG ι) (r u : WNode ι) :
    u ∈ (D.ancestorPrefix r).nodes ↔ u ∈ D.nodes ∧ D.Reach u r := by
  simp [ancestorPrefix]

@[simp]
theorem prefix_edge_iff (D : WitnessDAG ι) (r u v : WNode ι) :
    (D.ancestorPrefix r).Edge u v ↔ D.Edge u v ∧ D.Reach v r := by
  simp [ancestorPrefix, Edge]

theorem reach_prefix (D : WitnessDAG ι) (r u : WNode ι) (h : D.Reach u r) :
    (D.ancestorPrefix r).Reach u r := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head he hp ih =>
    exact ih.head ((prefix_edge_iff D r _ _).mpr ⟨he, hp⟩)

theorem prefix_valid (G : SimpleGraph ι) (D : WitnessDAG ι) (hD : D.Valid G)
    (r : WNode ι) : (D.ancestorPrefix r).Valid G := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v h
    obtain ⟨huv, hvr⟩ := (prefix_edge_iff D r u v).mp h
    obtain ⟨hu, hv⟩ := hD.supported u v huv
    exact ⟨(prefix_node_iff D r u).mpr ⟨hu, hvr.head huv⟩,
      (prefix_node_iff D r v).mpr ⟨hv, hvr⟩⟩
  · exact Acyclic.mono D.Edge _
      (fun u v h => ((prefix_edge_iff D r u v).mp h).1) hD.acyclic
  · intro u hu v hv huv
    obtain ⟨hu, hur⟩ := (prefix_node_iff D r u).mp hu
    obtain ⟨hv, hvr⟩ := (prefix_node_iff D r v).mp hv
    simpa only [prefix_edge_iff, hur, hvr, and_true] using hD.oriented u hu v hv huv

theorem prefix_proper (D : WitnessDAG ι) (r : WNode ι) (hr : r ∈ D.nodes) :
    (D.ancestorPrefix r).Proper := by
  refine ⟨r, (prefix_node_iff D r r).mpr ⟨hr, .refl⟩, ?_⟩
  intro u hu
  exact reach_prefix D r u ((prefix_node_iff D r u).mp hu).2

theorem prefix_canonical (D : WitnessDAG ι) (hD : D.Canonical) (r : WNode ι) :
    (D.ancestorPrefix r).Canonical := by
  constructor
  · intro i n hn
    obtain ⟨hn, hnr⟩ := (prefix_node_iff D r (i, n + 1)).mp hn
    have hn₀ := hD.1 i n hn
    have hedge := hD.2 i n (n + 1) hn₀ hn (Nat.lt_succ_self n)
    exact (prefix_node_iff D r (i, n)).mpr ⟨hn₀, hnr.head hedge⟩
  · intro i m n hm hn hmn
    obtain ⟨hm, _⟩ := (prefix_node_iff D r (i, m)).mp hm
    obtain ⟨hn, hnr⟩ := (prefix_node_iff D r (i, n)).mp hn
    exact (prefix_edge_iff D r _ _).mpr ⟨hD.2 i m n hm hn hmn, hnr⟩

end WitnessDAG
end HLS

#check @HLS.WitnessDAG.edge_ne
#check @HLS.WitnessDAG.edge_dependent
#check @HLS.WitnessDAG.transGen_supported
#check @HLS.WitnessDAG.proper_root_sink
#check @HLS.WitnessDAG.sink_eq_root
#check @HLS.WitnessDAG.proper_unique_sink
#check @HLS.WitnessDAG.reverse_edge_iff
#check @HLS.WitnessDAG.reverse_valid
#check @HLS.WitnessDAG.reverse_canonical
#check @HLS.WitnessDAG.prefix_node_iff
#check @HLS.WitnessDAG.prefix_edge_iff
#check @HLS.WitnessDAG.reach_prefix
#check @HLS.WitnessDAG.prefix_valid
#check @HLS.WitnessDAG.prefix_proper
#check @HLS.WitnessDAG.prefix_canonical
