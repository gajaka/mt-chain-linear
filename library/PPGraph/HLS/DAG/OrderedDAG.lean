/- Finite labeled DAGs obtained from a strict total order of their vertices. -/
module

public import PPGraph.HLS.DAG.WitnessDAG

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.OrderedDAG

variable {ι A : Type} [DecidableEq ι] [DecidableEq A]

def embed (label : A → ι) (tag : A → ℕ) (a : A) : WNode ι := (label a, tag a)

noncomputable def build (G : SimpleGraph ι) (s : Finset A) (label : A → ι) (tag : A → ℕ)
    (before : A → A → Prop) : WitnessDAG ι where
  nodes := s.image (embed label tag)
  arcs := ((s ×ˢ s).filter (fun e => before e.1 e.2 ∧
    (label e.1 = label e.2 ∨ G.Adj (label e.1) (label e.2)))).image
      (fun e => (embed label tag e.1, embed label tag e.2))

theorem node_iff (G : SimpleGraph ι) (s : Finset A) (label : A → ι) (tag : A → ℕ)
    (before : A → A → Prop) (u : WNode ι) :
    u ∈ (build G s label tag before).nodes ↔ ∃ a ∈ s, embed label tag a = u :=
  Finset.mem_image

theorem edge_witness (G : SimpleGraph ι) (s : Finset A) (label : A → ι) (tag : A → ℕ)
    (before : A → A → Prop) (u v : WNode ι) :
    (build G s label tag before).Edge u v ↔
      ∃ a ∈ s, ∃ b ∈ s, embed label tag a = u ∧ embed label tag b = v ∧
        before a b ∧ (label a = label b ∨ G.Adj (label a) (label b)) := by
  constructor
  · intro he
    obtain ⟨e, he, heu⟩ := Finset.mem_image.mp he
    obtain ⟨hemem, hab, hdep⟩ := Finset.mem_filter.mp he
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hemem
    exact ⟨e.1, ha, e.2, hb, congrArg Prod.fst heu, congrArg Prod.snd heu, hab, hdep⟩
  · rintro ⟨a, ha, b, hb, hau, hbv, hab, hdep⟩
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab, hdep⟩, Prod.ext hau hbv⟩

theorem edge_embed (G : SimpleGraph ι) (s : Finset A) (label : A → ι) (tag : A → ℕ)
    (before : A → A → Prop) (hinj : Set.InjOn (embed label tag) (↑s : Set A))
    (a b : A) (ha : a ∈ s) (hb : b ∈ s) :
    (build G s label tag before).Edge (embed label tag a) (embed label tag b) ↔
      before a b ∧ (label a = label b ∨ G.Adj (label a) (label b)) := by
  constructor
  · intro he
    obtain ⟨x, hx, y, hy, hxa, hyb, hxy, hdep⟩ := (edge_witness G s label tag before _ _).mp he
    have hxa' := hinj hx ha hxa
    have hyb' := hinj hy hb hyb
    simpa only [hxa', hyb'] using And.intro hxy hdep
  · rintro ⟨hab, hdep⟩
    exact (edge_witness G s label tag before _ _).mpr ⟨a, ha, b, hb, rfl, rfl, hab, hdep⟩

theorem transGen_order (G : SimpleGraph ι) (s : Finset A) (label : A → ι) (tag : A → ℕ)
    (before : A → A → Prop) (hinj : Set.InjOn (embed label tag) (↑s : Set A))
    (htrans : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, before a b → before b c → before a c)
    (u v : WNode ι) (h : Relation.TransGen (build G s label tag before).Edge u v) :
    ∃ a ∈ s, ∃ b ∈ s, embed label tag a = u ∧ embed label tag b = v ∧ before a b := by
  induction h with
  | single h =>
    obtain ⟨a, ha, b, hb, hau, hbv, hab, _⟩ := (edge_witness G s label tag before _ _).mp h
    exact ⟨a, ha, b, hb, hau, hbv, hab⟩
  | tail _ he ih =>
    obtain ⟨a, ha, b, hb, hau, hbv, hab⟩ := ih
    obtain ⟨c, hc, d, hd, hcv, hdz, hcd, _⟩ := (edge_witness G s label tag before _ _).mp he
    have hbc : b = c := hinj hb hc (hbv.trans hcv.symm)
    subst c
    exact ⟨a, ha, d, hd, hau, hdz, htrans a ha b hb d hd hab hcd⟩

theorem valid (G : SimpleGraph ι) (s : Finset A) (label : A → ι) (tag : A → ℕ)
    (before : A → A → Prop) (hinj : Set.InjOn (embed label tag) (↑s : Set A))
    (hirr : ∀ a ∈ s, ¬ before a a)
    (htrans : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, before a b → before b c → before a c)
    (htotal : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → before a b ∨ before b a) :
    (build G s label tag before).Valid G := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v he
    obtain ⟨a, ha, b, hb, hau, hbv, _, _⟩ := (edge_witness G s label tag before u v).mp he
    exact ⟨(node_iff G s label tag before u).mpr ⟨a, ha, hau⟩,
      (node_iff G s label tag before v).mpr ⟨b, hb, hbv⟩⟩
  · intro u hcycle
    obtain ⟨a, ha, b, hb, hau, hbu, hab⟩ := transGen_order G s label tag before hinj htrans u u hcycle
    have hab' : a = b := hinj ha hb (hau.trans hbu.symm)
    exact hirr a ha (hab' ▸ hab)
  · intro u hu v hv hne
    obtain ⟨a, ha, hau⟩ := (node_iff G s label tag before u).mp hu
    obtain ⟨b, hb, hbv⟩ := (node_iff G s label tag before v).mp hv
    subst u
    subst v
    have hab : a ≠ b := by intro h; exact hne (congrArg (embed label tag) h)
    rw [edge_embed G s label tag before hinj a b ha hb,
      edge_embed G s label tag before hinj b a hb ha]
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩)
      · exact h
      · exact h.imp Eq.symm (fun h => G.adj_symm h)
    · intro hdep
      rcases htotal a ha b hb hab with h | h
      · exact Or.inl ⟨h, hdep⟩
      · exact Or.inr ⟨h, hdep.imp Eq.symm (fun h => G.adj_symm h)⟩

end HLS.OrderedDAG

#check @HLS.OrderedDAG.node_iff
#check @HLS.OrderedDAG.edge_witness
#check @HLS.OrderedDAG.edge_embed
#check @HLS.OrderedDAG.transGen_order
#check @HLS.OrderedDAG.valid
