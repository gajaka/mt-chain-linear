/- Label-preserving finite DAG isomorphisms and canonical names. -/
module

public import PPGraph.HLS.Encoding.Normalization

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [DecidableEq ι]

structure NodeIso (D E : HLS.WitnessDAG ι) where
  map : WNode ι → WNode ι
  injective : Set.InjOn map (↑D.nodes : Set (WNode ι))
  nodes : D.nodes.image map = E.nodes
  label : ∀ u ∈ D.nodes, (map u).1 = u.1
  edge : ∀ u ∈ D.nodes, ∀ v ∈ D.nodes, E.Edge (map u) (map v) ↔ D.Edge u v

theorem NodeIso.map_mem {D E : HLS.WitnessDAG ι} (f : NodeIso D E)
    (u : WNode ι) (hu : u ∈ D.nodes) : f.map u ∈ E.nodes := by
  rw [← f.nodes]
  exact Finset.mem_image.mpr ⟨u, hu, rfl⟩

theorem NodeIso.labelPrior_image {D E : HLS.WitnessDAG ι} (f : NodeIso D E)
    (u : WNode ι) (hu : u ∈ D.nodes) :
    (D.labelPrior u).image f.map = E.labelPrior (f.map u) := by
  ext w
  constructor
  · rintro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hv, hl, he⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨f.map_mem v hv,
      (f.label v hv).trans (hl.trans (f.label u hu).symm), (f.edge v hv u hu).mpr he⟩
  · intro hw
    obtain ⟨hw, hl, he⟩ := Finset.mem_filter.mp hw
    rw [← f.nodes] at hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv,
      (f.label v hv).symm.trans (hl.trans (f.label u hu)), (f.edge v hv u hu).mp he⟩, rfl⟩

theorem NodeIso.canonicalName_map {D E : HLS.WitnessDAG ι} (f : NodeIso D E)
    (u : WNode ι) (hu : u ∈ D.nodes) : E.canonicalName (f.map u) = D.canonicalName u := by
  apply Prod.ext
  · exact f.label u hu
  · change (E.labelPrior (f.map u)).card = (D.labelPrior u).card
    rw [← f.labelPrior_image u hu, Finset.card_image_of_injOn]
    exact f.injective.mono (by intro w hw; exact (Finset.mem_filter.mp hw).1)

theorem NodeIso.map_eq_of_canonical {D E : HLS.WitnessDAG ι} (f : NodeIso D E)
    (G : SimpleGraph ι) (hD : D.Valid G) (hE : E.Valid G)
    (hcD : D.Canonical) (hcE : E.Canonical) (u : WNode ι) (hu : u ∈ D.nodes) : f.map u = u := by
  have h := f.canonicalName_map u hu
  rwa [canonicalName_eq_of_canonical G E hE hcE _ (f.map_mem u hu),
    canonicalName_eq_of_canonical G D hD hcD u hu] at h

theorem NodeIso.eq_of_canonical {D E : HLS.WitnessDAG ι} (f : NodeIso D E)
    (G : SimpleGraph ι) (hD : D.Valid G) (hE : E.Valid G)
    (hcD : D.Canonical) (hcE : E.Canonical) : D = E := by
  have hn : D.nodes = E.nodes := by
    calc
      D.nodes = D.nodes.image f.map := by
        ext u
        constructor
        · intro hu
          exact Finset.mem_image.mpr ⟨u, hu, f.map_eq_of_canonical G hD hE hcD hcE u hu⟩
        · intro hu
          obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp hu
          rw [f.map_eq_of_canonical G hD hE hcD hcE v hv] at hvu
          exact hvu ▸ hv
      _ = E.nodes := f.nodes
  have ha : D.arcs = E.arcs := by
    ext e
    constructor
    · intro he
      obtain ⟨hu, hv⟩ := hD.supported e.1 e.2 he
      have he' := (f.edge e.1 hu e.2 hv).mpr he
      rwa [f.map_eq_of_canonical G hD hE hcD hcE e.1 hu,
        f.map_eq_of_canonical G hD hE hcD hcE e.2 hv] at he'
    · intro he
      obtain ⟨hu, hv⟩ := hE.supported e.1 e.2 he
      rw [← hn] at hu hv
      apply (f.edge e.1 hu e.2 hv).mp
      rw [f.map_eq_of_canonical G hD hE hcD hcE e.1 hu,
        f.map_eq_of_canonical G hD hE hcD hcE e.2 hv]
      exact he
  cases D
  cases E
  simp_all

end HLS.WitnessDAG

#check @HLS.WitnessDAG.NodeIso.map_mem
#check @HLS.WitnessDAG.NodeIso.labelPrior_image
#check @HLS.WitnessDAG.NodeIso.canonicalName_map
#check @HLS.WitnessDAG.NodeIso.map_eq_of_canonical
#check @HLS.WitnessDAG.NodeIso.eq_of_canonical
