/-
  Resampling-table consistency for finite witness DAGs. Every node reads
  one table entry for each variable in its event footprint. Direct
  predecessor counts order all nodes sharing a variable; hence different
  nodes read disjoint coordinate blocks and the ordinary DAG-check
  probability factors. Intersection-sensitive augmentation is separate.
  Source: He--Li--Sun, arXiv:2111.06527, Section 3.1.
-/
module

public import PPGraph.HLS.DAG.WitnessDAG
public import PPGraph.Shearer.BDD
public import PPGraph.MoserTardos.Probability.Probability

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory

namespace HLS.WitnessDAG

variable {V : Type} [DecidableEq V] {S : VarSpaces V}
    {ι : Type} [DecidableEq ι]

theorem edge_of_transGen_dependent (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u v : WNode ι) (hp : Relation.TransGen D.Edge u v)
    (hdep : u.1 = v.1 ∨ G.Adj u.1 v.1) : D.Edge u v := by
  obtain ⟨hu, hv⟩ := transGen_supported G D hD u v hp
  have huv : u ≠ v := by
    rintro rfl
    exact hD.acyclic u hp
  rcases (hD.oriented u hu v hv huv).mpr hdep with h | h
  · exact h
  · exact False.elim (hD.acyclic u (hp.tail h))

theorem dependent_of_shared_variable (P : MTProcess S ι) (u v : WNode ι)
    (a : V) (hu : a ∈ P.footprint u.1) (hv : a ∈ P.footprint v.1) :
    u.1 = v.1 ∨ (Shearer.dependencyGraph P.footprint).Adj u.1 v.1 := by
  by_cases h : u.1 = v.1
  · exact Or.inl h
  · exact Or.inr ((Shearer.dependencyGraph_adj_iff P.footprint u.1 v.1).mpr
      ⟨h, ⟨a, Finset.mem_inter.mpr ⟨hu, hv⟩⟩⟩)

noncomputable def priorReaders (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (u : WNode ι) (a : V) : Finset (WNode ι) :=
  D.nodes.filter (fun w => D.Edge w u ∧ a ∈ P.footprint w.1)

noncomputable def localIndex (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (u : WNode ι) (a : V) : ℕ := (priorReaders P D u a).card

theorem priorReaders_strict_of_edge (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (huv : D.Edge u v) (a : V)
    (hu : a ∈ P.footprint u.1) (hv : a ∈ P.footprint v.1) :
    priorReaders P D u a ⊂ priorReaders P D v a := by
  have hsub : priorReaders P D u a ⊆ priorReaders P D v a := by
    intro w hw
    obtain ⟨hw, hwu, hwa⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hw,
      edge_of_transGen_dependent _ D hD w v ((Relation.TransGen.single hwu).tail huv)
        (dependent_of_shared_variable P w v a hwa hv), hwa⟩
  apply lt_of_le_of_ne hsub
  intro heq
  have huin : u ∈ priorReaders P D v a :=
    Finset.mem_filter.mpr ⟨(hD.supported u v huv).1, huv, hu⟩
  have hself := (Finset.mem_filter.mp (heq.symm ▸ huin)).2.1
  exact hD.acyclic.irrefl _ u hself

theorem localIndex_lt_of_edge (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (huv : D.Edge u v) (a : V)
    (hu : a ∈ P.footprint u.1) (hv : a ∈ P.footprint v.1) :
    localIndex P D u a < localIndex P D v a :=
  Finset.card_lt_card (priorReaders_strict_of_edge P D hD u v huv a hu hv)

noncomputable def tableCoordinates (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (u : WNode ι) : Finset (ℕ × V) :=
  (P.footprint u.1).image (fun a => (localIndex P D u a, a))

theorem tableCoordinates_disjoint (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (hu : u ∈ D.nodes) (hv : v ∈ D.nodes) (hne : u ≠ v) :
    Disjoint (tableCoordinates P D u) (tableCoordinates P D v) := by
  apply Finset.disjoint_left.mpr
  intro p hp₁ hp₂
  obtain ⟨a, ha, hap⟩ := Finset.mem_image.mp hp₁
  obtain ⟨b, hb, hbp⟩ := Finset.mem_image.mp hp₂
  have hab : a = b := congrArg Prod.snd (hap.trans hbp.symm)
  subst b
  have hind : localIndex P D u a = localIndex P D v a :=
    congrArg Prod.fst (hap.trans hbp.symm)
  rcases (hD.oriented u hu v hv hne).mpr (dependent_of_shared_variable P u v a ha hb)
      with huv | hvu
  · have h := localIndex_lt_of_edge P D hD u v huv a ha hb
    omega
  · have h := localIndex_lt_of_edge P D hD v u hvu a hb ha
    omega

noncomputable def tableState (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (ω : LogSpace S) (u : WNode ι) : MTState S := readAt (localIndex P D u) ω

noncomputable def tableEvent (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (u : WNode ι) : Set (LogSpace S) := {ω | tableState P D ω u ∈ P.bad u.1}

noncomputable def tableCheck (P : MTProcess S ι) (D : HLS.WitnessDAG ι) :
    Set (LogSpace S) := ⋂ u ∈ D.nodes, tableEvent P D u

theorem measurable_tableState (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (u : WNode ι) : Measurable (fun ω => tableState P D ω u) :=
  measurable_readAt _

theorem measurableSet_tableEvent (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (u : WNode ι) :
    MeasurableSet (tableEvent P D u) := (hbad u.1).preimage (measurable_tableState P D u)

theorem tableEvent_depends_on_coordinates (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (u : WNode ι) (ω ω' : LogSpace S)
    (h : ∀ a ∈ tableCoordinates P D u, ω a = ω' a) :
    ω ∈ tableEvent P D u ↔ ω' ∈ tableEvent P D u := by
  apply P.dep u.1
  intro a ha
  exact h _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

theorem logMeasure_tableEvent_eq_pi [Fintype V] (P : MTProcess S ι)
    (D : HLS.WitnessDAG ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (u : WNode ι) :
    logMeasure S (tableEvent P D u) = Measure.pi (fun a => S.measure a) (P.bad u.1) := by
  rw [← logMeasure_map_readAt_eq_pi (S := S) (localIndex P D u),
    Measure.map_apply (measurable_readAt _) (hbad u.1)]
  rfl

theorem measurableSet_tableCheck (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) : MeasurableSet (tableCheck P D) := by
  exact Finset.measurableSet_biInter D.nodes
    (fun u _ => measurableSet_tableEvent P D hbad u)

/-- The ordinary product bound for a witness DAG is an exact equality. -/
theorem logMeasure_tableCheck_eq_prod [Fintype V] (P : MTProcess S ι)
    (D : HLS.WitnessDAG ι) (hD : D.Valid (Shearer.dependencyGraph P.footprint))
    (hbad : ∀ i, MeasurableSet (P.bad i)) :
    logMeasure S (tableCheck P D) =
      ∏ u ∈ D.nodes, Measure.pi (fun a => S.measure a) (P.bad u.1) := by
  have : ∀ a, IsProbabilityMeasure (μCoin S a) := fun a => S.isProb a.2
  have hd : (↑D.nodes : Set (WNode ι)).PairwiseDisjoint (tableCoordinates P D) :=
    fun u hu v hv hne => tableCoordinates_disjoint P D hD u v hu hv hne
  calc
    logMeasure S (tableCheck P D) = ∏ u ∈ D.nodes, logMeasure S (tableEvent P D u) :=
      infinitePi_iInter_eq_prod_of_dependsOn (μCoin S) D.nodes
        (tableCoordinates P D) (tableEvent P D) hd
          (fun u _ ω ω' h => tableEvent_depends_on_coordinates P D u ω ω' h)
          (fun u _ => measurableSet_tableEvent P D hbad u)
    _ = _ := Finset.prod_congr rfl (fun u _ => logMeasure_tableEvent_eq_pi P D hbad u)

end HLS.WitnessDAG

#check @HLS.WitnessDAG.edge_of_transGen_dependent
#check @HLS.WitnessDAG.dependent_of_shared_variable
#check @HLS.WitnessDAG.priorReaders_strict_of_edge
#check @HLS.WitnessDAG.localIndex_lt_of_edge
#check @HLS.WitnessDAG.tableCoordinates_disjoint
#check @HLS.WitnessDAG.measurable_tableState
#check @HLS.WitnessDAG.measurableSet_tableEvent
#check @HLS.WitnessDAG.tableEvent_depends_on_coordinates
#check @HLS.WitnessDAG.logMeasure_tableEvent_eq_pi
#check @HLS.WitnessDAG.measurableSet_tableCheck
#check @HLS.WitnessDAG.logMeasure_tableCheck_eq_prod
