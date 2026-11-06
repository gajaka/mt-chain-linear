/-
  PPGraphShearerSequenceProbability.lean

  The checking event depends only on the sequence of depth-label sets,
  not on the parent relation of a witness tree. Same-depth independence
  makes (depth, label) injective on nodes, so those sets retain exactly
  the multiplicities needed by every localCount.

  Source: Vondrak, MATH233A lecture 7, Lemma 7.5, and Harvey--Vondrak,
  "An Algorithmic Proof of the Lovasz Local Lemma via Resampling Oracles",
  arXiv:1504.02044. A fixed representative will bound an entire occurring
  sequence class without summing over tree shapes or assuming their injectivity.
-/

module

public import PPGraph.MoserTardos.Probability.ProbabilityGeneral
public import PPGraph.MoserTardos.Probability.OccurrenceProbability
public import PPGraph.Shearer.Occurrence

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory
open scoped ENNReal

namespace Shearer

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type} [DecidableEq ι]

/-- The finite set of (depth, label) pairs is determined by all depth layers. -/
theorem depthLabelProfile_eq_of_layer_labels_eq (T U : GrowingTree ι)
    (hlayers : ∀ d, (T.dom.filter (fun w => w.length = d)).image T.lab =
      (U.dom.filter (fun w => w.length = d)).image U.lab) :
    T.dom.image (fun w => (w.length, T.lab w)) =
      U.dom.image (fun w => (w.length, U.lab w)) := by
  have hmem (T : GrowingTree ι) (d : ℕ) (a : ι) :
      (d, a) ∈ T.dom.image (fun w => (w.length, T.lab w)) ↔
        a ∈ (T.dom.filter (fun w => w.length = d)).image T.lab := by
    constructor
    · intro h
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp h
      obtain ⟨hd, ha⟩ := Prod.mk.inj heq
      exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hd⟩, ha⟩
    · intro h
      obtain ⟨w, hw, ha⟩ := Finset.mem_image.mp h
      obtain ⟨hw, hd⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_image.mpr ⟨w, hw, Prod.ext hd ha⟩
  ext ⟨d, a⟩
  rw [hmem, hmem, hlayers d]

#check @depthLabelProfile_eq_of_layer_labels_eq

/-- On a same-depth-independent tree, counting nodes selected by a predicate
on depth and label is the same as counting their distinct profile pairs. -/
theorem card_filter_eq_card_depthLabelProfile (P : MTProcess S ι)
    (T : GrowingTree ι) (hSDI : SameDepthIndependent P T)
    (pred : ℕ → ι → Prop) :
    (T.dom.filter (fun w => pred w.length (T.lab w))).card =
      ((T.dom.image (fun w => (w.length, T.lab w))).filter
        (fun z => pred z.1 z.2)).card := by
  classical
  have himage : (T.dom.filter (fun w => pred w.length (T.lab w))).image
        (fun w => (w.length, T.lab w)) =
      (T.dom.image (fun w => (w.length, T.lab w))).filter
        (fun z => pred z.1 z.2) := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hw, hp⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨w, hw, rfl⟩, hp⟩
    · intro hz
      obtain ⟨hz, hp⟩ := Finset.mem_filter.mp hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hp⟩, rfl⟩
  rw [← himage]
  symm
  apply Finset.card_image_of_injOn
  intro w hw u hu heq
  by_contra hne
  obtain ⟨hd, ha⟩ := Prod.mk.inj heq
  exact (hSDI w u (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hu).1 hd hne).1 ha

#check @card_filter_eq_card_depthLabelProfile

/-- The check's sample index is determined by the depth layers and node depth. -/
theorem localCount_eq_of_layer_labels_eq (P : MTProcess S ι)
    (T U : GrowingTree ι) (hT : SameDepthIndependent P T)
    (hU : SameDepthIndependent P U)
    (hlayers : ∀ d, (T.dom.filter (fun w => w.length = d)).image T.lab =
      (U.dom.filter (fun w => w.length = d)).image U.lab)
    (w u : List ℕ) (hdepth : w.length = u.length) (v : V) :
    localCount P T w v = localCount P U u v := by
  have hcount (T : GrowingTree ι) (hT : SameDepthIndependent P T) (w : List ℕ) :
      localCount P T w v =
        ((T.dom.image (fun u => (u.length, T.lab u))).filter
          (fun z => w.length < z.1 ∧ v ∈ P.footprint z.2)).card := by
    convert card_filter_eq_card_depthLabelProfile P T hT
      (fun d a => w.length < d ∧ v ∈ P.footprint a) using 1
    · unfold localCount
      congr 1
      ext x
      simp
    · congr 1
      ext x
      simp
  rw [hcount T hT w, hcount U hU u,
    depthLabelProfile_eq_of_layer_labels_eq T U hlayers, hdepth]

#check @localCount_eq_of_layer_labels_eq

/-- Equal depth-label layers give the same tau-check on every fixed log.
No equality or injectivity of the underlying tree shapes is asserted. -/
theorem τCheck_congr_of_layer_labels_eq (P : MTProcess S ι)
    (T U : GrowingTree ι) (hT : SameDepthIndependent P T)
    (hU : SameDepthIndependent P U)
    (hlayers : ∀ d, (T.dom.filter (fun w => w.length = d)).image T.lab =
      (U.dom.filter (fun w => w.length = d)).image U.lab)
    (ω : LogSpace S) : τCheck P T ω ↔ τCheck P U ω := by
  have transfer (T U : GrowingTree ι) (hT : SameDepthIndependent P T)
      (hU : SameDepthIndependent P U)
      (hlayers : ∀ d, (T.dom.filter (fun w => w.length = d)).image T.lab =
        (U.dom.filter (fun w => w.length = d)).image U.lab)
      (hcheck : τCheck P T ω) : τCheck P U ω := by
    intro u hu
    have hulab : U.lab u ∈ (U.dom.filter (fun w => w.length = u.length)).image U.lab :=
      Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, rfl⟩, rfl⟩
    rw [← hlayers u.length] at hulab
    obtain ⟨w, hw, hlabel⟩ := Finset.mem_image.mp hulab
    obtain ⟨hw, hdepth⟩ := Finset.mem_filter.mp hw
    have hstate : checkState P T ω w = checkState P U ω u := by
      funext v
      show atIdx ω v (localCount P T w v) = atIdx ω v (localCount P U u v)
      rw [localCount_eq_of_layer_labels_eq P T U hT hU hlayers w u hdepth v]
    have h := hcheck w hw
    rwa [hstate, hlabel] at h
  exact ⟨transfer T U hT hU hlayers, transfer U T hU hT (fun d => (hlayers d).symm)⟩

#check @τCheck_congr_of_layer_labels_eq

/-- The list of depth-label sets determines the tau-check. -/
theorem τCheck_congr_of_treeLayers_eq (P : MTProcess S ι)
    (T U : GrowingTree ι) (hT : SameDepthIndependent P T)
    (hU : SameDepthIndependent P U) (hlayers : treeLayers T = treeLayers U)
    (ω : LogSpace S) : τCheck P T ω ↔ τCheck P U ω :=
  τCheck_congr_of_layer_labels_eq P T U hT hU
    (fun d => treeLayers_eq_imp_layer_eq T U hlayers d) ω

#check @τCheck_congr_of_treeLayers_eq

variable [Fintype ι] [Nonempty ι]

/-- Fix one raw witness with the prescribed layer sequence. Every occurrence
of that sequence passes this same fixed representative's check on its own log. -/
theorem sequenceOccurrence_subset_τCheck_of_representative (P : MTProcess S ι)
    (α : ι) (L : List (Finset ι)) (ωrep : LogSpace S) (srep : ℕ)
    (hrep : randomInitSequence P ωrep srep = L) :
    sequenceOccurrence P α L ⊆
      {ω | τCheck P
        (τC P (shiftedC P (initialStateFromLog ωrep) ωrep) (srep + 1)) ω} := by
  intro ω hω
  obtain ⟨s, hs, hseq⟩ := hω
  have hpass := τCheck_holds_of_randomInit_trajectory P ω (s + 1) (by omega) hs.1
  have hlayers :
      treeLayers (τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)) =
        treeLayers (τC P (shiftedC P (initialStateFromLog ωrep) ωrep) (srep + 1)) :=
    hseq.trans hrep.symm
  exact (τCheck_congr_of_treeLayers_eq P _ _
    (τBuild_sameDepthIndependent P (shiftedC P (initialStateFromLog ω) ω)
      (s + 1) ((s + 1) - 1))
    (τBuild_sameDepthIndependent P (shiftedC P (initialStateFromLog ωrep) ωrep)
      (srep + 1) ((srep + 1) - 1)) hlayers ω).mp hpass

#check @sequenceOccurrence_subset_τCheck_of_representative

/-- Layering preserves the product of node probabilities, including all
occurrences of one label at different depths. -/
theorem randomInitSequence_weight_eq_prod (P : MTProcess S ι) (p : ι → ℝ)
    (ω : LogSpace S) (s : ℕ) :
    sequenceWeight p (randomInitSequence P ω s) =
      ∏ w ∈ (τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)).dom,
        p ((τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)).lab w) :=
  sequenceWeight_treeLayers P _
    (τBuild_sameDepthIndependent P (shiftedC P (initialStateFromLog ω) ω)
      (s + 1) ((s + 1) - 1)) p

#check @randomInitSequence_weight_eq_prod

/-- One representative bounds the probability of an entire stable-sequence
occurrence class. There is no union bound over the tree shapes in that class. -/
theorem logMeasure_sequenceOccurrence_le_sequenceWeight [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ ENNReal.ofReal (p i))
    (α : ι) (L : List (Finset ι)) :
    logMeasure S (sequenceOccurrence P α L) ≤ ENNReal.ofReal (sequenceWeight p L) := by
  by_cases hocc : (sequenceOccurrence P α L).Nonempty
  · obtain ⟨ωrep, srep, _, hrep⟩ := hocc
    let C : ℕ → ι := shiftedC P (initialStateFromLog ωrep) ωrep
    have hsub : sequenceOccurrence P α L ⊆ {ω | τCheck P (τC P C (srep + 1)) ω} :=
      sequenceOccurrence_subset_τCheck_of_representative P α L ωrep srep hrep
    have hweight : sequenceWeight p L =
        ∏ w ∈ (τC P C (srep + 1)).dom, p ((τC P C (srep + 1)).lab w) := by
      have h := randomInitSequence_weight_eq_prod P p ωrep srep
      rw [hrep] at h
      exact h
    calc
      logMeasure S (sequenceOccurrence P α L) ≤
          logMeasure S {ω | τCheck P (τC P C (srep + 1)) ω} := measure_mono hsub
      _ = ∏ w ∈ (τC P C (srep + 1)).dom,
          Measure.pi (fun v => S.measure v) (P.bad ((τC P C (srep + 1)).lab w)) :=
        logMeasure_τCheck_eq_prod_p_of_τC P hbad C (srep + 1)
      _ ≤ ∏ w ∈ (τC P C (srep + 1)).dom,
          ENNReal.ofReal (p ((τC P C (srep + 1)).lab w)) :=
        Finset.prod_le_prod (fun w _ => hp ((τC P C (srep + 1)).lab w))
      _ = ENNReal.ofReal (sequenceWeight p L) := by
        rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ =>
          hp_nonneg ((τC P C (srep + 1)).lab w)), ← hweight]
  · rw [Set.not_nonempty_iff_eq_empty.mp hocc, measure_empty]
    exact bot_le

#check @logMeasure_sequenceOccurrence_le_sequenceWeight

end Shearer
