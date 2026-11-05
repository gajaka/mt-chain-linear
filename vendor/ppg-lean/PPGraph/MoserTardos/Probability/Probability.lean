/-
  PPGraphMoserTardosProbability.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), Theorem 5.7.2, probability half.

  Connects the deterministic checking procedure (`PPGraphMoserTardosCheck.lean`,
  `τCheck`) to the actual probability measure over logs (`PPGraphMoserTardosLogSpace.lean`,
  `logMeasure`), via the independent-encoding technique: each vertex `w` of a witness
  tree `T` reads the log at a FINITE, tree-determined set of coordinates
  (`checkState_bad_depends_only_on_indices`), and distinct vertices read PAIRWISE
  DISJOINT coordinate sets (`checkState_indices_injective`,
  `PPGraphMoserTardosCheckBirth.lean`). Since `logMeasure` is an independent product
  over all (index, variable) coordinates, events depending on disjoint coordinate
  blocks are independent, giving `Pr[τCheck] = ∏_w Pr[vertex w's own check]`.

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import Mathlib.Probability.ProductMeasure
public import PPGraph.MoserTardos.Witness.Check
public import PPGraph.MoserTardos.Witness.CheckBirth
public import PPGraph.MoserTardos.Process.LogSpace

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical MeasureTheory

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- The coordinate block a vertex reads, and its disjointness
-- -------------------------------------------------------------------

/-- The finite set of LogSpace coordinates vertex `w` reads: one
    `(localCount, v)` pair per variable in its label's footprint.
    `checkState P T ω w ∈ P.bad (T.lab w)` depends only on `ω`'s values
    here (`checkState_bad_depends_only_on_indices`). -/
noncomputable def vertexIdx {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (w : List ℕ) : Finset (ℕ × V) :=
  (P.footprint (T.lab w)).image (fun v => (localCount P T w v, v))

/-- Distinct vertices of a `τC`-built tree read pairwise disjoint
    coordinate blocks -- immediate from `checkState_indices_injective`:
    a shared coordinate would force `v1 = v2` (equal second components)
    and hence `w1 = w2` by injectivity, contradicting `w1 ≠ w2`. -/
theorem vertexIdx_disjoint {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w1 w2 : List ℕ)
    (hw1 : w1 ∈ (τC P C t).dom) (hw2 : w2 ∈ (τC P C t).dom) (hne : w1 ≠ w2) :
    Disjoint (vertexIdx P (τC P C t) w1) (vertexIdx P (τC P C t) w2) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  unfold vertexIdx at hp1 hp2
  rw [Finset.mem_image] at hp1 hp2
  obtain ⟨v1, hv1, heq1⟩ := hp1
  obtain ⟨v2, hv2, heq2⟩ := hp2
  have hveq : v1 = v2 := by
    have := heq1.trans heq2.symm
    exact (Prod.mk.injEq _ _ _ _).mp this |>.2
  have hidxeq : localCount P (τC P C t) w1 v1 = localCount P (τC P C t) w2 v2 := by
    have := heq1.trans heq2.symm
    exact (Prod.mk.injEq _ _ _ _).mp this |>.1
  exact hne (checkState_indices_injective P C t w1 w2 hw1 hw2 v1 v2 hv1 hv2 hveq hidxeq)

-- -------------------------------------------------------------------
-- General block-independence infrastructure for `Measure.infinitePi`
-- (not specific to Moser-Tardos -- reusable measure theory). Mathlib
-- has `infinitePi_map_restrict` (finite marginal of infinitePi is
-- Measure.pi) and `measurePreserving_piFinsetUnion` (Measure.pi over a
-- disjoint Finset union is a product of the two Measure.pi's), but no
-- ready-made "events depending on disjoint finite coordinate blocks
-- are independent" lemma -- built from those two.
-- -------------------------------------------------------------------

section BlockIndep

variable {ι : Type} [DecidableEq ι] {X : ι → Type} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- A fixed base point, one per coordinate, existing since
    `MeasureTheory.nonempty_of_isProbabilityMeasure` gives each `X i` a
    point from `μ i` being a probability measure. -/
noncomputable def basePoint (i : ι) : X i :=
  (MeasureTheory.nonempty_of_isProbabilityMeasure (μ i)).some

/-- Canonical extension of a partial assignment on `F` to a full one,
    filling every coordinate outside `F` with `basePoint`. Literally
    `Function.updateFinset` from the fixed base point, so it inherits
    Mathlib's existing `updateFinset` lemma library (`restrict_updateFinset`,
    `measurable_updateFinset`, and -- the crux step below --
    `updateFinset_updateFinset`, which connects two nested updates to
    `Equiv.piFinsetUnion`). -/
noncomputable def extendDefault (F : Finset ι) (y : ∀ i : F, X i) : ∀ i, X i :=
  Function.updateFinset (basePoint μ) F y

theorem extendDefault_restrict (F : Finset ι) (y : ∀ i : F, X i) :
    F.restrict (extendDefault μ F y) = y :=
  Function.restrict_updateFinset (basePoint μ) y

theorem measurable_extendDefault (F : Finset ι) : Measurable (extendDefault μ F) :=
  measurable_updateFinset

/-- A set depending only on `F` (in the `depends_only_on` sense) is
    exactly the preimage under `F.restrict` of its own image under
    `extendDefault` -- the "factor through the restriction" fact,
    built explicitly via `extendDefault` rather than reached for via
    Mathlib's general `DependsOn`/`Function.FactorsThrough` machinery
    (no converse from `DependsOn` to `Measurable[piFinset]` exists
    there, so hand-building via a concrete extension is more direct). -/
theorem dependsOn_eq_restrict_preimage {F : Finset ι} {A : Set (∀ i, X i)}
    (hA : ∀ ω1 ω2 : ∀ i, X i, (∀ i ∈ F, ω1 i = ω2 i) → (ω1 ∈ A ↔ ω2 ∈ A)) :
    A = (F.restrict : (∀ i, X i) → ∀ i : F, X i) ⁻¹' (extendDefault μ F ⁻¹' A) := by
  ext ω
  simp only [Set.mem_preimage]
  apply hA
  intro i hi
  have h := congrFun (extendDefault_restrict μ F (F.restrict ω)) ⟨i, hi⟩
  simpa only [Finset.restrict] using h.symm

/-- The `infinitePi` measure of a set depending only on a finite `F` is
    exactly its `Measure.pi`-measure after collapsing onto `F` via
    `extendDefault` -- `infinitePi`'s general finite-marginal fact
    (`Measure.infinitePi_map_restrict`) specialized through the
    factoring above. -/
theorem infinitePi_eq_pi_of_dependsOn {F : Finset ι} {A : Set (∀ i, X i)}
    (hA : ∀ ω1 ω2 : ∀ i, X i, (∀ i ∈ F, ω1 i = ω2 i) → (ω1 ∈ A ↔ ω2 ∈ A))
    (hAmeas : MeasurableSet A) :
    Measure.infinitePi μ A = Measure.pi (fun i : F => μ i) (extendDefault μ F ⁻¹' A) := by
  have heq := dependsOn_eq_restrict_preimage μ hA
  have hAmeas' : MeasurableSet (extendDefault μ F ⁻¹' A) :=
    hAmeas.preimage (measurable_extendDefault μ F)
  calc Measure.infinitePi μ A
      = Measure.infinitePi μ (F.restrict ⁻¹' (extendDefault μ F ⁻¹' A)) := by rw [← heq]
    _ = (Measure.infinitePi μ).map F.restrict (extendDefault μ F ⁻¹' A) := by
        rw [Measure.map_apply (F.measurable_restrict) hAmeas']
    _ = Measure.pi (fun i : F => μ i) (extendDefault μ F ⁻¹' A) := by
        rw [Measure.infinitePi_map_restrict]

/-- Restricting to `F1` after updating a DISJOINT `F2` is unaffected by
    that update -- the complement of `restrict_updateFinset_of_subset`
    (which handles restricting to a SUBSET of what was updated; here we
    restrict to something disjoint from it instead). -/
theorem restrict_updateFinset_of_disjoint {F1 F2 : Finset ι} (hdisj : Disjoint F1 F2)
    (x : ∀ i, X i) (z : ∀ i : F2, X i) :
    F1.restrict (Function.updateFinset x F2 z) = F1.restrict x := by
  funext i
  simp only [Finset.restrict, Function.updateFinset]
  rw [dite_eq_right (Finset.disjoint_left.mp hdisj i.2)]

/-- The crux independence step: `infinitePi` splits multiplicatively
    over two sets depending on DISJOINT finite coordinate blocks. Built
    from `infinitePi_eq_pi_of_dependsOn` (collapsing each side, and the
    combined `A ∩ B`, onto a finite `Measure.pi`) plus
    `measurePreserving_piFinsetUnion` (the disjoint-union product
    structure) and `updateFinset_updateFinset` (identifying
    `extendDefault` over `F1 ∪ F2` with nesting the two individual
    `extendDefault`s, so the combined preimage is literally a product
    set `A₀ ×ˢ B₀`). -/
theorem infinitePi_inter_eq_mul_of_dependsOn
    {F1 F2 : Finset ι} (hdisj : Disjoint F1 F2) {A B : Set (∀ i, X i)}
    (hAdep : ∀ ω1 ω2 : ∀ i, X i, (∀ i ∈ F1, ω1 i = ω2 i) → (ω1 ∈ A ↔ ω2 ∈ A))
    (hAmeas : MeasurableSet A)
    (hBdep : ∀ ω1 ω2 : ∀ i, X i, (∀ i ∈ F2, ω1 i = ω2 i) → (ω1 ∈ B ↔ ω2 ∈ B))
    (hBmeas : MeasurableSet B) :
    Measure.infinitePi μ (A ∩ B) = Measure.infinitePi μ A * Measure.infinitePi μ B := by
  have hABdep : ∀ ω1 ω2 : ∀ i, X i, (∀ i ∈ F1 ∪ F2, ω1 i = ω2 i) → (ω1 ∈ A ∩ B ↔ ω2 ∈ A ∩ B) := by
    intro ω1 ω2 hagree
    have hA' := hAdep ω1 ω2 (fun i hi => hagree i (Finset.mem_union_left F2 hi))
    have hB' := hBdep ω1 ω2 (fun i hi => hagree i (Finset.mem_union_right F1 hi))
    exact and_congr hA' hB'
  have hABmeas : MeasurableSet (A ∩ B) := hAmeas.inter hBmeas
  rw [infinitePi_eq_pi_of_dependsOn μ hAdep hAmeas,
      infinitePi_eq_pi_of_dependsOn μ hBdep hBmeas,
      infinitePi_eq_pi_of_dependsOn μ hABdep hABmeas]
  have hmp := measurePreserving_piFinsetUnion hdisj μ
  have hAB0meas : MeasurableSet (extendDefault μ (F1 ∪ F2) ⁻¹' (A ∩ B)) :=
    hABmeas.preimage (measurable_extendDefault μ (F1 ∪ F2))
  rw [← hmp.map_eq, Measure.map_apply hmp.measurable hAB0meas]
  have hcoe : ⇑(MeasurableEquiv.piFinsetUnion X hdisj) = ⇑(Equiv.piFinsetUnion X hdisj) := rfl
  have hset : (MeasurableEquiv.piFinsetUnion X hdisj) ⁻¹' (extendDefault μ (F1 ∪ F2) ⁻¹' (A ∩ B))
      = (extendDefault μ F1 ⁻¹' A) ×ˢ (extendDefault μ F2 ⁻¹' B) := by
    ext ⟨y, z⟩
    have key1 : ∀ i (hi : i ∈ F1), extendDefault μ (F1 ∪ F2) (MeasurableEquiv.piFinsetUnion X hdisj ⟨y, z⟩) i
        = extendDefault μ F1 y i := by
      intro i hi
      simp only [extendDefault, Function.updateFinset, dite_eq_left hi, dite_eq_left (Finset.mem_union_left F2 hi)]
      rw [hcoe]
      exact Equiv.piFinsetUnion_left X hdisj hi (Finset.mem_union_left F2 hi)
    have key2 : ∀ i (hi : i ∈ F2), extendDefault μ (F1 ∪ F2) (MeasurableEquiv.piFinsetUnion X hdisj ⟨y, z⟩) i
        = extendDefault μ F2 z i := by
      intro i hi
      simp only [extendDefault, Function.updateFinset, dite_eq_left hi, dite_eq_left (Finset.mem_union_right F1 hi)]
      rw [hcoe]
      exact Equiv.piFinsetUnion_right X hdisj hi (Finset.mem_union_right F1 hi)
    have hagreeA := fun i (hi : i ∈ F1) => (key1 i hi).symm
    have hagreeB := fun i (hi : i ∈ F2) => (key2 i hi).symm
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff]
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨(hAdep (extendDefault μ F1 y) _ hagreeA).mpr ha,
             (hBdep (extendDefault μ F2 z) _ hagreeB).mpr hb⟩
    · rintro ⟨ha, hb⟩
      exact ⟨(hAdep (extendDefault μ F1 y) _ hagreeA).mp ha,
             (hBdep (extendDefault μ F2 z) _ hagreeB).mp hb⟩
  rw [hset, Measure.prod_prod]

/-- The n-ary generalization: `infinitePi` splits multiplicatively over
    a FINITE family of sets, each depending on its own coordinate
    block, PROVIDED the blocks are pairwise disjoint (over the finset
    `s` doing the indexing). By induction on `s`, peeling one element
    off at a time and applying `infinitePi_inter_eq_mul_of_dependsOn`
    to (that element's block) vs (the union of the rest). -/
theorem infinitePi_iInter_eq_prod_of_dependsOn {ι' : Type}
    (s : Finset ι') (blk : ι' → Finset ι) (E : ι' → Set (∀ i, X i))
    (hdisj : (↑s : Set ι').PairwiseDisjoint blk)
    (hdep : ∀ w ∈ s, ∀ ω1 ω2 : ∀ i, X i, (∀ i ∈ blk w, ω1 i = ω2 i) → (ω1 ∈ E w ↔ ω2 ∈ E w))
    (hmeas : ∀ w ∈ s, MeasurableSet (E w)) :
    Measure.infinitePi μ (⋂ w ∈ s, E w) = ∏ w ∈ s, Measure.infinitePi μ (E w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert w0 s' hw0 ih =>
    have hsplit : (⋂ w ∈ insert w0 s', E w) = E w0 ∩ ⋂ w ∈ s', E w := by
      ext x
      simp only [Set.mem_iInter, Finset.mem_insert, Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨h w0 (Or.inl rfl), fun w hw => h w (Or.inr hw)⟩
      · rintro ⟨h0, hrest⟩ w (hw | hw)
        · rw [hw]; exact h0
        · exact hrest w hw
    rw [hsplit, Finset.prod_insert hw0]
    have hdisj' : (↑s' : Set ι').PairwiseDisjoint blk := hdisj.subset (by simp)
    have hdep' : ∀ w ∈ s', ∀ ω1 ω2 : ∀ i, X i, (∀ i ∈ blk w, ω1 i = ω2 i) → (ω1 ∈ E w ↔ ω2 ∈ E w) :=
      fun w hw => hdep w (Finset.mem_insert_of_mem hw)
    have hmeas' : ∀ w ∈ s', MeasurableSet (E w) := fun w hw => hmeas w (Finset.mem_insert_of_mem hw)
    have ihs' := ih hdisj' hdep' hmeas'
    have hrest_dep : ∀ ω1 ω2 : ∀ i, X i, (∀ i ∈ s'.biUnion blk, ω1 i = ω2 i)
        → (ω1 ∈ ⋂ w ∈ s', E w ↔ ω2 ∈ ⋂ w ∈ s', E w) := by
      intro ω1 ω2 hagree
      simp only [Set.mem_iInter]
      refine forall_congr' fun w => forall_congr' fun hw => ?_
      exact hdep' w hw ω1 ω2 (fun i hi => hagree i (Finset.mem_biUnion.mpr ⟨w, hw, hi⟩))
    have hrest_meas : MeasurableSet (⋂ w ∈ s', E w) := MeasurableSet.biInter s'.countable_toSet hmeas'
    have hw0_disj_rest : Disjoint (blk w0) (s'.biUnion blk) := by
      rw [Finset.disjoint_biUnion_right]
      intro w hw
      exact hdisj (Finset.mem_insert_self w0 s') (Finset.mem_insert_of_mem hw)
        (fun h => hw0 (h ▸ hw))
    rw [infinitePi_inter_eq_mul_of_dependsOn μ hw0_disj_rest
          (hdep w0 (Finset.mem_insert_self w0 s')) (hmeas w0 (Finset.mem_insert_self w0 s'))
          hrest_dep hrest_meas,
        ihs']

#check @nonempty_of_isProbabilityMeasure
#check @extendDefault
#check @extendDefault_restrict
#check @measurable_extendDefault
#check @dependsOn_eq_restrict_preimage
#check @restrict_updateFinset_of_disjoint
#check @infinitePi_inter_eq_mul_of_dependsOn
#check @infinitePi_eq_pi_of_dependsOn

end BlockIndep

-- -------------------------------------------------------------------
-- The result: Theorem 5.7.2's probability bound, `τCheck`'s
-- probability under `logMeasure` splits into a product over the
-- witness tree's own vertices.
-- -------------------------------------------------------------------

/-- Each vertex's own check-event depends only on `ω`'s values at its
    `vertexIdx` block -- routes `checkState_bad_depends_only_on_indices`
    (an `MTState`-level `depends_only_on` fact) through the
    `LogSpace`-coordinate view `vertexIdx` uses. -/
theorem checkState_event_dependsOn {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (w : List ℕ) :
    ∀ ω1 ω2 : LogSpace S, (∀ i ∈ vertexIdx P T w, ω1 i = ω2 i) →
      (checkState P T ω1 w ∈ P.bad (T.lab w) ↔ checkState P T ω2 w ∈ P.bad (T.lab w)) := by
  intro ω1 ω2 hagree
  apply checkState_bad_depends_only_on_indices
  intro v hv
  exact hagree (localCount P T w v, v) (Finset.mem_image.mpr ⟨v, hv, rfl⟩)

/-- Measurability of a single vertex's check-event, given the standing
    `hbad` hypothesis (every `P.bad i` measurable) already used
    throughout the random-trajectory files. -/
theorem measurableSet_checkState_event {S : VarSpaces V} {ι : Type} [Fintype ι]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (T : GrowingTree ι) (w : List ℕ) :
    MeasurableSet {ω : LogSpace S | checkState P T ω w ∈ P.bad (T.lab w)} := by
  have hmeas : Measurable (fun ω : LogSpace S => checkState P T ω w) := by
    apply Measurable.of_eval
    intro v
    exact measurable_pi_apply (localCount P T w v, v)
  exact hmeas (hbad (T.lab w))

/-- Theorem 5.7.2, the probability half. The probability, under
    `logMeasure` (the genuine random log), that a witness tree's τ-check
    passes is a product over the tree's vertices, one factor per vertex.
    Each vertex reads a coordinate block disjoint from every other
    vertex's (`vertexIdx_disjoint`, from `checkState_indices_injective`),
    so `infinitePi_iInter_eq_prod_of_dependsOn` applies. -/
theorem logMeasure_τCheck_eq_prod {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (C : ℕ → ι) (t : ℕ) :
    logMeasure S {ω | τCheck P (τC P C t) ω}
      = ∏ w ∈ (τC P C t).dom,
          logMeasure S {ω | checkState P (τC P C t) ω w ∈ P.bad ((τC P C t).lab w)} := by
  have hset : {ω : LogSpace S | τCheck P (τC P C t) ω}
      = ⋂ w ∈ (τC P C t).dom, {ω | checkState P (τC P C t) ω w ∈ P.bad ((τC P C t).lab w)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, τCheck]
  rw [hset]
  unfold logMeasure
  exact infinitePi_iInter_eq_prod_of_dependsOn (μCoin S) (τC P C t).dom
    (vertexIdx P (τC P C t))
    (fun w => {ω | checkState P (τC P C t) ω w ∈ P.bad ((τC P C t).lab w)})
    (fun w1 hw1 w2 hw2 hne => vertexIdx_disjoint P C t w1 w2 hw1 hw2 hne)
    (fun w _ => checkState_event_dependsOn P (τC P C t) w)
    (fun w _ => measurableSet_checkState_event P hbad (τC P C t) w)

-- -------------------------------------------------------------------
-- Closing the loop: each single-vertex factor reduces to the label's
-- own base probability `p(label w)` -- no independence needed here,
-- just that reading ANY fixed per-variable slot gives the SAME law
-- (μCoin's law at (n,v) is `S.measure v` regardless of `n`).
-- -------------------------------------------------------------------

/-- Read each variable at its own FIXED slot `n v` -- `checkState`'s
    shape with an arbitrary (not tree-derived) per-variable index.
    Codomain stated as the UNFOLDED `∀ v, S.space v` rather than
    `MTState S` -- both are the same type, but `MTState` is a `def`
    (not `abbrev`) carrying its OWN separately-declared
    `instMeasurableSpaceMTState` instance, which typeclass search does
    not automatically identify with the generic Pi instance found here
    even though they're defeq -- staying on the generic side throughout
    avoids that instance mismatch resurfacing inside `Measure.pi_eq`'s
    machine-generated subgoals. -/
def readAt {S : VarSpaces V} (n : V → ℕ) (ω : LogSpace S) : ∀ v, S.space v :=
  fun v => atIdx ω v (n v)

theorem measurable_readAt {S : VarSpaces V} (n : V → ℕ) :
    Measurable (readAt (S := S) n) := by
  apply Measurable.of_eval
  intro v
  exact measurable_pi_apply (n v, v)

/-- However the per-variable slots are chosen, reading them gives
    exactly the natural product law over `MTState` -- since `μCoin`
    only depends on the VARIABLE coordinate, never the slot. This is
    what lets `checkState`'s tree-dependent slot choice (`localCount`)
    be identified with the label's plain probability `p(label w)`. -/
theorem logMeasure_map_readAt_eq_pi {S : VarSpaces V} [Fintype V] (n : V → ℕ) :
    (logMeasure S).map (readAt n) = Measure.pi (fun v => S.measure v) := by
  have : ∀ v, IsProbabilityMeasure (S.measure v) := S.isProb
  have hinj : ∀ v1 ∈ (Finset.univ : Finset V), ∀ v2 ∈ (Finset.univ : Finset V),
      (n v1, v1) = (n v2, v2) → v1 = v2 :=
    fun v1 _ v2 _ h => (Prod.mk.injEq _ _ _ _).mp h |>.2
  symm
  apply MeasureTheory.Measure.pi_eq
  intro s hs
  have heq : (readAt n) ⁻¹' (Set.pi Set.univ s)
      = Set.pi (Finset.univ.image (fun v : V => (n v, v)) : Finset (ℕ × V))
          (fun i : ℕ × V => s i.2) := by
    ext ω
    constructor
    · intro h i hi
      rw [Finset.mem_coe, Finset.mem_image] at hi
      obtain ⟨v, _, hv⟩ := hi
      rw [← hv]
      exact h v (Set.mem_univ v)
    · intro h v _
      exact h (n v, v) (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ v)))
  rw [Measure.map_apply (measurable_readAt n) (MeasurableSet.univ_pi hs), heq]
  have hmeas : ∀ i ∈ Finset.univ.image (fun v : V => (n v, v)), MeasurableSet (s i.2) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨v, _, hv⟩ := hi
    rw [← hv]
    exact hs v
  show Measure.infinitePi (μCoin S) _ = _
  rw [Measure.infinitePi_pi (μ := μCoin S) hmeas, Finset.prod_image hinj]
  rfl

/-- The closing identification: each vertex's own check-probability
    equals the label's base probability under the natural product
    measure over `MTState` -- matching what `mtWeight`'s `p` stands for
    in `PPGraphMoserTardosConvergence.lean`. -/
theorem logMeasure_checkState_eq_pi {S : VarSpaces V} [Fintype V] {ι : Type}
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (T : GrowingTree ι) (w : List ℕ) :
    logMeasure S {ω | checkState P T ω w ∈ P.bad (T.lab w)}
      = Measure.pi (fun v => S.measure v) (P.bad (T.lab w)) := by
  rw [← logMeasure_map_readAt_eq_pi (S := S) (fun v => localCount P T w v),
      Measure.map_apply (measurable_readAt _) (hbad (T.lab w))]
  rfl

/-- Theorem 5.7.2 in its usual stated form: the probability a
    witness tree's τ-check passes equals the product, over its own
    vertices, of each vertex's LABEL's base probability -- combining
    `logMeasure_τCheck_eq_prod` (the independence/product-over-vertices
    structure) with `logMeasure_checkState_eq_pi` (each factor reduces
    to the label's own probability, no independence needed there). -/
theorem logMeasure_τCheck_eq_prod_p {S : VarSpaces V} [Fintype V] {ι : Type} [Fintype ι]
    [DecidableEq ι] (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (C : ℕ → ι) (t : ℕ) :
    logMeasure S {ω | τCheck P (τC P C t) ω}
      = ∏ w ∈ (τC P C t).dom, Measure.pi (fun v => S.measure v) (P.bad ((τC P C t).lab w)) := by
  rw [logMeasure_τCheck_eq_prod P hbad C t]
  exact Finset.prod_congr rfl (fun w _ => logMeasure_checkState_eq_pi P hbad (τC P C t) w)

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @vertexIdx
#check @vertexIdx_disjoint
#check @checkState_event_dependsOn
#check @measurableSet_checkState_event
#check @logMeasure_τCheck_eq_prod
#check @readAt
#check @logMeasure_map_readAt_eq_pi
#check @logMeasure_checkState_eq_pi
#check @logMeasure_τCheck_eq_prod_p

-- Explicit checks for all remaining helper theorems.
#check @infinitePi_iInter_eq_prod_of_dependsOn
#check @measurable_readAt
