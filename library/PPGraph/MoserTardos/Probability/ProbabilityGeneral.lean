/-
  PPGraphMoserTardosProbabilityGeneral.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), Theorem 5.7.2 GENERALIZED to an
  arbitrary GrowingTree, not just `tau_C P C t`.

  Checked directly (not guessed): the ONLY place the existing
  `checkState_indices_injective` (PPGraphMoserTardosCheckBirth.lean) needs
  anything tau_C-SPECIFIC is one line inside `localCount_ne_of_ne`'s equal-length
  case, which calls `tauBuild_sameDepthIndependent` purely to extract the
  `SameDepthIndependent` CONCLUSION. Everything else in that proof
  (`localCount_strict_anti`, `footprint_common_var_same_or_neighbor`) is already
  stated for an arbitrary GrowingTree. Likewise `checkState_event_dependsOn` and
  `measurableSet_checkState_event` (PPGraphMoserTardosCheck.lean /
  PPGraphMoserTardosProbability.lean) are ALREADY general.

  So Theorem 5.7.2 genuinely only needs `SameDepthIndependent P T` as an
  ABSTRACT HYPOTHESIS, not "T is literally built by tau_Build" -- this file
  re-derives the whole chain taking that hypothesis explicitly, so a future
  FIXED, tau_C-independent witness-tree representative (once one is
  constructed, together with a shape-level proof that it inherits
  SameDepthIndependent from the real occurrence it represents) can use
  Theorem 5.7.2 WITHOUT needing to be presented as `tau_C P C' t'` for some
  C', t' -- sidestepping the (so far unresolved) question of whether an
  arbitrary occurring canonical shape can be realized that way.

  This file changes NOTHING about the existing tau_C-specific theorems (kept
  exactly as-is, still used by Lemma 2.1(ii) etc.) -- it only ADDS the
  general versions, recovering the tau_C-specific ones as trivial corollaries
  for sanity (bottom of file).

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.MoserTardos.Witness.CheckBirth
public import PPGraph.MoserTardos.Probability.Probability

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical MeasureTheory

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- Section 1: the distinctness chain, generalized to take
-- `SameDepthIndependent P T` as an explicit hypothesis instead of deriving
-- it internally from `τBuild_sameDepthIndependent`.
-- -------------------------------------------------------------------

theorem localCount_ne_of_ne_general {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (hSDI : SameDepthIndependent P T)
    (w1 w2 : List ℕ) (hw1 : w1 ∈ T.dom) (hw2 : w2 ∈ T.dom) (hne : w1 ≠ w2)
    (v : V) (hv1 : v ∈ P.footprint (T.lab w1)) (hv2 : v ∈ P.footprint (T.lab w2)) :
    localCount P T w1 v ≠ localCount P T w2 v := by
  rcases lt_trichotomy w1.length w2.length with hlt | heqlen | hgt
  · exact ne_of_gt (localCount_strict_anti P T w1 w2 hw1 hw2 v hv1 hv2 hlt)
  · exfalso
    obtain ⟨hlabne, hnotneighbor⟩ := hSDI w1 w2 hw1 hw2 heqlen hne
    rcases footprint_common_var_same_or_neighbor P (T.lab w1) (T.lab w2) v hv1 hv2
      with heq' | hneighbor'
    · exact hlabne heq'
    · exact hnotneighbor hneighbor'
  · exact ne_of_lt (localCount_strict_anti P T w2 w1 hw2 hw1 v hv2 hv1 hgt)

theorem checkState_indices_injective_general {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (hSDI : SameDepthIndependent P T)
    (w1 w2 : List ℕ) (hw1 : w1 ∈ T.dom) (hw2 : w2 ∈ T.dom)
    (v1 v2 : V) (hv1 : v1 ∈ P.footprint (T.lab w1)) (hv2 : v2 ∈ P.footprint (T.lab w2))
    (hveq : v1 = v2) (hidxeq : localCount P T w1 v1 = localCount P T w2 v2) :
    w1 = w2 := by
  by_contra hne
  subst hveq
  exact localCount_ne_of_ne_general P T hSDI w1 w2 hw1 hw2 hne v1 hv1 hv2 hidxeq

theorem vertexIdx_disjoint_general {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (hSDI : SameDepthIndependent P T)
    (w1 w2 : List ℕ) (hw1 : w1 ∈ T.dom) (hw2 : w2 ∈ T.dom) (hne : w1 ≠ w2) :
    Disjoint (vertexIdx P T w1) (vertexIdx P T w2) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  unfold vertexIdx at hp1 hp2
  rw [Finset.mem_image] at hp1 hp2
  obtain ⟨v1, hv1, heq1⟩ := hp1
  obtain ⟨v2, hv2, heq2⟩ := hp2
  have hveq : v1 = v2 := by
    have := heq1.trans heq2.symm
    exact (Prod.mk.injEq _ _ _ _).mp this |>.2
  have hidxeq : localCount P T w1 v1 = localCount P T w2 v2 := by
    have := heq1.trans heq2.symm
    exact (Prod.mk.injEq _ _ _ _).mp this |>.1
  exact hne (checkState_indices_injective_general P T hSDI w1 w2 hw1 hw2 v1 v2 hv1 hv2 hveq hidxeq)

-- -------------------------------------------------------------------
-- Section 2: Theorem 5.7.2 itself, generalized. `checkState_event_dependsOn`
-- and `measurableSet_checkState_event` were ALREADY general (no change
-- needed); only the disjointness step required `SameDepthIndependent`.
-- -------------------------------------------------------------------

theorem logMeasure_τCheck_eq_prod_general {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (T : GrowingTree ι) (hSDI : SameDepthIndependent P T) :
    logMeasure S {ω | τCheck P T ω}
      = ∏ w ∈ T.dom, logMeasure S {ω | checkState P T ω w ∈ P.bad (T.lab w)} := by
  have hset : {ω : LogSpace S | τCheck P T ω}
      = ⋂ w ∈ T.dom, {ω | checkState P T ω w ∈ P.bad (T.lab w)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, τCheck]
  rw [hset]
  unfold logMeasure
  exact infinitePi_iInter_eq_prod_of_dependsOn (μCoin S) T.dom (vertexIdx P T)
    (fun w => {ω | checkState P T ω w ∈ P.bad (T.lab w)})
    (fun w1 hw1 w2 hw2 hne => vertexIdx_disjoint_general P T hSDI w1 w2 hw1 hw2 hne)
    (fun w _ => checkState_event_dependsOn P T w)
    (fun w _ => measurableSet_checkState_event P hbad T w)

/-- Theorem 5.7.2, generalized: holds for ANY GrowingTree `T` satisfying
    `SameDepthIndependent` -- not just `τC P C t`. This is the form a future
    fixed, omega-independent witness-tree representative needs: it only has
    to be shown to satisfy `SameDepthIndependent` (a shape-inheritable fact,
    not "was built by τBuild"), never to be literally `τC P C' t'` for some
    C', t'. -/
theorem logMeasure_τCheck_eq_prod_p_general {S : VarSpaces V} [Fintype V] {ι : Type}
    [Fintype ι] [DecidableEq ι] (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (T : GrowingTree ι) (hSDI : SameDepthIndependent P T) :
    logMeasure S {ω | τCheck P T ω}
      = ∏ w ∈ T.dom, Measure.pi (fun v => S.measure v) (P.bad (T.lab w)) := by
  rw [logMeasure_τCheck_eq_prod_general P hbad T hSDI]
  exact Finset.prod_congr rfl (fun w _ => logMeasure_checkState_eq_pi P hbad T w)

-- -------------------------------------------------------------------
-- Section 3: sanity -- the old τC-specific theorems really are special
-- cases (τC's own SameDepthIndependent proof supplies the hypothesis).
-- -------------------------------------------------------------------

theorem logMeasure_τCheck_eq_prod_p_of_τC {S : VarSpaces V} [Fintype V] {ι : Type}
    [Fintype ι] [DecidableEq ι] (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (C : ℕ → ι) (t : ℕ) :
    logMeasure S {ω | τCheck P (τC P C t) ω}
      = ∏ w ∈ (τC P C t).dom, Measure.pi (fun v => S.measure v) (P.bad ((τC P C t).lab w)) :=
  logMeasure_τCheck_eq_prod_p_general P hbad (τC P C t) (τBuild_sameDepthIndependent P C t (t - 1))

#check @localCount_ne_of_ne_general
#check @checkState_indices_injective_general
#check @vertexIdx_disjoint_general
#check @logMeasure_τCheck_eq_prod_general
#check @logMeasure_τCheck_eq_prod_p_general
#check @logMeasure_τCheck_eq_prod_p_of_τC
