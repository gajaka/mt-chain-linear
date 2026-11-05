/-
  PPGraphMoserTardosCanonical.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), Theorem 5.7.1/5.7.2 bridge, part 2.

  The `wtreesUpTo` (PPGraphMoserTardosWeightSum.lean) enumeration is a
  `Finset (WTree ι)`, and `WTree`'s children are a `List` (order
  matters for literal term equality) built, at every node, via
  `Finset.attach.toList` over the LABEL set. A real tree (e.g. from
  `GrowingTree.toWTree`, PPGraphMoserTardosRealTree.lean) instead
  builds its children list via `Finset.attach.toList` over an ADDRESS
  set -- a different Finset of a different type, with no reason to
  produce the same list order. So an arbitrary WellFormed+Proper tree
  is NOT literally a member of `wtreesUpTo` in general: what IS true,
  and is all the eventual sum bound needs, is that it is WEIGHT-EQUAL
  to a tree that is -- since `weight` is a product over the (unordered)
  set of children, order never affects it.

  This file builds that bridge: `WTree.canonicalize` reconstructs a
  tree's children list in `wtreesUpTo`'s own canonical (label-Finset-
  attach) order, and is shown to preserve label/weight/WellFormed/
  Proper/depth and to genuinely land inside `wtreesUpTo`.

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.MoserTardos.Bounds.WeightSum

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical
open scoped NNReal

variable {ι : Type} [DecidableEq ι]

-- -------------------------------------------------------------------
-- Section 1: labelSet and childOf -- extracting "the child with a
-- given label" from a tree's children list
-- -------------------------------------------------------------------

/-- The (Finset) set of labels among a tree's immediate children. -/
noncomputable def WTree.labelSet (t : WTree ι) : Finset ι :=
  (t.children.map WTree.label).toFinset

theorem WTree.mem_labelSet_iff (t : WTree ι) (β : ι) :
    β ∈ t.labelSet ↔ ∃ c ∈ t.children, c.label = β := by
  unfold WTree.labelSet
  rw [List.mem_toFinset, List.mem_map]

/-- The (unique, given `Proper`) child carrying label `β`. -/
noncomputable def WTree.childOf (t : WTree ι) (β : ι) (hβ : β ∈ t.labelSet) : WTree ι :=
  ((t.mem_labelSet_iff β).mp hβ).choose

theorem WTree.childOf_mem (t : WTree ι) (β : ι) (hβ : β ∈ t.labelSet) :
    t.childOf β hβ ∈ t.children :=
  ((t.mem_labelSet_iff β).mp hβ).choose_spec.1

theorem WTree.childOf_label (t : WTree ι) (β : ι) (hβ : β ∈ t.labelSet) :
    (t.childOf β hβ).label = β :=
  ((t.mem_labelSet_iff β).mp hβ).choose_spec.2

/-- `Proper`'s sibling condition, restated as plain list-nodup on the
    children's labels -- `List.pairwise_map` connects the two shapes
    directly. -/
theorem WTree.proper_nodup_labels (t : WTree ι) (hp : t.Proper) :
    (t.children.map WTree.label).Nodup := by
  cases t with
  | mk i cs =>
    unfold WTree.Proper at hp
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact hp.1

/-- `Proper` forces the children list itself to be nodup (as `WTree`s):
    two equal children would trivially share a label, contradicting
    pairwise label-distinctness. -/
theorem WTree.proper_nodup_children (t : WTree ι) (hp : t.Proper) :
    t.children.Nodup :=
  List.Nodup.of_map WTree.label (t.proper_nodup_labels hp)

/-- Two children carrying the same label must be the SAME child --
    the key uniqueness fact `childOf` needs to be meaningful. -/
theorem WTree.eq_of_mem_children_label_eq (t : WTree ι) (hp : t.Proper)
    (c1 c2 : WTree ι) (h1 : c1 ∈ t.children) (h2 : c2 ∈ t.children)
    (hlab : c1.label = c2.label) : c1 = c2 := by
  cases t with
  | mk i cs =>
    unfold WTree.Proper at hp
    by_contra hne
    have hsymm : Std.Symm (fun a b : WTree ι => a.label ≠ b.label) := ⟨fun _ _ h => h.symm⟩
    exact (hp.1.forall h1 h2 hne) hlab

theorem WTree.childOf_eq_self_of_mem (t : WTree ι) (hp : t.Proper) (c : WTree ι)
    (hc : c ∈ t.children) :
    t.childOf c.label ((t.mem_labelSet_iff c.label).mpr ⟨c, hc, rfl⟩) = c :=
  t.eq_of_mem_children_label_eq hp _ c
    (t.childOf_mem c.label ((t.mem_labelSet_iff c.label).mpr ⟨c, hc, rfl⟩)) hc
    (t.childOf_label c.label ((t.mem_labelSet_iff c.label).mpr ⟨c, hc, rfl⟩))

-- -------------------------------------------------------------------
-- Section 2: the children list is a PERMUTATION of the label-Finset's
-- attach.toList mapped through childOf
-- -------------------------------------------------------------------

theorem WTree.children_perm_labelSet_attach (t : WTree ι) (hp : t.Proper) :
    List.Perm t.children
      (t.labelSet.attach.toList.map (fun p => t.childOf p.1 p.2)) := by
  have hcs_nodup : t.children.Nodup := t.proper_nodup_children hp
  have hother_nodup : (t.labelSet.attach.toList.map (fun p => t.childOf p.1 p.2)).Nodup := by
    apply List.Nodup.map
    · intro p q hpq
      have h1 := t.childOf_label p.1 p.2
      have h2 := t.childOf_label q.1 q.2
      apply Subtype.ext
      have hpq' : t.childOf p.1 p.2 = t.childOf q.1 q.2 := hpq
      rw [← h1, ← h2, hpq']
    · exact t.labelSet.attach.nodup_toList
  apply List.perm_of_nodup_nodup_toFinset_eq hcs_nodup hother_nodup
  apply Finset.Subset.antisymm
  · intro c hc
    simp only [List.mem_toFinset] at hc ⊢
    simp only [List.mem_map, Finset.mem_toList]
    refine ⟨⟨c.label, (t.mem_labelSet_iff c.label).mpr ⟨c, hc, rfl⟩⟩, Finset.mem_attach _ _, ?_⟩
    exact t.childOf_eq_self_of_mem hp c hc
  · intro c hc
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_toList] at hc
    obtain ⟨p, _, hpc⟩ := hc
    rw [List.mem_toFinset, ← hpc]
    exact t.childOf_mem p.1 p.2

-- -------------------------------------------------------------------
-- Verification (Section 1-2)
-- -------------------------------------------------------------------

-- -------------------------------------------------------------------
-- Section 3: depth is strictly bigger than any child's -- the
-- decreasing measure the canonicalization recursion needs
-- -------------------------------------------------------------------

theorem WTree.depth_lt_depthList (cs : List (WTree ι)) (c : WTree ι) (hc : c ∈ cs) :
    WTree.depth c < WTree.depthList cs := by
  induction cs with
  | nil => exact absurd hc List.not_mem_nil
  | cons x xs ih =>
    simp only [WTree.depthList]
    rcases List.mem_cons.mp hc with rfl | hc
    · have h : WTree.depth c < 1 + WTree.depth c := by omega
      exact lt_of_lt_of_le h (le_max_left _ _)
    · exact lt_of_lt_of_le (ih hc) (le_max_right _ _)

theorem WTree.depth_child_lt (t : WTree ι) (c : WTree ι) (hc : c ∈ t.children) :
    WTree.depth c < WTree.depth t := by
  cases t with
  | mk i cs => exact WTree.depth_lt_depthList cs c hc

-- -------------------------------------------------------------------
-- Section 4: canonicalize -- rebuild the children list in
-- `wtreesUpTo`'s own canonical (label-Finset-attach) order
-- -------------------------------------------------------------------

noncomputable def WTree.canonicalizeFuel : ℕ → WTree ι → WTree ι
  | 0, t => WTree.mk t.label []
  | (n + 1), t =>
      WTree.mk t.label
        (t.labelSet.attach.toList.map (fun p => WTree.canonicalizeFuel n (t.childOf p.1 p.2)))

theorem WTree.canonicalizeFuel_props {V : Type} [DecidableEq V] {S : VarSpaces V} [Fintype ι]
    (P : MTProcess S ι) (p : ι → ℝ≥0) :
    ∀ n (t : WTree ι), WTree.WellFormed P t → WTree.Proper t → WTree.depth t ≤ n →
      (WTree.canonicalizeFuel n t).label = t.label ∧
      (WTree.canonicalizeFuel n t).weight p = t.weight p ∧
      WTree.WellFormed P (WTree.canonicalizeFuel n t) ∧
      WTree.Proper (WTree.canonicalizeFuel n t) ∧
      (WTree.canonicalizeFuel n t) ∈ wtreesUpTo P n t.label := by
  intro n
  induction n with
  | zero =>
    intro t hwf hpr hd
    cases t with
    | mk i cs =>
      have hnil : cs = [] := by
        rcases cs with _ | ⟨c, cs'⟩
        · rfl
        · exfalso
          have hmem : c ∈ (c :: cs') := List.mem_cons_self
          have hlt := WTree.depth_lt_depthList (c :: cs') c hmem
          have hd' : WTree.depthList (c :: cs') ≤ 0 := hd
          omega
      subst hnil
      refine ⟨rfl, rfl, WTree.wellFormed_singleton P i, WTree.proper_singleton i, ?_⟩
      show WTree.mk i ([] : List (WTree ι)) ∈ wtreesUpTo P 0 i
      show WTree.mk i ([] : List (WTree ι)) ∈ ({WTree.mk i []} : Finset (WTree ι))
      exact Finset.mem_singleton_self _
  | succ n ih =>
    intro t hwf hpr hd
    cases t with
    | mk i cs =>
      have hwf1 : ∀ c ∈ cs, c.label = i ∨ neighbor P i c.label := by
        have h := hwf; unfold WTree.WellFormed at h; exact h.1
      have hwf2 : ∀ c ∈ cs, WTree.WellFormed P c := by
        have h := hwf; unfold WTree.WellFormed at h; exact h.2
      have hpr2 : ∀ c ∈ cs, WTree.Proper c := by
        have h := hpr; unfold WTree.Proper at h; exact h.2
      set T := (WTree.mk i cs).labelSet with hTdef
      set children := T.attach.toList.map (fun q => WTree.canonicalizeFuel n ((WTree.mk i cs).childOf q.1 q.2))
        with hchildren_def
      have hTsub : T ⊆ plusNeighbors P i := by
        intro β hβ
        obtain ⟨c, hcmem, hclab⟩ := (WTree.mk i cs).mem_labelSet_iff β |>.mp hβ
        have := hwf1 c hcmem
        rw [hclab] at this
        simp only [plusNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact this
      have hchild_ih : ∀ q : {β // β ∈ T},
          (WTree.canonicalizeFuel n ((WTree.mk i cs).childOf q.1 q.2)).label = q.1 ∧
          (WTree.canonicalizeFuel n ((WTree.mk i cs).childOf q.1 q.2)).weight p
            = ((WTree.mk i cs).childOf q.1 q.2).weight p ∧
          WTree.WellFormed P (WTree.canonicalizeFuel n ((WTree.mk i cs).childOf q.1 q.2)) ∧
          WTree.Proper (WTree.canonicalizeFuel n ((WTree.mk i cs).childOf q.1 q.2)) ∧
          (WTree.canonicalizeFuel n ((WTree.mk i cs).childOf q.1 q.2)) ∈ wtreesUpTo P n q.1 := by
        intro q
        have hcmem : (WTree.mk i cs).childOf q.1 q.2 ∈ cs := (WTree.mk i cs).childOf_mem q.1 q.2
        have hclabel : ((WTree.mk i cs).childOf q.1 q.2).label = q.1 :=
          (WTree.mk i cs).childOf_label q.1 q.2
        have hcwf : WTree.WellFormed P ((WTree.mk i cs).childOf q.1 q.2) := hwf2 _ hcmem
        have hcpr : WTree.Proper ((WTree.mk i cs).childOf q.1 q.2) := hpr2 _ hcmem
        have hcdepth : WTree.depth ((WTree.mk i cs).childOf q.1 q.2) ≤ n := by
          have hlt := (WTree.mk i cs).depth_child_lt _ hcmem
          have hd' : WTree.depth (WTree.mk i cs) ≤ n + 1 := hd
          omega
        have hres := ih _ hcwf hcpr hcdepth
        rwa [hclabel] at hres
      show (WTree.mk i children).label = i ∧
        (WTree.mk i children).weight p = (WTree.mk i cs).weight p ∧
        WTree.WellFormed P (WTree.mk i children) ∧
        WTree.Proper (WTree.mk i children) ∧
        (WTree.mk i children) ∈ wtreesUpTo P (n + 1) i
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · rw [hchildren_def]
        show (WTree.mk i (T.attach.toList.map (fun q => WTree.canonicalizeFuel n
            ((WTree.mk i cs).childOf q.1 q.2)))).weight p = (WTree.mk i cs).weight p
        rw [WTree.weight_children, WTree.weight_children]
        congr 1
        have hstep1 : (T.attach.toList.map (fun q => WTree.canonicalizeFuel n
            ((WTree.mk i cs).childOf q.1 q.2))).map (WTree.weight p)
            = T.attach.toList.map (fun q => ((WTree.mk i cs).childOf q.1 q.2).weight p) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro q _
          exact (hchild_ih q).2.1
        rw [hstep1]
        have hperm := (WTree.mk i cs).children_perm_labelSet_attach hpr
        show (T.attach.toList.map (fun q => ((WTree.mk i cs).childOf q.1 q.2).weight p)).prod
          = (cs.map (WTree.weight p)).prod
        have hpermMapped := hperm.map (WTree.weight p)
        rw [List.map_map] at hpermMapped
        exact hpermMapped.prod_eq.symm
      · unfold WTree.WellFormed
        constructor
        · intro c hc
          rw [hchildren_def] at hc
          simp only [List.mem_map, Finset.mem_toList] at hc
          obtain ⟨q, _, hqc⟩ := hc
          have hql := (hchild_ih q).1
          rw [← hqc, hql]
          have := hTsub q.2
          simp only [plusNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact this
        · intro c hc
          rw [hchildren_def] at hc
          simp only [List.mem_map, Finset.mem_toList] at hc
          obtain ⟨q, _, hqc⟩ := hc
          rw [← hqc]
          exact (hchild_ih q).2.2.1
      · unfold WTree.Proper
        constructor
        · rw [hchildren_def, List.pairwise_map]
          have hnodup : T.attach.toList.Pairwise (fun a b => a ≠ b) := by
            rw [← List.nodup_iff_pairwise_ne]
            exact T.attach.nodup_toList
          refine hnodup.imp ?_
          intro q1 q2 hq12
          have hl1 := (hchild_ih q1).1
          have hl2 := (hchild_ih q2).1
          rw [hl1, hl2]
          intro hcontra
          exact hq12 (Subtype.ext hcontra)
        · intro c hc
          rw [hchildren_def] at hc
          simp only [List.mem_map, Finset.mem_toList] at hc
          obtain ⟨q, _, hqc⟩ := hc
          rw [← hqc]
          exact (hchild_ih q).2.2.2.1
      · rw [hchildren_def]
        simp only [wtreesUpTo, Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
        refine ⟨T, hTsub, fun β hβ => WTree.canonicalizeFuel n ((WTree.mk i cs).childOf β hβ),
          ?_, rfl⟩
        rw [Finset.mem_pi]
        intro β hβ
        exact (hchild_ih ⟨β, hβ⟩).2.2.2.2

-- -------------------------------------------------------------------
-- Section 5: the result -- canonicalize embeds any WellFormed+Proper
-- tree, weight-preserved, into `wtreesUpTo`
-- -------------------------------------------------------------------

noncomputable def WTree.canonicalize (t : WTree ι) : WTree ι :=
  WTree.canonicalizeFuel (WTree.depth t) t

theorem WTree.canonicalize_mem_wtreesUpTo {V : Type} [DecidableEq V] {S : VarSpaces V} [Fintype ι]
    (P : MTProcess S ι) (p : ι → ℝ≥0) (t : WTree ι)
    (hwf : WTree.WellFormed P t) (hpr : WTree.Proper t) :
    (WTree.canonicalize t).label = t.label ∧
    (WTree.canonicalize t).weight p = t.weight p ∧
    (WTree.canonicalize t) ∈ wtreesUpTo P (WTree.depth t) t.label := by
  obtain ⟨h1, h2, _, _, h5⟩ := WTree.canonicalizeFuel_props P p (WTree.depth t) t hwf hpr le_rfl
  exact ⟨h1, h2, h5⟩

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @WTree.labelSet
#check @WTree.childOf
#check @WTree.childOf_mem
#check @WTree.childOf_label
#check @WTree.proper_nodup_labels
#check @WTree.proper_nodup_children
#check @WTree.eq_of_mem_children_label_eq
#check @WTree.childOf_eq_self_of_mem
#check @WTree.children_perm_labelSet_attach
#check @WTree.depth_lt_depthList
#check @WTree.depth_child_lt
#check @WTree.canonicalizeFuel
#check @WTree.canonicalizeFuel_props
#check @WTree.canonicalize
#check @WTree.canonicalize_mem_wtreesUpTo

-- -------------------------------------------------------------------
-- Section 6: canonicalize preserves the per-label occurrence count --
-- the invariant `τC_injective_on_occurrences` distinguishes trees by,
-- so injectivity survives conversion into `wtreesUpTo`'s world.
-- -------------------------------------------------------------------

mutual
def WTree.countLabel (A : ι) : WTree ι → ℕ
  | mk i cs => (if i = A then 1 else 0) + WTree.countLabelList A cs

def WTree.countLabelList (A : ι) : List (WTree ι) → ℕ
  | [] => 0
  | (c :: cs) => WTree.countLabel A c + WTree.countLabelList A cs
end

theorem WTree.countLabelList_eq_sum (A : ι) :
    ∀ cs : List (WTree ι), WTree.countLabelList A cs = (cs.map (WTree.countLabel A)).sum
  | [] => rfl
  | (c :: cs) => by
      simp only [WTree.countLabelList, List.map_cons, List.sum_cons]
      rw [WTree.countLabelList_eq_sum A cs]

theorem WTree.canonicalizeFuel_countLabel (A : ι) :
    ∀ n (t : WTree ι), WTree.Proper t → WTree.depth t ≤ n →
      WTree.countLabel A (WTree.canonicalizeFuel n t) = WTree.countLabel A t := by
  intro n
  induction n with
  | zero =>
    intro t hpr hd
    cases t with
    | mk i cs =>
      have hnil : cs = [] := by
        rcases cs with _ | ⟨c, cs'⟩
        · rfl
        · exfalso
          have hmem : c ∈ (c :: cs') := List.mem_cons_self
          have hlt := WTree.depth_lt_depthList (c :: cs') c hmem
          have hd' : WTree.depthList (c :: cs') ≤ 0 := hd
          omega
      subst hnil
      rfl
  | succ n ih =>
    intro t hpr hd
    cases t with
    | mk i cs =>
      have hpr2 : ∀ c ∈ cs, WTree.Proper c := by
        have h := hpr; unfold WTree.Proper at h; exact h.2
      set T := (WTree.mk i cs).labelSet with hTdef
      show WTree.countLabel A (WTree.mk i (T.attach.toList.map (fun q =>
          WTree.canonicalizeFuel n ((WTree.mk i cs).childOf q.1 q.2))))
        = WTree.countLabel A (WTree.mk i cs)
      simp only [WTree.countLabel]
      congr 1
      rw [WTree.countLabelList_eq_sum, WTree.countLabelList_eq_sum, List.map_map]
      have hstep : (T.attach.toList.map (WTree.countLabel A ∘ fun q =>
          WTree.canonicalizeFuel n ((WTree.mk i cs).childOf q.1 q.2)))
          = T.attach.toList.map (fun q => WTree.countLabel A ((WTree.mk i cs).childOf q.1 q.2)) := by
        apply List.map_congr_left
        intro q _
        show WTree.countLabel A (WTree.canonicalizeFuel n ((WTree.mk i cs).childOf q.1 q.2))
          = WTree.countLabel A ((WTree.mk i cs).childOf q.1 q.2)
        have hcmem := (WTree.mk i cs).childOf_mem q.1 q.2
        have hcpr := hpr2 _ hcmem
        have hcdepth : WTree.depth ((WTree.mk i cs).childOf q.1 q.2) ≤ n := by
          have hlt := (WTree.mk i cs).depth_child_lt _ hcmem
          have hd' : WTree.depth (WTree.mk i cs) ≤ n + 1 := hd
          omega
        exact ih _ hcpr hcdepth
      rw [hstep]
      have hperm := (WTree.mk i cs).children_perm_labelSet_attach hpr
      have hpermMapped := hperm.map (WTree.countLabel A)
      rw [List.map_map] at hpermMapped
      exact hpermMapped.sum_eq.symm

theorem WTree.canonicalize_countLabel (A : ι) (t : WTree ι) (hpr : WTree.Proper t) :
    WTree.countLabel A (WTree.canonicalize t) = WTree.countLabel A t :=
  WTree.canonicalizeFuel_countLabel A (WTree.depth t) t hpr le_rfl

#check @WTree.countLabel
#check @WTree.countLabelList_eq_sum
#check @WTree.canonicalizeFuel_countLabel
#check @WTree.canonicalize_countLabel

-- Explicit checks for all remaining helper theorems.
#check @WTree.mem_labelSet_iff
