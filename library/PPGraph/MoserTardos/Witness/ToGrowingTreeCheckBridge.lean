/-
  PPGraphMoserTardosToGrowingTreeCheckBridge.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), the address-to-shape bridge
  specifically for `WTree.toGrowingTree` (PPGraphMoserTardosWTreeToGrowingTree.lean):
  for an ARBITRARY WTree `t` (no `tau_C`/`toWTreeFuel` roundtrip involved at all
  this time), the address-level `τCheck P (WTree.toGrowingTree t) ω` agrees with
  the purely-`t`-level `WTree.tauCheck P ω t`.

  This is the last piece needed before resuming the E[T_LOG] roadmap's step 3
  (`project_ppg_lean.md`, 2026-09-29 entry): step 3 needs Theorem 5.7.2 (stated
  at the address level) applied to a FIXED shape-representative `toGrowingTree T`,
  transporting a WTree-level fact about `T` down to that representative's own
  address-level `τCheck` -- exactly this bridge, in the τCheck ↔ tauCheck
  direction the other bridges (CheckBridge.lean, for τC-built trees) don't cover.

  Two independent pieces:
  1. `WTree.toGT_dom_footprintCountBeyondAt`: a `Finset.card` bridge between
     `footprintCountBeyondAt` (WTree-level, PPGraphMoserTardosCheckInvariance.lean)
     and a `toGT_dom`-filter (address-level). Mirrors
     `WTree.labelsAtDepth_eq_domFilter_map`'s mutual-induction SHAPE
     (PPGraphMoserTardosWTreeToGrowingTree.lean) -- same `toGT_dom`/`toGT_domChildren`
     recursion, same reused disjointness helpers -- but simpler to close since the
     target is `Finset.card` (`Finset.card_biUnion`, like the ORIGINAL
     `GrowingTree.toWTreeFuel_footprintCountBeyondAt`), not a `Multiset` equality
     (no `Finset.disjiUnion`/`Multiset.map_bind` needed).
  2. `WTree.checkOK_iff_toGT_dom`/`checkOKList_iff_toGT_domChildren`: a Prop
     bridge between `checkOK`/`checkOKList` (WTree-level,
     PPGraphMoserTardosCheckShape.lean) and `toGT_dom`/`toGT_domChildren`. This
     one does NOT need piece 1 at all -- it treats `checkStateAt` as an opaque
     function of its depth argument throughout, so it is a purely-structural
     Prop-conjunction bridge, exactly like `τC_toWTreeFuel_checkOK`'s shape but
     without any fuel/bound bookkeeping (structural recursion on the WTree
     itself, not a fuel-indexed reconstruction).

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.MoserTardos.Witness.WTreeToGrowingTree
public import PPGraph.MoserTardos.Witness.CheckInvariance
public import PPGraph.MoserTardos.Witness.CheckShape
public import PPGraph.MoserTardos.Witness.Check

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- Section 1: `footprintCountBeyondAt` (WTree-level) vs a `toGT_dom`
-- filter-card (address-level). Mirrors `toGT_dom`/`toGT_domChildren`'s
-- own mutual-recursion shape, reusing `toGT_domChildren_head_ge` /
-- `toGT_domChildren_head_disjoint` exactly as `labelsAtDepth_eq_domFilter_map`
-- did, but targeting `Finset.card` (`Finset.card_biUnion`) instead of a
-- `Multiset` equality.
--
-- `pd` ("parent depth") generalizes over how deep the CURRENT node `t`
-- sits, relative to whichever top-level call eventually specializes it
-- to 0 -- exactly how `GrowingTree.toWTreeFuel_footprintCountBeyondAt`
-- generalized over the starting address `x`.
-- -------------------------------------------------------------------

mutual
theorem WTree.toGT_dom_footprintCountBeyondAt {ι : Type} {S : VarSpaces V} (P : MTProcess S ι)
    (v : V) (d pd : ℕ) :
    ∀ t : WTree ι,
      WTree.footprintCountBeyondAt P v d pd t
        = ((WTree.toGT_dom t).filter (fun w => d < pd + w.length ∧ v ∈ P.footprint (WTree.toGT_lab t w))).card
  | WTree.mk i cs => by
      show (if d < pd ∧ v ∈ P.footprint i then 1 else 0)
          + WTree.footprintCountBeyondListAt P v d (pd + 1) cs
        = ((insert ([] : List ℕ) (WTree.toGT_domChildren cs 0)).filter
            (fun w => d < pd + w.length ∧ v ∈ P.footprint (WTree.toGT_lab (WTree.mk i cs) w))).card
      have hrootnotin : ([] : List ℕ) ∉ WTree.toGT_domChildren cs 0 := by
        intro hcontra
        have := WTree.toGT_domChildren_length_pos cs 0 [] hcontra
        simp at this
      have hsplit : (insert ([] : List ℕ) (WTree.toGT_domChildren cs 0)).filter
            (fun w => d < pd + w.length ∧ v ∈ P.footprint (WTree.toGT_lab (WTree.mk i cs) w))
          = (if d < pd + (0 : ℕ) ∧ v ∈ P.footprint (WTree.toGT_lab (WTree.mk i cs) ([] : List ℕ))
              then ({([] : List ℕ)} : Finset (List ℕ)) else ∅) ∪
            (WTree.toGT_domChildren cs 0).filter
              (fun w => d < pd + w.length ∧ v ∈ P.footprint (WTree.toGT_lab (WTree.mk i cs) w)) := by
        apply Finset.ext
        intro w
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
        constructor
        · rintro ⟨hw | hw, hcond⟩
          · subst hw
            by_cases hc : d < pd + (0:ℕ) ∧ v ∈ P.footprint (WTree.toGT_lab (WTree.mk i cs) ([] : List ℕ))
            · rw [ite_eq_left hc]; exact Or.inl (Finset.mem_singleton_self _)
            · exact absurd hcond hc
          · exact Or.inr ⟨hw, hcond⟩
        · rintro (h | ⟨hw, hcond⟩)
          · by_cases hc : d < pd + (0:ℕ) ∧ v ∈ P.footprint (WTree.toGT_lab (WTree.mk i cs) ([] : List ℕ))
            · rw [ite_eq_left hc] at h
              have hweq : w = [] := Finset.mem_singleton.mp h
              exact ⟨Or.inl hweq, hweq ▸ hc⟩
            · rw [ite_eq_right hc] at h
              exact absurd h (Finset.notMem_empty w)
          · exact ⟨Or.inr hw, hcond⟩
      rw [hsplit]
      have hdisj : Disjoint
          (if d < pd + (0:ℕ) ∧ v ∈ P.footprint (WTree.toGT_lab (WTree.mk i cs) ([] : List ℕ))
              then ({([] : List ℕ)} : Finset (List ℕ)) else ∅)
          ((WTree.toGT_domChildren cs 0).filter
              (fun w => d < pd + w.length ∧ v ∈ P.footprint (WTree.toGT_lab (WTree.mk i cs) w))) := by
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        by_cases hc : d < pd + (0:ℕ) ∧ v ∈ P.footprint (WTree.toGT_lab (WTree.mk i cs) ([] : List ℕ))
        · rw [ite_eq_left hc] at hw1
          have hweq : w = [] := Finset.mem_singleton.mp hw1
          rw [Finset.mem_filter] at hw2
          exact hrootnotin (hweq ▸ hw2.1)
        · rw [ite_eq_right hc] at hw1
          exact absurd hw1 (Finset.notMem_empty w)
      rw [Finset.card_union_of_disjoint hdisj]
      have hif : (if d < pd + (0:ℕ) ∧ v ∈ P.footprint (WTree.toGT_lab (WTree.mk i cs) ([] : List ℕ))
              then ({([] : List ℕ)} : Finset (List ℕ)) else ∅).card
          = if d < pd ∧ v ∈ P.footprint i then 1 else 0 := by
        show (if d < pd + (0:ℕ) ∧ v ∈ P.footprint i then ({([] : List ℕ)} : Finset (List ℕ)) else ∅).card
            = if d < pd ∧ v ∈ P.footprint i then 1 else 0
        by_cases hc : d < pd ∧ v ∈ P.footprint i
        · rw [ite_eq_left (by simpa using hc), ite_eq_left hc, Finset.card_singleton]
        · rw [ite_eq_right (by simpa using hc), ite_eq_right hc, Finset.card_empty]
      rw [hif]
      congr 1
      exact WTree.toGT_domChildren_footprintCountBeyondAt P v d pd (WTree.mk i cs) cs 0 rfl

theorem WTree.toGT_domChildren_footprintCountBeyondAt {ι : Type} {S : VarSpaces V}
    (P : MTProcess S ι) (v : V) (d pd : ℕ) (parent : WTree ι) :
    ∀ (cs : List (WTree ι)) (idx0 : ℕ), parent.children.drop idx0 = cs →
      WTree.footprintCountBeyondListAt P v d (pd + 1) cs
        = ((WTree.toGT_domChildren cs idx0).filter
            (fun w => d < pd + w.length ∧ v ∈ P.footprint (WTree.toGT_lab parent w))).card
  | [], idx0, _ => by simp [WTree.footprintCountBeyondListAt, WTree.toGT_domChildren]
  | (c :: cs), idx0, hsuffix => by
      obtain ⟨hget, hsuffix'⟩ :=
        List.getElem?_and_drop_succ_of_drop_eq_cons idx0 parent.children c cs hsuffix
      show WTree.footprintCountBeyondAt P v d (pd + 1) c
          + WTree.footprintCountBeyondListAt P v d (pd + 1) cs
        = (((WTree.toGT_dom c).image (fun a => idx0 :: a)
              ∪ WTree.toGT_domChildren cs (idx0 + 1)).filter
            (fun w => d < pd + w.length ∧ v ∈ P.footprint (WTree.toGT_lab parent w))).card
      have hdisj : Disjoint ((WTree.toGT_dom c).image (fun a => idx0 :: a))
          (WTree.toGT_domChildren cs (idx0 + 1)) :=
        WTree.toGT_domChildren_head_disjoint c cs idx0
      have hdisj' : Disjoint (((WTree.toGT_dom c).image (fun a => idx0 :: a)).filter
            (fun w => d < pd + w.length ∧ v ∈ P.footprint (WTree.toGT_lab parent w)))
          ((WTree.toGT_domChildren cs (idx0 + 1)).filter
            (fun w => d < pd + w.length ∧ v ∈ P.footprint (WTree.toGT_lab parent w))) :=
        hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      rw [Finset.filter_union, Finset.card_union_of_disjoint hdisj']
      congr 1
      · have hfilter : ((WTree.toGT_dom c).image (fun a => idx0 :: a)).filter
              (fun w => d < pd + w.length ∧ v ∈ P.footprint (WTree.toGT_lab parent w))
            = ((WTree.toGT_dom c).filter
                (fun a => d < (pd + 1) + a.length ∧ v ∈ P.footprint (WTree.toGT_lab c a))).image
              (fun a => idx0 :: a) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_image]
          constructor
          · rintro ⟨⟨a, ha, rfl⟩, hlen, hfp⟩
            simp only [List.length_cons] at hlen
            refine ⟨a, ⟨ha, by omega, ?_⟩, rfl⟩
            show v ∈ P.footprint (WTree.toGT_lab c a)
            have : WTree.toGT_lab c a = WTree.toGT_lab parent (idx0 :: a) := by
              simp [WTree.toGT_lab, hget]
            rw [this]; exact hfp
          · rintro ⟨a, ⟨ha, hlen, hfp⟩, rfl⟩
            refine ⟨⟨a, ha, rfl⟩, by simp only [List.length_cons]; omega, ?_⟩
            show v ∈ P.footprint (WTree.toGT_lab parent (idx0 :: a))
            have : WTree.toGT_lab parent (idx0 :: a) = WTree.toGT_lab c a := by
              simp [WTree.toGT_lab, hget]
            rw [this]; exact hfp
        rw [hfilter]
        have hinj : Set.InjOn (fun a => idx0 :: a)
            (((WTree.toGT_dom c).filter
                (fun a => d < (pd + 1) + a.length ∧ v ∈ P.footprint (WTree.toGT_lab c a))) : Set (List ℕ)) := by
          intro a _ b _ hab
          injection hab
        rw [Finset.card_image_of_injOn hinj]
        exact WTree.toGT_dom_footprintCountBeyondAt P v d (pd + 1) c
      · exact WTree.toGT_domChildren_footprintCountBeyondAt P v d pd parent cs (idx0 + 1) hsuffix'
end

/-- Specialized at the root (`pd = 0`), matching `footprintCountBeyondAt`'s own
    root-level usage in `WTree.checkStateAt`. -/
theorem WTree.toGT_dom_footprintCountBeyondAt_root {ι : Type} {S : VarSpaces V} (P : MTProcess S ι)
    (v : V) (d : ℕ) (t : WTree ι) :
    ((WTree.toGT_dom t).filter (fun w => d < w.length ∧ v ∈ P.footprint (WTree.toGT_lab t w))).card
      = WTree.footprintCountBeyondAt P v d 0 t := by
  have h := WTree.toGT_dom_footprintCountBeyondAt P v d 0 t
  simpa using h.symm

-- -------------------------------------------------------------------
-- Section 2: `checkOK`/`checkOKList` (WTree-level) vs `toGT_dom`/
-- `toGT_domChildren` (address-level). Purely structural -- treats
-- `checkStateAt` as an opaque function of its depth argument, no
-- dependence on Section 1 at all.
-- -------------------------------------------------------------------

mutual
theorem WTree.checkOK_iff_toGT_dom {ι : Type} {S : VarSpaces V} (P : MTProcess S ι)
    (ω : LogSpace S) (whole : WTree ι) (curDepth : ℕ) :
    ∀ t : WTree ι,
      WTree.checkOK P ω whole curDepth t
        ↔ ∀ w ∈ WTree.toGT_dom t, WTree.checkStateAt P ω whole (curDepth + w.length) ∈ P.bad (WTree.toGT_lab t w)
  | WTree.mk i cs => by
      constructor
      · rintro ⟨hself, hchildren⟩ w hw
        rcases Finset.mem_insert.mp hw with rfl | hw'
        · show WTree.checkStateAt P ω whole (curDepth + ([] : List ℕ).length) ∈ P.bad i
          simpa [WTree.toGT_lab] using hself
        · exact (WTree.checkOKList_iff_toGT_domChildren P ω whole curDepth (WTree.mk i cs) cs 0 rfl).mp
            hchildren w hw'
      · intro hall
        refine ⟨?_,
          (WTree.checkOKList_iff_toGT_domChildren P ω whole curDepth (WTree.mk i cs) cs 0 rfl).mpr
            (fun w hw => hall w (Finset.mem_insert_of_mem hw))⟩
        have h0 := hall [] (WTree.toGT_dom_root_mem (WTree.mk i cs))
        have heq0 : WTree.toGT_lab (WTree.mk i cs) ([] : List ℕ) = i := rfl
        rw [heq0] at h0
        simpa using h0

theorem WTree.checkOKList_iff_toGT_domChildren {ι : Type} {S : VarSpaces V} (P : MTProcess S ι)
    (ω : LogSpace S) (whole : WTree ι) (d0 : ℕ) (parent : WTree ι) :
    ∀ (cs : List (WTree ι)) (idx0 : ℕ), parent.children.drop idx0 = cs →
      (WTree.checkOKList P ω whole (d0 + 1) cs
        ↔ ∀ w ∈ WTree.toGT_domChildren cs idx0, WTree.checkStateAt P ω whole (d0 + w.length) ∈ P.bad (WTree.toGT_lab parent w))
  | [], idx0, _ => by simp [WTree.checkOKList, WTree.toGT_domChildren]
  | (c :: cs), idx0, hsuffix => by
      obtain ⟨hget, hsuffix'⟩ :=
        List.getElem?_and_drop_succ_of_drop_eq_cons idx0 parent.children c cs hsuffix
      show (WTree.checkOK P ω whole (d0 + 1) c ∧ WTree.checkOKList P ω whole (d0 + 1) cs)
        ↔ ∀ w ∈ (WTree.toGT_dom c).image (fun a => idx0 :: a) ∪ WTree.toGT_domChildren cs (idx0 + 1),
            WTree.checkStateAt P ω whole (d0 + w.length) ∈ P.bad (WTree.toGT_lab parent w)
      have hhead : WTree.checkOK P ω whole (d0 + 1) c
          ↔ ∀ w ∈ (WTree.toGT_dom c).image (fun a => idx0 :: a),
              WTree.checkStateAt P ω whole (d0 + w.length) ∈ P.bad (WTree.toGT_lab parent w) := by
        rw [WTree.checkOK_iff_toGT_dom P ω whole (d0 + 1) c]
        constructor
        · intro hc w hw
          rw [Finset.mem_image] at hw
          obtain ⟨a, ha, rfl⟩ := hw
          have hlab : WTree.toGT_lab c a = WTree.toGT_lab parent (idx0 :: a) := by
            simp [WTree.toGT_lab, hget]
          have heq : d0 + (idx0 :: a).length = (d0 + 1) + a.length := by
            simp only [List.length_cons]; omega
          have := hc a ha
          rw [hlab, ← heq] at this
          exact this
        · intro hall a ha
          have hw := hall (idx0 :: a) (Finset.mem_image_of_mem _ ha)
          have hlab : WTree.toGT_lab c a = WTree.toGT_lab parent (idx0 :: a) := by
            simp [WTree.toGT_lab, hget]
          have heq : d0 + (idx0 :: a).length = (d0 + 1) + a.length := by
            simp only [List.length_cons]; omega
          rw [← hlab, heq] at hw
          exact hw
      have htail : WTree.checkOKList P ω whole (d0 + 1) cs
          ↔ ∀ w ∈ WTree.toGT_domChildren cs (idx0 + 1),
              WTree.checkStateAt P ω whole (d0 + w.length) ∈ P.bad (WTree.toGT_lab parent w) :=
        WTree.checkOKList_iff_toGT_domChildren P ω whole d0 parent cs (idx0 + 1) hsuffix'
      rw [hhead, htail]
      constructor
      · rintro ⟨h1, h2⟩ w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact h1 w hw
        · exact h2 w hw
      · intro hall
        exact ⟨fun w hw => hall w (Finset.mem_union_left _ hw),
          fun w hw => hall w (Finset.mem_union_right _ hw)⟩
end

-- -------------------------------------------------------------------
-- Section 3: the result. `τCheck P (WTree.toGrowingTree t) ω` agrees
-- with `WTree.tauCheck P ω t`, for an ARBITRARY WTree `t` -- no
-- `τC`/`toWTreeFuel` roundtrip involved.
-- -------------------------------------------------------------------

/-- The `toGrowingTree` address-to-shape bridge. The address-indexed
    `τCheck` on the direct `WTree -> GrowingTree` embedding agrees with the
    purely-`t`-level `WTree.tauCheck`. Combined with
    `WTree.tauCheck_congr_of_canonicalize_eq` and the existing `τC`-side bridge
    (`τC_tauCheck_iff_WTree_tauCheck`, PPGraphMoserTardosCheckBridge.lean), this
    lets a WTree-level fact transported from the real occurrence come BACK DOWN
    to an address-level `τCheck` fact about a FIXED shape-representative
    `WTree.toGrowingTree T` -- exactly what the entropy-compression union
    bound's step 3 needs. -/
theorem WTree.τCheck_toGrowingTree_iff_tauCheck {V : Type} [DecidableEq V] {ι : Type}
    {S : VarSpaces V} (P : MTProcess S ι) (ω : LogSpace S) (t : WTree ι) :
    τCheck P (WTree.toGrowingTree t) ω ↔ WTree.tauCheck P ω t := by
  have hstateEq : ∀ w ∈ WTree.toGT_dom t,
      checkState P (WTree.toGrowingTree t) ω w = WTree.checkStateAt P ω t w.length := by
    intro w hw
    funext x
    show atIdx ω x (localCount P (WTree.toGrowingTree t) w x)
      = atIdx ω x (WTree.footprintCountBeyondAt P x w.length 0 t)
    show atIdx ω x (((WTree.toGT_dom t).filter
        (fun w' => w.length < w'.length ∧ x ∈ P.footprint (WTree.toGT_lab t w'))).card)
      = atIdx ω x (WTree.footprintCountBeyondAt P x w.length 0 t)
    rw [WTree.toGT_dom_footprintCountBeyondAt_root]
  have hkey := WTree.checkOK_iff_toGT_dom P ω t 0 t
  show (∀ w ∈ WTree.toGT_dom t, checkState P (WTree.toGrowingTree t) ω w ∈ P.bad (WTree.toGT_lab t w))
    ↔ WTree.checkOK P ω t 0 t
  rw [hkey]
  constructor
  · intro hall w hw
    rw [show (0:ℕ) + w.length = w.length from by omega, ← hstateEq w hw]
    exact hall w hw
  · intro hall w hw
    have := hall w hw
    rw [show (0:ℕ) + w.length = w.length from by omega] at this
    rw [hstateEq w hw]
    exact this

#check @WTree.toGT_dom_footprintCountBeyondAt
#check @WTree.toGT_domChildren_footprintCountBeyondAt
#check @WTree.toGT_dom_footprintCountBeyondAt_root
#check @WTree.checkOK_iff_toGT_dom
#check @WTree.checkOKList_iff_toGT_domChildren
#check @WTree.τCheck_toGrowingTree_iff_tauCheck
