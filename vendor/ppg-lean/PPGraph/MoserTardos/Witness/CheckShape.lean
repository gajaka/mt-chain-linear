/-
  PPGraphMoserTardosCheckShape.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), the entropy-compression
  assembly step: tauCheck depends only on the reconstructed tree's
  CANONICAL SHAPE, not on which GrowingTree (raw addresses) realizes it.

  This is the piece `PPGraphMoserTardosCheckInvariance.lean` built the
  foundation for (`GrowingTree.localCount_eq_footprintCountBeyondAt`,
  `WTree.canonicalize_footprintCountBeyond`): that file showed the
  tree-determined INDEX `localCount` is shape-only. This file lifts that
  to the CHECK itself (`tauCheck`/`checkState`'s bad-membership, not
  just the index), so that two GrowingTrees T1, T2 whose reconstructions
  canonicalize to the SAME WTree shape give the SAME tauCheck verdict on
  any fixed log omega. Combined with Theorem 5.7.2
  (`logMeasure_tauCheck_eq_prod_p`, proved for tau_C-built trees), this
  lets a UNION BOUND over the real, self-referential process's occurring
  trees be replaced by a union over `wtreesUpTo`'s fixed, address-free
  enumeration, one FIXED representative GrowingTree per shape, with no
  multiplicity.

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.MoserTardos.Witness.CheckInvariance
public import PPGraph.MoserTardos.Witness.Check

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- Section 1: a WTree-level check, mirroring `tauCheck`/`checkState`
-- exactly but reading `footprintCountBeyondAt` against a FIXED "whole"
-- tree (the true root) rather than an address-indexed `localCount` --
-- this is what makes the recursion able to carry the GLOBAL from-root
-- depth threshold correctly at every node, matching `localCount`'s own
-- "count over the WHOLE tree, not just descendants" semantics (see
-- `PPGraphMoserTardosCheckInvariance.lean`'s header).
-- -------------------------------------------------------------------

/-- The state the WTree-level check reconstructs at a node sitting at
    `curDepth` in `whole`: for each variable, read `omega` at the
    GLOBAL (whole-tree) count of deeper occurrences -- the WTree analogue
    of `checkState`. -/
noncomputable def WTree.checkStateAt {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (ω : LogSpace S) (whole : WTree ι) (curDepth : ℕ) : MTState S :=
  fun v => atIdx ω v (WTree.footprintCountBeyondAt P v curDepth 0 whole)

mutual
/-- WTree-level tau-check at one node `t`, sitting at `curDepth` inside
    `whole` (so `footprintCountBeyondAt` reads against `whole`, not `t`
    itself): the node's own label must be bad given the reconstructed
    state, AND every child (one depth deeper) must also check out. -/
def WTree.checkOK {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (ω : LogSpace S) (whole : WTree ι) (curDepth : ℕ) : WTree ι → Prop
  | WTree.mk i cs =>
      WTree.checkStateAt P ω whole curDepth ∈ P.bad i
        ∧ WTree.checkOKList P ω whole (curDepth + 1) cs

def WTree.checkOKList {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (ω : LogSpace S) (whole : WTree ι) (curDepth : ℕ) : List (WTree ι) → Prop
  | [] => True
  | (c :: cs) => WTree.checkOK P ω whole curDepth c ∧ WTree.checkOKList P ω whole curDepth cs
end

/-- The WTree-level tau-check on a whole tree: check it against itself,
    starting at depth 0. -/
def WTree.tauCheck {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (ω : LogSpace S) (t : WTree ι) : Prop :=
  WTree.checkOK P ω t 0 t

-- -------------------------------------------------------------------
-- Section 2: canonicalize-invariance of `checkOK`/`tauCheck` -- exactly
-- the SAME fuel-induction skeleton as `canonicalizeFuel_footprintCountBeyondAt`
-- (`PPGraphMoserTardosCheckInvariance.lean`), with the Prop-conjunction
-- carried via `List.Perm`'s pointwise-preserved-`And` (rather than
-- `List.Perm.sum_eq`).
-- -------------------------------------------------------------------

theorem WTree.checkOKList_iff_forall_mem {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (ω : LogSpace S) (whole : WTree ι) (curDepth : ℕ) :
    ∀ cs : List (WTree ι), WTree.checkOKList P ω whole curDepth cs
      ↔ ∀ c ∈ cs, WTree.checkOK P ω whole curDepth c
  | [] => by simp [WTree.checkOKList]
  | (c :: cs) => by
      simp only [WTree.checkOKList, List.mem_cons, forall_eq_or_imp]
      rw [WTree.checkOKList_iff_forall_mem P ω whole curDepth cs]

/-- General helper: if `P (f a) ↔ Q a` for every `a ∈ l`, then the
    universally-quantified statement over `l.map f` agrees with the one
    over `l` itself via `Q`. Purely combinatorial, no `WTree` content. -/
theorem list_forall_map_iff_pointwise {α β : Type} (l : List α) (f : α → β)
    (P : β → Prop) (Q : α → Prop) (h : ∀ a ∈ l, P (f a) ↔ Q a) :
    (∀ b ∈ l.map f, P b) ↔ (∀ a ∈ l, Q a) := by
  constructor
  · intro hall a ha
    exact (h a ha).mp (hall (f a) (List.mem_map_of_mem ha))
  · intro hall b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact (h a ha).mpr (hall a ha)

theorem WTree.canonicalizeFuel_checkOK {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (ω : LogSpace S) (whole : WTree ι) :
    ∀ n curDepth (t : WTree ι), WTree.Proper t → WTree.depth t ≤ n →
      (WTree.checkOK P ω whole curDepth (WTree.canonicalizeFuel n t)
        ↔ WTree.checkOK P ω whole curDepth t) := by
  intro n
  induction n with
  | zero =>
    intro curDepth t hpr hd
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
    intro curDepth t hpr hd
    cases t with
    | mk i cs =>
      have hpr2 : ∀ c ∈ cs, WTree.Proper c := by
        have h := hpr; unfold WTree.Proper at h; exact h.2
      set T := (WTree.mk i cs).labelSet with hTdef
      show WTree.checkOK P ω whole curDepth (WTree.mk i (T.attach.toList.map (fun q =>
          WTree.canonicalizeFuel n ((WTree.mk i cs).childOf q.1 q.2))))
        ↔ WTree.checkOK P ω whole curDepth (WTree.mk i cs)
      show (WTree.checkStateAt P ω whole curDepth ∈ P.bad i
          ∧ WTree.checkOKList P ω whole (curDepth + 1) (T.attach.toList.map (fun q =>
              WTree.canonicalizeFuel n ((WTree.mk i cs).childOf q.1 q.2))))
        ↔ (WTree.checkStateAt P ω whole curDepth ∈ P.bad i
            ∧ WTree.checkOKList P ω whole (curDepth + 1) cs)
      apply and_congr_right
      intro _
      rw [WTree.checkOKList_iff_forall_mem, WTree.checkOKList_iff_forall_mem]
      have hstepA : (∀ b ∈ T.attach.toList.map (fun q =>
              WTree.canonicalizeFuel n ((WTree.mk i cs).childOf q.1 q.2)),
            WTree.checkOK P ω whole (curDepth + 1) b)
          ↔ ∀ q ∈ T.attach.toList, WTree.checkOK P ω whole (curDepth + 1)
              ((WTree.mk i cs).childOf q.1 q.2) := by
        apply list_forall_map_iff_pointwise
        intro q _
        have hcmem := (WTree.mk i cs).childOf_mem q.1 q.2
        have hcpr := hpr2 _ hcmem
        have hcdepth : WTree.depth ((WTree.mk i cs).childOf q.1 q.2) ≤ n := by
          have hlt := (WTree.mk i cs).depth_child_lt _ hcmem
          have hd' : WTree.depth (WTree.mk i cs) ≤ n + 1 := hd
          omega
        exact ih (curDepth + 1) _ hcpr hcdepth
      rw [hstepA]
      have hperm := (WTree.mk i cs).children_perm_labelSet_attach hpr
      constructor
      · intro hall c hc
        obtain ⟨q, hq, hqeq⟩ := List.mem_map.mp (hperm.mem_iff.mp hc)
        rw [← hqeq]
        exact hall q hq
      · intro hall q hq
        exact hall _ (hperm.mem_iff.mpr (List.mem_map_of_mem hq))

theorem WTree.canonicalize_checkOK {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (ω : LogSpace S) (whole : WTree ι) (t : WTree ι) (hpr : WTree.Proper t) :
    WTree.checkOK P ω whole 0 (WTree.canonicalize t) ↔ WTree.checkOK P ω whole 0 t :=
  WTree.canonicalizeFuel_checkOK P ω whole (WTree.depth t) 0 t hpr le_rfl

-- -------------------------------------------------------------------
-- Section 3: `checkOK` doesn't care WHICH tree plays the role of
-- `whole` either, as long as it gives the same footprint counts at
-- every (variable, threshold) -- which `canonicalize_footprintCountBeyond`
-- already establishes for a tree and its own canonicalization. This is
-- what lets `whole` and the tree being walked be canonicalized
-- INDEPENDENTLY in the final cross-tree corollary below.
-- -------------------------------------------------------------------

mutual
theorem WTree.checkOK_whole_congr {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (ω : LogSpace S) (whole1 whole2 : WTree ι)
    (hagree : ∀ v threshold, WTree.footprintCountBeyondAt P v threshold 0 whole1
      = WTree.footprintCountBeyondAt P v threshold 0 whole2)
    (curDepth : ℕ) : ∀ t : WTree ι,
      WTree.checkOK P ω whole1 curDepth t ↔ WTree.checkOK P ω whole2 curDepth t
  | WTree.mk i cs => by
      show (WTree.checkStateAt P ω whole1 curDepth ∈ P.bad i
          ∧ WTree.checkOKList P ω whole1 (curDepth + 1) cs)
        ↔ (WTree.checkStateAt P ω whole2 curDepth ∈ P.bad i
            ∧ WTree.checkOKList P ω whole2 (curDepth + 1) cs)
      have hstate : WTree.checkStateAt P ω whole1 curDepth = WTree.checkStateAt P ω whole2 curDepth := by
        funext v
        show atIdx ω v (WTree.footprintCountBeyondAt P v curDepth 0 whole1)
          = atIdx ω v (WTree.footprintCountBeyondAt P v curDepth 0 whole2)
        rw [hagree v curDepth]
      rw [hstate]
      exact and_congr_right (fun _ =>
        WTree.checkOKList_whole_congr P ω whole1 whole2 hagree (curDepth + 1) cs)

theorem WTree.checkOKList_whole_congr {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (ω : LogSpace S) (whole1 whole2 : WTree ι)
    (hagree : ∀ v threshold, WTree.footprintCountBeyondAt P v threshold 0 whole1
      = WTree.footprintCountBeyondAt P v threshold 0 whole2)
    (curDepth : ℕ) : ∀ cs : List (WTree ι),
      WTree.checkOKList P ω whole1 curDepth cs ↔ WTree.checkOKList P ω whole2 curDepth cs
  | [] => Iff.rfl
  | (c :: cs) =>
      and_congr (WTree.checkOK_whole_congr P ω whole1 whole2 hagree curDepth c)
        (WTree.checkOKList_whole_congr P ω whole1 whole2 hagree curDepth cs)
end

-- -------------------------------------------------------------------
-- Section 4: the result -- `tauCheck` agrees for any two Proper WTrees
-- sharing the same canonical shape. This is the piece that lets the
-- entropy-compression union bound sum over CANONICAL SHAPES (one fixed
-- representative each) instead of over the real process's raw,
-- address-dependent occurring trees.
-- -------------------------------------------------------------------

theorem WTree.tauCheck_iff_tauCheck_canonicalize {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (ω : LogSpace S) (t : WTree ι) (hpr : WTree.Proper t) :
    WTree.tauCheck P ω t ↔ WTree.tauCheck P ω (WTree.canonicalize t) := by
  show WTree.checkOK P ω t 0 t ↔ WTree.checkOK P ω (WTree.canonicalize t) 0 (WTree.canonicalize t)
  have hagree : ∀ v threshold, WTree.footprintCountBeyondAt P v threshold 0 t
      = WTree.footprintCountBeyondAt P v threshold 0 (WTree.canonicalize t) := by
    intro v threshold
    exact (WTree.canonicalize_footprintCountBeyond P v threshold t hpr).symm
  calc WTree.checkOK P ω t 0 t
      ↔ WTree.checkOK P ω (WTree.canonicalize t) 0 t :=
        WTree.checkOK_whole_congr P ω t (WTree.canonicalize t) hagree 0 t
    _ ↔ WTree.checkOK P ω (WTree.canonicalize t) 0 (WTree.canonicalize t) :=
        (WTree.canonicalize_checkOK P ω (WTree.canonicalize t) t hpr).symm

/-- The result: `tauCheck` depends only on the CANONICAL SHAPE of
    the tree, not on which Proper `WTree` realizes it. Two witness-tree
    reconstructions with the same canonical shape give the SAME
    tau-check verdict on any fixed log `omega`. -/
theorem WTree.tauCheck_congr_of_canonicalize_eq {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (ω : LogSpace S) (t1 t2 : WTree ι)
    (hpr1 : WTree.Proper t1) (hpr2 : WTree.Proper t2)
    (hshape : WTree.canonicalize t1 = WTree.canonicalize t2) :
    WTree.tauCheck P ω t1 ↔ WTree.tauCheck P ω t2 := by
  rw [WTree.tauCheck_iff_tauCheck_canonicalize P ω t1 hpr1, hshape,
    ← WTree.tauCheck_iff_tauCheck_canonicalize P ω t2 hpr2]

#check @WTree.checkOK
#check @WTree.tauCheck
#check @WTree.canonicalizeFuel_checkOK
#check @WTree.canonicalize_checkOK
#check @WTree.checkOK_whole_congr
#check @WTree.tauCheck_congr_of_canonicalize_eq

-- Explicit checks for all remaining helper theorems.
#check @WTree.checkOKList_iff_forall_mem
#check @WTree.checkOKList_whole_congr
#check @WTree.tauCheck_iff_tauCheck_canonicalize
#check @list_forall_map_iff_pointwise
