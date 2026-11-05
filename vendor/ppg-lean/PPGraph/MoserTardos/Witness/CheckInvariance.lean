/-
  PPGraphMoserTardosCheckInvariance.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), the piece needed to
  connect the SELF-REFERENTIAL real trajectory (the scheduling function
  `shiftedC P ω0 ω` is itself a function of ω) to the FIXED-C enumeration
  `wtreesUpTo`/Theorem 5.7.2 -- the "entropy compression" step.

  The core fact: `localCount P T w v` (PPGraphMoserTardosCheck.lean) --
  hence `checkState`/`τCheck` -- depends only on the SHAPE of the
  reconstructed tree (which vertices, at which relative depths, carry
  which labels), NOT on which specific addresses realize that shape.
  So τCheck's truth value, and via Theorem 5.7.2 its probability, is a
  function of the CANONICAL shape alone -- letting us bound the real,
  self-referential process by a union over `wtreesUpTo`'s fixed,
  address-free enumeration WITHOUT any multiplicity/overcounting factor
  (a wrong path already ruled out this session: summing over raw label
  sequences overcounts, since many sequences collapse to the same shape
  via `attachAt`'s conditional no-op).

  Strategy: define a WTree-level, depth-thresholded occurrence count
  (`WTree.footprintCountBeyondAt`) that mirrors `WTree.countLabel`'s
  already-proved canonicalize-invariance pattern exactly (same
  permutation argument, `children_perm_labelSet_attach`), then bridge
  it to the GrowingTree-level `localCount` via the SAME induction shape
  as `GrowingTree.toWTreeFuel_countLabel` (PPGraphMoserTardosInjectivityBridge.lean).

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.MoserTardos.Witness.Check
public import PPGraph.MoserTardos.Witness.InjectivityBridge

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical
open scoped NNReal

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- Section 1: WTree-level depth-thresholded footprint count. `curDepth`
-- is the CURRENT node's depth (0 at the point the whole recursion
-- started); each recursive call into `cs` bumps it by 1 -- matching
-- how, on the GrowingTree side, a child address is one entry LONGER
-- than its parent's.
-- -------------------------------------------------------------------

mutual
def WTree.footprintCountBeyondAt {S : VarSpaces V} {ι : Type} (P : MTProcess S ι)
    (v : V) (threshold curDepth : ℕ) : WTree ι → ℕ
  | WTree.mk i cs =>
      (if threshold < curDepth ∧ v ∈ P.footprint i then 1 else 0)
        + WTree.footprintCountBeyondListAt P v threshold (curDepth + 1) cs

def WTree.footprintCountBeyondListAt {S : VarSpaces V} {ι : Type} (P : MTProcess S ι)
    (v : V) (threshold curDepth : ℕ) : List (WTree ι) → ℕ
  | [] => 0
  | (c :: cs) =>
      WTree.footprintCountBeyondAt P v threshold curDepth c
        + WTree.footprintCountBeyondListAt P v threshold curDepth cs
end

theorem WTree.footprintCountBeyondListAt_eq_sum {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (v : V) (threshold curDepth : ℕ) :
    ∀ cs : List (WTree ι), WTree.footprintCountBeyondListAt P v threshold curDepth cs
      = (cs.map (WTree.footprintCountBeyondAt P v threshold curDepth)).sum
  | [] => rfl
  | (c :: cs) => by
      simp only [WTree.footprintCountBeyondListAt, List.map_cons, List.sum_cons]
      rw [WTree.footprintCountBeyondListAt_eq_sum P v threshold curDepth cs]

-- -------------------------------------------------------------------
-- Section 2: canonicalize-invariance -- exactly `countLabel`'s proof
-- (PPGraphMoserTardosCanonical.lean), `curDepth` threaded through
-- unchanged (permutation of siblings doesn't touch it).
-- -------------------------------------------------------------------

theorem WTree.canonicalizeFuel_footprintCountBeyondAt {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (v : V) (threshold : ℕ) :
    ∀ n curDepth (t : WTree ι), WTree.Proper t → WTree.depth t ≤ n →
      WTree.footprintCountBeyondAt P v threshold curDepth (WTree.canonicalizeFuel n t)
        = WTree.footprintCountBeyondAt P v threshold curDepth t := by
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
      show WTree.footprintCountBeyondAt P v threshold curDepth (WTree.mk i (T.attach.toList.map (fun q =>
          WTree.canonicalizeFuel n ((WTree.mk i cs).childOf q.1 q.2))))
        = WTree.footprintCountBeyondAt P v threshold curDepth (WTree.mk i cs)
      simp only [WTree.footprintCountBeyondAt]
      congr 1
      rw [WTree.footprintCountBeyondListAt_eq_sum, WTree.footprintCountBeyondListAt_eq_sum, List.map_map]
      have hstep : (T.attach.toList.map (WTree.footprintCountBeyondAt P v threshold (curDepth + 1) ∘ fun q =>
          WTree.canonicalizeFuel n ((WTree.mk i cs).childOf q.1 q.2)))
          = T.attach.toList.map (fun q =>
              WTree.footprintCountBeyondAt P v threshold (curDepth + 1) ((WTree.mk i cs).childOf q.1 q.2)) := by
        apply List.map_congr_left
        intro q _
        show WTree.footprintCountBeyondAt P v threshold (curDepth + 1)
            (WTree.canonicalizeFuel n ((WTree.mk i cs).childOf q.1 q.2))
          = WTree.footprintCountBeyondAt P v threshold (curDepth + 1) ((WTree.mk i cs).childOf q.1 q.2)
        have hcmem := (WTree.mk i cs).childOf_mem q.1 q.2
        have hcpr := hpr2 _ hcmem
        have hcdepth : WTree.depth ((WTree.mk i cs).childOf q.1 q.2) ≤ n := by
          have hlt := (WTree.mk i cs).depth_child_lt _ hcmem
          have hd' : WTree.depth (WTree.mk i cs) ≤ n + 1 := hd
          omega
        exact ih (curDepth + 1) _ hcpr hcdepth
      rw [hstep]
      have hperm := (WTree.mk i cs).children_perm_labelSet_attach hpr
      have hpermMapped := hperm.map (WTree.footprintCountBeyondAt P v threshold (curDepth + 1))
      rw [List.map_map] at hpermMapped
      exact hpermMapped.sum_eq.symm

theorem WTree.canonicalize_footprintCountBeyond {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (v : V) (threshold : ℕ) (t : WTree ι) (hpr : WTree.Proper t) :
    WTree.footprintCountBeyondAt P v threshold 0 (WTree.canonicalize t)
      = WTree.footprintCountBeyondAt P v threshold 0 t :=
  WTree.canonicalizeFuel_footprintCountBeyondAt P v threshold (WTree.depth t) 0 t hpr le_rfl

-- -------------------------------------------------------------------
-- Section 3: bridge to the GrowingTree/address-level `localCount` --
-- exactly `GrowingTree.toWTreeFuel_countLabel`'s induction
-- (PPGraphMoserTardosInjectivityBridge.lean), with `T.lab w = A`
-- replaced by `threshold < w.length ∧ v ∈ P.footprint (T.lab w)`, and
-- `curDepth` carried as `x.length` (the address IS the depth-from-root
-- for a GrowingTree, so this generalizes over the starting vertex `x`
-- rather than fixing it at the true root).
-- -------------------------------------------------------------------

theorem GrowingTree.toWTreeFuel_footprintCountBeyondAt {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (T : GrowingTree ι) (hV : T.Valid) (v : V) (threshold : ℕ) :
    ∀ n x, x ∈ T.dom → (∀ w ∈ T.dom, w.length ≤ x.length + n) →
      WTree.footprintCountBeyondAt P v threshold x.length (T.toWTreeFuel n x)
        = (T.dom.filter (fun w => x <+: w ∧ threshold < w.length ∧ v ∈ P.footprint (T.lab w))).card := by
  intro n
  induction n with
  | zero =>
    intro x hx hb
    show (if threshold < x.length ∧ v ∈ P.footprint (T.lab x) then 1 else 0)
      = (T.dom.filter (fun w => x <+: w ∧ threshold < w.length ∧ v ∈ P.footprint (T.lab w))).card
    by_cases hcond : threshold < x.length ∧ v ∈ P.footprint (T.lab x)
    · rw [ite_eq_left hcond]
      have hset : T.dom.filter (fun w => x <+: w ∧ threshold < w.length ∧ v ∈ P.footprint (T.lab w)) = {x} := by
        apply Finset.ext
        intro w
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hwdom, hpre, _, _⟩
          have hb' := hb w hwdom
          exact (hpre.eq_of_length_le (by omega)).symm
        · intro heq
          rw [heq]
          exact ⟨hx, List.prefix_refl x, hcond⟩
      rw [hset, Finset.card_singleton]
    · rw [ite_eq_right hcond]
      have hset : T.dom.filter (fun w => x <+: w ∧ threshold < w.length ∧ v ∈ P.footprint (T.lab w)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro w hwdom hc
        obtain ⟨hpre, hlt, hfp⟩ := hc
        have hb' := hb w hwdom
        have hweq : x = w := hpre.eq_of_length_le (by omega)
        exact hcond (hweq ▸ ⟨hlt, hfp⟩)
      rw [hset, Finset.card_empty]
  | succ n ih =>
    intro x hx hb
    set children := T.dom.filter (fun w => ∃ k, w = x ++ [k]) with hchildren_def
    show (if threshold < x.length ∧ v ∈ P.footprint (T.lab x) then 1 else 0) +
        WTree.footprintCountBeyondListAt P v threshold (x.length + 1)
          (children.toList.map (fun w => T.toWTreeFuel n w))
      = (T.dom.filter (fun w => x <+: w ∧ threshold < w.length ∧ v ∈ P.footprint (T.lab w))).card
    rw [WTree.footprintCountBeyondListAt_eq_sum, List.map_map]
    have hstep : (children.toList.map (WTree.footprintCountBeyondAt P v threshold (x.length + 1)
          ∘ fun w => T.toWTreeFuel n w))
        = children.toList.map (fun w =>
            (T.dom.filter (fun w' => w <+: w' ∧ threshold < w'.length ∧ v ∈ P.footprint (T.lab w'))).card) := by
      apply List.map_congr_left
      intro w hw
      show WTree.footprintCountBeyondAt P v threshold (x.length + 1) (T.toWTreeFuel n w)
        = (T.dom.filter (fun w' => w <+: w' ∧ threshold < w'.length ∧ v ∈ P.footprint (T.lab w'))).card
      rw [hchildren_def, Finset.mem_toList, Finset.mem_filter] at hw
      obtain ⟨hwdom, k, hwk⟩ := hw
      have hwlen : w.length = x.length + 1 := by rw [hwk]; simp
      have hbw : ∀ w' ∈ T.dom, w'.length ≤ w.length + n := by
        intro w' hw'
        have hb' := hb w' hw'
        omega
      rw [← hwlen]
      exact ih w hwdom hbw
    rw [hstep]
    have hsplit : T.dom.filter (fun w => x <+: w ∧ threshold < w.length ∧ v ∈ P.footprint (T.lab w)) =
        (if threshold < x.length ∧ v ∈ P.footprint (T.lab x) then ({x} : Finset (List ℕ)) else ∅) ∪
          children.biUnion (fun u => T.dom.filter (fun w => u <+: w ∧ threshold < w.length ∧ v ∈ P.footprint (T.lab w))) := by
      apply Finset.ext
      intro w
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_biUnion]
      constructor
      · rintro ⟨hwdom, hpre, hlt, hfp⟩
        rcases eq_or_ne w x with heq | hne
        · left
          subst heq
          by_cases hcond : threshold < w.length ∧ v ∈ P.footprint (T.lab w)
          · rw [ite_eq_left hcond]; exact Finset.mem_singleton_self w
          · exact absurd ⟨hlt, hfp⟩ hcond
        · right
          obtain ⟨t, ht⟩ := hpre
          have ht_ne : t ≠ [] := by
            intro h
            subst h
            simp only [List.append_nil] at ht
            exact hne ht.symm
          obtain ⟨k, t', htk⟩ := List.exists_cons_of_ne_nil ht_ne
          have hkey : (x ++ [k]) ++ t' = w := by rw [← ht, htk]; simp [List.append_assoc]
          refine ⟨x ++ [k], ?_, hwdom, ⟨t', hkey⟩, hlt, hfp⟩
          rw [hchildren_def, Finset.mem_filter]
          exact ⟨GrowingTree.Valid.prefix_mem T hV w hwdom (x ++ [k]) ⟨t', hkey⟩, k, rfl⟩
      · rintro (h | ⟨u, hu, hwdom, hpre, hlt, hfp⟩)
        · by_cases hcond : threshold < x.length ∧ v ∈ P.footprint (T.lab x)
          · rw [ite_eq_left hcond] at h
            have hwx : w = x := Finset.mem_singleton.mp h
            subst hwx
            exact ⟨hx, List.prefix_refl w, hcond.1, hcond.2⟩
          · rw [ite_eq_right hcond] at h
            exact absurd h (Finset.notMem_empty w)
        · rw [hchildren_def, Finset.mem_filter] at hu
          obtain ⟨_, k, huk⟩ := hu
          refine ⟨hwdom, ?_, hlt, hfp⟩
          have hxu : x <+: u := by rw [huk]; exact ⟨[k], rfl⟩
          exact hxu.trans hpre
    rw [hsplit]
    have hdisjoint : (children : Set (List ℕ)).PairwiseDisjoint
        (fun u => T.dom.filter (fun w => u <+: w ∧ threshold < w.length ∧ v ∈ P.footprint (T.lab w))) := by
      intro u1 hu1 u2 hu2 hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro w hw1 hw2
      simp only [Finset.mem_filter] at hw1 hw2
      rw [hchildren_def, Finset.mem_coe, Finset.mem_filter] at hu1 hu2
      obtain ⟨_, k1, hk1⟩ := hu1
      obtain ⟨_, k2, hk2⟩ := hu2
      apply hne
      have hlen1 : u1.length = x.length + 1 := by rw [hk1]; simp
      have hlen2 : u2.length = x.length + 1 := by rw [hk2]; simp
      have hu1u2 : u1 <+: u2 := List.prefix_of_prefix_length_le hw1.2.1 hw2.2.1 (by omega)
      exact hu1u2.eq_of_length_le (by omega)
    have hunioncard : ((if threshold < x.length ∧ v ∈ P.footprint (T.lab x) then ({x} : Finset (List ℕ)) else ∅) ∪
        children.biUnion (fun u => T.dom.filter (fun w => u <+: w ∧ threshold < w.length ∧ v ∈ P.footprint (T.lab w)))).card
        = (if threshold < x.length ∧ v ∈ P.footprint (T.lab x) then ({x} : Finset (List ℕ)) else ∅).card +
          (children.biUnion (fun u => T.dom.filter (fun w => u <+: w ∧ threshold < w.length ∧ v ∈ P.footprint (T.lab w)))).card := by
      apply Finset.card_union_of_disjoint
      simp only [Finset.disjoint_left]
      intro w hw1 hw2
      simp only [Finset.mem_biUnion] at hw2
      obtain ⟨u, hu, hw2'⟩ := hw2
      simp only [Finset.mem_filter] at hw2'
      rw [hchildren_def, Finset.mem_filter] at hu
      obtain ⟨_, k, huk⟩ := hu
      by_cases hcond : threshold < x.length ∧ v ∈ P.footprint (T.lab x)
      · rw [ite_eq_left hcond] at hw1
        have hwx : w = x := Finset.mem_singleton.mp hw1
        have hulew : u.length ≤ w.length := hw2'.2.1.length_le
        have hulen : u.length = x.length + 1 := by rw [huk]; simp
        have hwxlen : w.length = x.length := by rw [hwx]
        omega
      · rw [ite_eq_right hcond] at hw1
        exact absurd hw1 (Finset.notMem_empty w)
    rw [hunioncard, Finset.card_biUnion hdisjoint]
    have hif : (if threshold < x.length ∧ v ∈ P.footprint (T.lab x) then ({x} : Finset (List ℕ)) else ∅).card
        = if threshold < x.length ∧ v ∈ P.footprint (T.lab x) then 1 else 0 := by
      by_cases hcond : threshold < x.length ∧ v ∈ P.footprint (T.lab x)
      · rw [ite_eq_left hcond, ite_eq_left hcond, Finset.card_singleton]
      · rw [ite_eq_right hcond, ite_eq_right hcond, Finset.card_empty]
    rw [hif]
    congr 1
    rw [hchildren_def]
    exact toList_map_sum _ _

-- -------------------------------------------------------------------
-- Section 4: specialize at the root -- `localCount` (address-level,
-- PPGraphMoserTardosCheck.lean) matches `footprintCountBeyondAt` on
-- the FULL reconstruction from the root, threshold = the queried
-- vertex's own length.
-- -------------------------------------------------------------------

theorem GrowingTree.localCount_eq_footprintCountBeyondAt {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (T : GrowingTree ι) (hV : T.Valid) (w : List ℕ) (v : V)
    (hw : w ∈ T.dom) (hroot : ([] : List ℕ) ∈ T.dom) :
    localCount P T w v = WTree.footprintCountBeyondAt P v w.length 0 (T.toWTree []) := by
  have hb : ∀ w' ∈ T.dom, w'.length ≤ ([] : List ℕ).length + T.dom.card := by
    intro w' hw'
    have := GrowingTree.Valid.length_lt_card T hV hw'
    simp only [List.length_nil, zero_add]
    omega
  have hkey := GrowingTree.toWTreeFuel_footprintCountBeyondAt P T hV v w.length T.dom.card [] hroot hb
  simp only [List.length_nil] at hkey
  have heq : T.dom.filter (fun w' => ([] : List ℕ) <+: w' ∧ w.length < w'.length ∧ v ∈ P.footprint (T.lab w'))
      = T.dom.filter (fun w' => w.length < w'.length ∧ v ∈ P.footprint (T.lab w')) := by
    apply Finset.filter_congr
    intro w' _
    simp only [List.nil_prefix, true_and]
  show localCount P T w v = WTree.footprintCountBeyondAt P v w.length 0 (T.toWTreeFuel T.dom.card [])
  rw [hkey, heq]
  rfl

#check @WTree.footprintCountBeyondAt
#check @WTree.canonicalize_footprintCountBeyond
#check @GrowingTree.toWTreeFuel_footprintCountBeyondAt
#check @GrowingTree.localCount_eq_footprintCountBeyondAt

-- Explicit checks for all remaining helper theorems.
#check @WTree.canonicalizeFuel_footprintCountBeyondAt
#check @WTree.footprintCountBeyondListAt_eq_sum
