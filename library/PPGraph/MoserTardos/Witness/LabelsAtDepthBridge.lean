/-
  PPGraphMoserTardosLabelsAtDepthBridge.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), piece (b)(ii): bridges
  the address-level `T.dom`'s own depth-`d` label multiset to the
  WTree-level `WTree.labelsAtDepth (T.toWTree []) d`
  (PPGraphMoserTardosWTreeToGrowingTree.lean), for an ARBITRARY Valid
  GrowingTree `T` -- mirroring `GrowingTree.toWTreeFuel_footprintCountBeyondAt`'s
  induction (PPGraphMoserTardosCheckInvariance.lean) and
  `GrowingTree.toWTreeFuel_countLabel`'s (PPGraphMoserTardosInjectivityBridge.lean),
  but for an EXACT depth match (not "beyond threshold", not "whole subtree"),
  and producing a Multiset (via `.val.map T.lab`) rather than a `Finset.card`.

  THIS is the piece flagged as genuinely needed (not the τCheck-event bridge,
  which is order-insensitive and separate) to transfer the REAL occurrence's
  already-proved address-level `SameDepthIndependent` down to a purely
  WTree-level `labelsAtDepth` fact, closing piece (b) of the entropy-compression
  "fixed representative" plan (PPGraphMoserTardosProbabilityGeneral.lean's
  header comment) via `WTree.toGrowingTree_sameDepthIndependent_of_labelsAtDepth`.

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.MoserTardos.Witness.CheckInvariance
public import PPGraph.MoserTardos.Witness.WTreeToGrowingTree

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- Section 1: a generic helper -- `labelsAtDepthChildren` over a mapped
-- list is the LIST-sum of `labelsAtDepth` over the mapped elements.
-- Trivial structural induction, no address content at all.
-- -------------------------------------------------------------------

theorem WTree.labelsAtDepthChildren_map_eq_sum {α ι : Type} (d : ℕ) (f : α → WTree ι) :
    ∀ (l : List α),
      WTree.labelsAtDepthChildren (l.map f) d = (l.map (fun a => WTree.labelsAtDepth (f a) d)).sum
  | [] => by simp [WTree.labelsAtDepthChildren]
  | (a :: l) => by
      show WTree.labelsAtDepth (f a) d + WTree.labelsAtDepthChildren (l.map f) d
        = ((f a |> fun c => WTree.labelsAtDepth c d) :: l.map (fun a => WTree.labelsAtDepth (f a) d)).sum
      rw [WTree.labelsAtDepthChildren_map_eq_sum d f l, List.sum_cons]

#check @WTree.labelsAtDepthChildren_map_eq_sum

-- -------------------------------------------------------------------
-- Section 2: the main bridge -- exact-depth address filter matches
-- `labelsAtDepth` on `toWTreeFuel`, for ANY Valid GrowingTree `T`.
-- -------------------------------------------------------------------

theorem GrowingTree.toWTreeFuel_labelsAtDepth {ι : Type} [DecidableEq ι]
    (T : GrowingTree ι) (hV : T.Valid) :
    ∀ d n x, x ∈ T.dom → (∀ w ∈ T.dom, w.length ≤ x.length + n) →
      WTree.labelsAtDepth (T.toWTreeFuel n x) d
        = (T.dom.filter (fun w => x <+: w ∧ w.length = x.length + d)).val.map T.lab := by
  intro d
  induction d with
  | zero =>
    intro n x hx hb
    have hset : T.dom.filter (fun w => x <+: w ∧ w.length = x.length + 0) = {x} := by
      apply Finset.ext
      intro w
      simp only [Finset.mem_filter, Finset.mem_singleton, Nat.add_zero]
      constructor
      · rintro ⟨_, hpre, hlen⟩
        exact (hpre.eq_of_length_le (by omega)).symm
      · intro heq
        rw [heq]
        exact ⟨hx, List.prefix_refl x, rfl⟩
    rw [hset]
    show WTree.labelsAtDepth (T.toWTreeFuel n x) 0 = ({x} : Finset (List ℕ)).val.map T.lab
    cases n with
    | zero =>
      show ({T.lab x} : Multiset ι) = ({x} : Finset (List ℕ)).val.map T.lab
      simp
    | succ n' =>
      show ({T.lab x} : Multiset ι) = ({x} : Finset (List ℕ)).val.map T.lab
      simp
  | succ d ih =>
    intro n x hx hb
    cases n with
    | zero =>
      have hempty : T.dom.filter (fun w => x <+: w ∧ w.length = x.length + (d + 1)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro w hw ⟨_, hlen⟩
        have := hb w hw
        omega
      rw [hempty]
      show WTree.labelsAtDepth (WTree.mk (T.lab x) []) (d + 1) = (∅ : Finset (List ℕ)).val.map T.lab
      show WTree.labelsAtDepthChildren [] d = (∅ : Finset (List ℕ)).val.map T.lab
      simp [WTree.labelsAtDepthChildren]
    | succ n' =>
      set children := T.dom.filter (fun w => ∃ k, w = x ++ [k]) with hchildren_def
      show WTree.labelsAtDepthChildren (children.toList.map (fun w => T.toWTreeFuel n' w)) d
        = (T.dom.filter (fun w => x <+: w ∧ w.length = x.length + (d + 1))).val.map T.lab
      rw [WTree.labelsAtDepthChildren_map_eq_sum d (fun w => T.toWTreeFuel n' w) children.toList]
      have hstep : (children.toList.map (fun w => WTree.labelsAtDepth (T.toWTreeFuel n' w) d))
          = children.toList.map (fun w =>
              (T.dom.filter (fun w' => w <+: w' ∧ w'.length = w.length + d)).val.map T.lab) := by
        apply List.map_congr_left
        intro w hw
        rw [hchildren_def, Finset.mem_toList, Finset.mem_filter] at hw
        obtain ⟨hwdom, k, hwk⟩ := hw
        have hbw : ∀ w' ∈ T.dom, w'.length ≤ w.length + n' := by
          intro w' hw'
          have hb' := hb w' hw'
          have hwlen : w.length = x.length + 1 := by rw [hwk]; simp
          omega
        exact ih n' w hwdom hbw
      rw [hstep]
      have hdisjoint : (children : Set (List ℕ)).PairwiseDisjoint
          (fun w => T.dom.filter (fun w' => w <+: w' ∧ w'.length = w.length + d)) := by
        intro w1 hw1 w2 hw2 hne
        simp only [Function.onFun, Finset.disjoint_left]
        intro w' hw1' hw2'
        simp only [Finset.mem_filter] at hw1' hw2'
        rw [hchildren_def, Finset.mem_coe, Finset.mem_filter] at hw1 hw2
        obtain ⟨_, k1, hk1⟩ := hw1
        obtain ⟨_, k2, hk2⟩ := hw2
        apply hne
        have hlen1 : w1.length = x.length + 1 := by rw [hk1]; simp
        have hlen2 : w2.length = x.length + 1 := by rw [hk2]; simp
        have hw1w2 : w1 <+: w2 :=
          List.prefix_of_prefix_length_le hw1'.2.1 hw2'.2.1 (by omega)
        exact hw1w2.eq_of_length_le (by omega)
      have hsplit : T.dom.filter (fun w => x <+: w ∧ w.length = x.length + (d + 1))
          = children.disjiUnion
              (fun w => T.dom.filter (fun w' => w <+: w' ∧ w'.length = w.length + d))
              hdisjoint := by
        apply Finset.ext
        intro w'
        simp only [Finset.mem_filter, Finset.mem_disjiUnion]
        constructor
        · rintro ⟨hw'dom, hpre, hlen⟩
          rcases eq_or_ne w' x with heq | hne
          · exfalso; subst heq; omega
          · obtain ⟨t, ht⟩ := hpre
            have ht_ne : t ≠ [] := by
              intro h; subst h; simp only [List.append_nil] at ht; exact hne ht.symm
            obtain ⟨k, t', htk⟩ := List.exists_cons_of_ne_nil ht_ne
            have hkey : (x ++ [k]) ++ t' = w' := by rw [← ht, htk]; simp [List.append_assoc]
            refine ⟨x ++ [k], ?_, hw'dom, ⟨t', hkey⟩, ?_⟩
            · rw [hchildren_def, Finset.mem_filter]
              exact ⟨GrowingTree.Valid.prefix_mem T hV w' hw'dom (x ++ [k]) ⟨t', hkey⟩, k, rfl⟩
            · have hxklen : (x ++ [k]).length = x.length + 1 := by simp
              omega
        · rintro ⟨w, hw, hw'dom, hpre, hlen⟩
          rw [hchildren_def, Finset.mem_filter] at hw
          obtain ⟨_, k, hwk⟩ := hw
          have hxw : x <+: w := by rw [hwk]; exact ⟨[k], rfl⟩
          have hwlen : w.length = x.length + 1 := by rw [hwk]; simp
          exact ⟨hw'dom, hxw.trans hpre, by omega⟩
      rw [hsplit, Finset.disjiUnion_val, Multiset.map_bind]
      show (children.toList.map fun w =>
            Multiset.map T.lab (T.dom.filter (fun w' => w <+: w' ∧ w'.length = w.length + d)).val).sum
        = (children.val.bind fun w =>
            Multiset.map T.lab (T.dom.filter (fun w' => w <+: w' ∧ w'.length = w.length + d)).val)
      rw [← Finset.coe_toList children]
      rfl

#check @GrowingTree.toWTreeFuel_labelsAtDepth

-- -------------------------------------------------------------------
-- Section 3: specialize at the root, matching
-- `GrowingTree.localCount_eq_footprintCountBeyondAt`'s shape.
-- -------------------------------------------------------------------

theorem GrowingTree.labelsAtDepth_toWTree_eq {ι : Type} [DecidableEq ι]
    (T : GrowingTree ι) (hV : T.Valid) (hroot : ([] : List ℕ) ∈ T.dom) (d : ℕ) :
    WTree.labelsAtDepth (T.toWTree []) d
      = (T.dom.filter (fun w => w.length = d)).val.map T.lab := by
  have hb : ∀ w' ∈ T.dom, w'.length ≤ ([] : List ℕ).length + T.dom.card := by
    intro w' hw'
    have := GrowingTree.Valid.length_lt_card T hV hw'
    simp only [List.length_nil, zero_add]
    omega
  have hkey := GrowingTree.toWTreeFuel_labelsAtDepth T hV d T.dom.card [] hroot hb
  simp only [List.length_nil, zero_add] at hkey
  have heq : T.dom.filter (fun w => ([] : List ℕ) <+: w ∧ w.length = d)
      = T.dom.filter (fun w => w.length = d) := by
    apply Finset.filter_congr
    intro w _
    simp only [List.nil_prefix, true_and]
  show WTree.labelsAtDepth (T.toWTreeFuel T.dom.card []) d
    = (T.dom.filter (fun w => w.length = d)).val.map T.lab
  rw [hkey, heq]

#check @GrowingTree.labelsAtDepth_toWTree_eq

-- -------------------------------------------------------------------
-- Section 4: piece (b) CLOSED -- any Valid GrowingTree T with a root
-- and address-level SameDepthIndependent gives SameDepthIndependent on
-- toGrowingTree(T.toWTree []), composing this file's bridge with
-- `WTree.toGrowingTree_sameDepthIndependent_of_labelsAtDepth`
-- (PPGraphMoserTardosWTreeToGrowingTree.lean). Applying this with
-- T := τC P (shiftedC P ω0 ω) t (whose SameDepthIndependent is already
-- proved via `τBuild_sameDepthIndependent`) is the last step needed for
-- the "fixed representative" plan.
-- -------------------------------------------------------------------

theorem GrowingTree.toWTree_sameDepthIndependent {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (T : GrowingTree ι) (hV : T.Valid) (hroot : ([] : List ℕ) ∈ T.dom)
    (hSDI : SameDepthIndependent P T) :
    SameDepthIndependent P (WTree.toGrowingTree (T.toWTree [])) := by
  apply WTree.toGrowingTree_sameDepthIndependent_of_labelsAtDepth
  · intro d
    rw [GrowingTree.labelsAtDepth_toWTree_eq T hV hroot d]
    have hNodupS : (T.dom.filter (fun w => w.length = d)).val.Nodup := (T.dom.filter _).nodup
    have hinj : ∀ w1 ∈ (T.dom.filter (fun w => w.length = d)).val,
        ∀ w2 ∈ (T.dom.filter (fun w => w.length = d)).val, T.lab w1 = T.lab w2 → w1 = w2 := by
      intro w1 hw1 w2 hw2 heq
      simp only [Finset.mem_val, Finset.mem_filter] at hw1 hw2
      by_contra hne
      exact (hSDI w1 w2 hw1.1 hw2.1 (hw1.2.trans hw2.2.symm) hne).1 heq
    exact Multiset.Nodup.map_on hinj hNodupS
  · intro d i j hi hj hij
    rw [GrowingTree.labelsAtDepth_toWTree_eq T hV hroot d] at hi hj
    rw [Multiset.mem_map] at hi hj
    obtain ⟨w1, hw1, hlab1⟩ := hi
    obtain ⟨w2, hw2, hlab2⟩ := hj
    simp only [Finset.mem_val, Finset.mem_filter] at hw1 hw2
    have hne : w1 ≠ w2 := by
      intro heq
      rw [heq] at hlab1
      exact hij (hlab1.symm.trans hlab2)
    have := (hSDI w1 w2 hw1.1 hw2.1 (hw1.2.trans hw2.2.symm) hne).2
    rwa [hlab1, hlab2] at this

#check @GrowingTree.toWTree_sameDepthIndependent

-- -------------------------------------------------------------------
-- Section 5: sanity corollary -- specialized to the REAL occurrence
-- τC P C t. This is the concrete instance the "fixed representative"
-- plan needs: a τC-independent-address GrowingTree, built directly
-- from τC's own WTree shape via `WTree.toGrowingTree`, inherits
-- SameDepthIndependent from the real trajectory it represents.
-- -------------------------------------------------------------------

theorem τC_toWTree_sameDepthIndependent {S : VarSpaces V} {ι : Type} [DecidableEq ι]
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) :
    SameDepthIndependent P (WTree.toGrowingTree ((τC P C t).toWTree [])) :=
  GrowingTree.toWTree_sameDepthIndependent P (τC P C t) (τC_valid P C t) (τC_root_mem P C t)
    (τBuild_sameDepthIndependent P C t (t - 1))

#check @τC_toWTree_sameDepthIndependent
