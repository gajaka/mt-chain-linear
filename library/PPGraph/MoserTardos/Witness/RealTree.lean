/-
  PPGraphMoserTardosRealTree.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos).

  The GrowingTree -> WTree bridge: real τ_C(t) trees (the address-indexed
  GrowingTree from PPGraphMoserTardosGrowing.lean) genuinely embed as
  WellFormed + Proper WTrees (PPGraphMoserTardosWitness.lean), matching
  the abstract enumeration wtreesUpTo (PPGraphMoserTardosWeightSum.lean).

  Both hard combinatorial facts this needs were already fully proved
  elsewhere in address form: the "child" condition from
  PPGraphMoserTardosCheckBirth.lean's birth-step machinery, and the
  "siblings" condition directly from τBuild_sameDepthIndependent
  (PPGraphMoserTardosCheckOrder.lean, Moser-Tardos Lemma 2.1(i)). This
  file's genuinely new content is (1) the rose-tree reconstruction
  itself (toWTreeFuel) and (2) threading those two address-level facts
  through it into WTree.WellFormed / WTree.Proper.

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.MoserTardos.Bounds.WeightSum
public import PPGraph.MoserTardos.Witness.CheckBirth
public import PPGraph.MoserTardos.Witness.CheckOrder

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- Section 1: GrowingTree.Valid is preserved by attachAt / τBuild
-- -------------------------------------------------------------------

theorem GrowingTree.attachAt_preserves_valid {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (a : ι) (hV : T.Valid) :
    (T.attachAt P a).Valid := by
  unfold GrowingTree.attachAt
  split
  · rename_i h
    have hchosen_mem := (Classical.choose_spec (exists_max_depth_candidate (T.candidates P a) h)).1
    have hchosen_dom : (Classical.choose (exists_max_depth_candidate (T.candidates P a) h)) ∈ T.dom :=
      ((mem_candidates_iff P T a _).mp hchosen_mem).1
    exact T.attachChild_preserves_valid _ a hchosen_dom hV
  · exact hV

theorem τBuild_valid {S : VarSpaces V} {ι : Type} (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) :
    ∀ n, (τBuild P C t n).Valid
  | 0 => GrowingTree.singleton_valid (C t)
  | (n + 1) => GrowingTree.attachAt_preserves_valid P (τBuild P C t n) (C (t - 1 - n)) (τBuild_valid P C t n)

theorem τC_valid {S : VarSpaces V} {ι : Type} (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) :
    (τC P C t).Valid :=
  τBuild_valid P C t (t - 1)

-- -------------------------------------------------------------------
-- Section 2: prefix-closed domains have address length < card
-- -------------------------------------------------------------------

theorem GrowingTree.Valid.exists_prefix_finset {ι : Type} (T : GrowingTree ι) (hV : T.Valid) :
    ∀ w, w ∈ T.dom →
      ∃ s : Finset (List ℕ), s ⊆ T.dom ∧ s.card = w.length + 1 ∧ ∀ x ∈ s, x.length ≤ w.length := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro hw
    exact ⟨{[]}, by simpa using hw, by simp, by simp⟩
  | append_singleton l a ih =>
    intro hw
    have hl : l ∈ T.dom := hV.2 l a hw
    obtain ⟨s0, hs0sub, hs0card, hs0len⟩ := ih hl
    refine ⟨insert (l ++ [a]) s0, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hw
      · exact hs0sub hx
    · have hnotmem : (l ++ [a]) ∉ s0 := by
        intro hmem
        have hle := hs0len _ hmem
        simp at hle
      rw [Finset.card_insert_of_notMem hnotmem, hs0card]
      simp
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp
      · have := hs0len x hx
        simp only [List.length_append, List.length_singleton]
        omega

theorem GrowingTree.Valid.length_lt_card {ι : Type} (T : GrowingTree ι) (hV : T.Valid)
    {w : List ℕ} (hw : w ∈ T.dom) : w.length < T.dom.card := by
  obtain ⟨s, hsub, hcard, _⟩ := GrowingTree.Valid.exists_prefix_finset T hV w hw
  have := Finset.card_le_card hsub
  omega

-- -------------------------------------------------------------------
-- Section 3: address-level WellFormed / Proper facts for τC
-- -------------------------------------------------------------------

/-- A child address's label is compatible with its parent's, in the
    WellFormed sense -- derived purely from `attachAt`'s candidate
    condition at the child's own birth step, via the birth-step
    machinery already built in PPGraphMoserTardosCheckBirth.lean. -/
theorem τC_child_wellformed {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (u : List ℕ) (k : ℕ)
    (hu : u ∈ (τC P C t).dom) (hc : u ++ [k] ∈ (τC P C t).dom) :
    (τC P C t).lab u = (τC P C t).lab (u ++ [k]) ∨
      neighbor P ((τC P C t).lab u) ((τC P C t).lab (u ++ [k])) := by
  have hcne : u ++ [k] ≠ [] := by simp
  have hb0 : birthStep P C t (u ++ [k]) hc ≠ 0 := fun h0 =>
    hcne ((birthStep_eq_zero_iff P C t (u ++ [k]) hc).mp h0)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hb0
  rw [Nat.succ_eq_add_one] at hm
  have hcand := candidates_nonempty_of_birthStep_eq_succ P C t (u ++ [k]) hc m hm
  have hceq := eq_newAttachAddr_of_birthStep_eq_succ P C t (u ++ [k]) hc m hm hcand
  have hceq_unfold : u ++ [k] = Classical.choose
        (exists_max_depth_candidate ((τBuild P C t m).candidates P (C (t - 1 - m))) hcand)
      ++ [(τBuild P C t m).freshIndex (Classical.choose
        (exists_max_depth_candidate ((τBuild P C t m).candidates P (C (t - 1 - m))) hcand))] :=
    hceq
  have hueq := (list_concat_inj hceq_unfold).1
  have hchosen_mem := (Classical.choose_spec
    (exists_max_depth_candidate ((τBuild P C t m).candidates P (C (t - 1 - m))) hcand)).1
  have hchosen_lab := (mem_candidates_iff P (τBuild P C t m) (C (t - 1 - m)) _).mp hchosen_mem
  have hu_mem_m : u ∈ (τBuild P C t m).dom := by rw [hueq]; exact hchosen_lab.1
  have hulab_m : (τBuild P C t m).lab u = C (t - 1 - m) ∨
      neighbor P ((τBuild P C t m).lab u) (C (t - 1 - m)) := by
    rw [hueq]; exact hchosen_lab.2
  have hulab_final : (τBuild P C t m).lab u = (τC P C t).lab u :=
    τBuild_lab_eq_final P C t u hu m hu_mem_m
  have hclab_succ : (τBuild P C t (m + 1)).lab (u ++ [k]) = C (t - 1 - m) := by
    rw [hceq]
    exact attachAt_lab_new_addr P (τBuild P C t m) (C (t - 1 - m)) hcand
  have hc_mem_succ : u ++ [k] ∈ (τBuild P C t (m + 1)).dom := by
    rw [hceq]; exact newAttachAddr_mem_attachAt_dom P (τBuild P C t m) (C (t - 1 - m)) hcand
  have hclab_final : (τBuild P C t (m + 1)).lab (u ++ [k]) = (τC P C t).lab (u ++ [k]) :=
    τBuild_lab_eq_final P C t (u ++ [k]) hc (m + 1) hc_mem_succ
  rw [← hulab_final, ← hclab_final, hclab_succ]
  exact hulab_m

/-- Siblings (children of the same parent address) always carry
    distinct labels -- Moser-Tardos Lemma 2.1(i)'s conclusion,
    specialized from same-depth to same-parent, which is the exact
    shape `WTree.Proper` needs. -/
theorem τC_siblings_proper {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (v : List ℕ) (k1 k2 : ℕ) (hne : k1 ≠ k2)
    (h1 : v ++ [k1] ∈ (τC P C t).dom) (h2 : v ++ [k2] ∈ (τC P C t).dom) :
    (τC P C t).lab (v ++ [k1]) ≠ (τC P C t).lab (v ++ [k2]) := by
  have hlenq : (v ++ [k1]).length = (v ++ [k2]).length := by simp
  have hwne : v ++ [k1] ≠ v ++ [k2] := fun heq => hne (list_concat_inj heq).2
  exact (τBuild_sameDepthIndependent P C t (t - 1) (v ++ [k1]) (v ++ [k2]) h1 h2 hlenq hwne).1

-- -------------------------------------------------------------------
-- Section 4: the rose-tree reconstruction
-- -------------------------------------------------------------------

/-- Reconstruct the plain rose-tree `WTree` shape from an address-indexed
    `GrowingTree`, rooted at `v`, using `n` as a fuel bound on remaining
    depth. Any `n` at least as large as the deepest address below `v`
    gives the genuine, correct subtree -- extra fuel is harmless since
    the children filter is empty past the real leaves regardless. -/
noncomputable def GrowingTree.toWTreeFuel {ι : Type} (T : GrowingTree ι) : ℕ → List ℕ → WTree ι
  | 0, v => WTree.mk (T.lab v) []
  | (n + 1), v =>
      WTree.mk (T.lab v)
        ((T.dom.filter (fun w => ∃ k, w = v ++ [k])).toList.map (fun w => T.toWTreeFuel n w))

/-- The canonical choice of fuel, `T.dom.card`, is always enough (see
    `GrowingTree.Valid.length_lt_card`). -/
noncomputable def GrowingTree.toWTree {ι : Type} (T : GrowingTree ι) (v : List ℕ) : WTree ι :=
  T.toWTreeFuel T.dom.card v

theorem WTree.depthList_le {ι : Type} :
    ∀ (l : List (WTree ι)) (n : ℕ), (∀ c ∈ l, WTree.depth c ≤ n) → WTree.depthList l ≤ n + 1
  | [], n, _ => by simp [WTree.depthList]
  | (c :: cs), n, h => by
      simp only [WTree.depthList]
      have h1 : WTree.depth c ≤ n := h c List.mem_cons_self
      have h2 : WTree.depthList cs ≤ n + 1 :=
        WTree.depthList_le cs n (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
      exact Nat.max_le.mpr ⟨by omega, h2⟩

-- -------------------------------------------------------------------
-- Section 5: toWTreeFuel is WellFormed + Proper, with the right label
-- and depth bound, for τC-produced trees
-- -------------------------------------------------------------------

theorem τC_toWTreeFuel_props {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) :
    ∀ n v, v ∈ (τC P C t).dom → (∀ w ∈ (τC P C t).dom, w.length ≤ v.length + n) →
      ((τC P C t).toWTreeFuel n v).label = (τC P C t).lab v ∧
      WTree.WellFormed P ((τC P C t).toWTreeFuel n v) ∧
      WTree.Proper ((τC P C t).toWTreeFuel n v) ∧
      ((τC P C t).toWTreeFuel n v).depth ≤ n := by
  intro n
  induction n with
  | zero =>
    intro v hv _
    refine ⟨rfl, WTree.wellFormed_singleton P _, WTree.proper_singleton _, ?_⟩
    show WTree.depth (WTree.mk ((τC P C t).lab v) []) ≤ 0
    rfl
  | succ n ih =>
    intro v hv hb
    set children := ((τC P C t).dom.filter (fun w => ∃ k, w = v ++ [k])) with hchildren
    show
      (WTree.mk ((τC P C t).lab v)
        (children.toList.map (fun w => (τC P C t).toWTreeFuel n w))).label
          = (τC P C t).lab v ∧
      WTree.WellFormed P (WTree.mk ((τC P C t).lab v)
        (children.toList.map (fun w => (τC P C t).toWTreeFuel n w))) ∧
      WTree.Proper (WTree.mk ((τC P C t).lab v)
        (children.toList.map (fun w => (τC P C t).toWTreeFuel n w))) ∧
      (WTree.mk ((τC P C t).lab v)
        (children.toList.map (fun w => (τC P C t).toWTreeFuel n w))).depth ≤ n + 1
    have hchild_ih : ∀ w ∈ children, w ∈ (τC P C t).dom ∧
        ((τC P C t).toWTreeFuel n w).label = (τC P C t).lab w ∧
        WTree.WellFormed P ((τC P C t).toWTreeFuel n w) ∧
        WTree.Proper ((τC P C t).toWTreeFuel n w) ∧
        ((τC P C t).toWTreeFuel n w).depth ≤ n := by
      intro w hw
      rw [hchildren, Finset.mem_filter] at hw
      obtain ⟨hwdom, k, hwk⟩ := hw
      have hbw : ∀ w' ∈ (τC P C t).dom, w'.length ≤ w.length + n := by
        intro w' hw'
        have hb' := hb w' hw'
        rw [hwk]
        simp only [List.length_append, List.length_singleton]
        omega
      obtain ⟨hlbl, hwf, hpr, hd⟩ := ih w hwdom hbw
      exact ⟨hwdom, hlbl, hwf, hpr, hd⟩
    unfold WTree.WellFormed WTree.Proper
    refine ⟨rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨w, hw, hwc⟩ := hc
      rw [Finset.mem_toList] at hw
      obtain ⟨hwdom, hlbl, _, _, _⟩ := hchild_ih w hw
      have hwmem := hw
      rw [hchildren, Finset.mem_filter] at hwmem
      obtain ⟨_, k, hwk⟩ := hwmem
      have hkey := τC_child_wellformed P C t v k hv (hwk ▸ hwdom)
      rw [← hwc, hlbl, hwk]
      rcases hkey with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    · intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨w, hw, hwc⟩ := hc
      rw [Finset.mem_toList] at hw
      obtain ⟨_, _, hwf, _, _⟩ := hchild_ih w hw
      rwa [← hwc]
    · rw [List.pairwise_map]
      have hnodup : children.toList.Pairwise (· ≠ ·) := by
        rw [← List.nodup_iff_pairwise_ne]
        exact children.nodup_toList
      refine hnodup.imp_of_mem ?_
      intro w1 w2 hw1 hw2 hwne
      have hw1' : w1 ∈ children := Finset.mem_toList.mp hw1
      have hw2' : w2 ∈ children := Finset.mem_toList.mp hw2
      obtain ⟨hlbl1, _, _, _⟩ := (hchild_ih w1 hw1').2
      obtain ⟨hlbl2, _, _, _⟩ := (hchild_ih w2 hw2').2
      rw [hchildren, Finset.mem_filter] at hw1' hw2'
      obtain ⟨hw1dom, k1, hwk1⟩ := hw1'
      obtain ⟨hw2dom, k2, hwk2⟩ := hw2'
      have hk12 : k1 ≠ k2 := by
        intro heq
        exact hwne (by rw [hwk1, hwk2, heq])
      rw [hlbl1, hlbl2, hwk1, hwk2]
      exact τC_siblings_proper P C t v k1 k2 hk12 (hwk1 ▸ hw1dom) (hwk2 ▸ hw2dom)
    · intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨w, hw, hwc⟩ := hc
      rw [Finset.mem_toList] at hw
      obtain ⟨_, _, _, hpr, _⟩ := hchild_ih w hw
      rwa [← hwc]
    · show WTree.depth (WTree.mk ((τC P C t).lab v)
        (children.toList.map (fun w => (τC P C t).toWTreeFuel n w))) ≤ n + 1
      show WTree.depthList (children.toList.map (fun w => (τC P C t).toWTreeFuel n w)) ≤ n + 1
      apply WTree.depthList_le
      intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨w, hw, hwc⟩ := hc
      rw [Finset.mem_toList] at hw
      obtain ⟨_, _, _, _, hd⟩ := hchild_ih w hw
      rwa [← hwc]

-- -------------------------------------------------------------------
-- Section 6: wiring up the root -- toWTree of τC is WellFormed +
-- Proper, rooted at C t, with depth bounded by dom.card
-- -------------------------------------------------------------------

theorem τBuild_root_mem {S : VarSpaces V} {ι : Type} (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) :
    ∀ n, ([] : List ℕ) ∈ (τBuild P C t n).dom
  | 0 => by simp [τBuild, GrowingTree.singleton]
  | (n + 1) => dom_subset_attachAt P (τBuild P C t n) (C (t - 1 - n)) (τBuild_root_mem P C t n)

theorem τC_root_mem {S : VarSpaces V} {ι : Type} (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) :
    ([] : List ℕ) ∈ (τC P C t).dom :=
  τBuild_root_mem P C t (t - 1)

theorem τC_root_label {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) :
    (τC P C t).lab [] = C t := by
  have hroot := τC_root_mem P C t
  have hb0 := birthStep_root P C t hroot
  have hbl := birth_label P C t [] hroot
  unfold birthTime at hbl
  rw [hb0] at hbl
  simpa using hbl

/-- The result: `τC P C t`'s address representation genuinely embeds as
    a WellFormed + Proper WTree rooted at `C t` -- matching exactly the
    conditions `wtreesUpTo` (PPGraphMoserTardosWeightSum.lean)
    enumerates. This is the tree-representation gap flagged as future
    work both in PPGraphMoserTardosGrowing.lean's own file docstring
    and in the Theorem 5.7.2 probability-half session notes. -/
theorem τC_toWTree_wellFormed_proper {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) :
    ((τC P C t).toWTree []).label = C t ∧
    WTree.WellFormed P ((τC P C t).toWTree []) ∧
    WTree.Proper ((τC P C t).toWTree []) ∧
    ((τC P C t).toWTree []).depth ≤ (τC P C t).dom.card := by
  have hroot := τC_root_mem P C t
  have hb : ∀ w ∈ (τC P C t).dom, w.length ≤ ([] : List ℕ).length + (τC P C t).dom.card := by
    intro w hw
    have := GrowingTree.Valid.length_lt_card (τC P C t) (τC_valid P C t) hw
    simp only [List.length_nil, zero_add]
    omega
  obtain ⟨hlbl, hwf, hpr, hd⟩ :=
    τC_toWTreeFuel_props P C t (τC P C t).dom.card [] hroot hb
  refine ⟨?_, hwf, hpr, hd⟩
  show ((τC P C t).toWTreeFuel (τC P C t).dom.card []).label = C t
  rw [hlbl, τC_root_label]

#check @GrowingTree.attachAt_preserves_valid
#check @τBuild_valid
#check @τC_valid
#check @GrowingTree.Valid.exists_prefix_finset
#check @GrowingTree.Valid.length_lt_card
#check @τC_child_wellformed
#check @τC_siblings_proper
#check @GrowingTree.toWTreeFuel
#check @τBuild_root_mem
#check @τC_root_mem
#check @τC_root_label
#check @τC_toWTree_wellFormed_proper
#check @GrowingTree.toWTree
#check @τC_toWTreeFuel_props

-- Explicit checks for all remaining helper theorems.
#check @WTree.depthList_le
