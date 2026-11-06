/-
  PPGraphMoserTardosInjectivityBridge.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), Theorem 5.7.1 bridge, part 3.

  Connects `τC_injective_on_occurrences` (PPGraphMoserTardosInjectivity.lean,
  address-level: distinct occurrence-times of the same event give
  distinct GrowingTrees) to the `WTree`/`wtreesUpTo` world
  (PPGraphMoserTardosRealTree.lean, PPGraphMoserTardosCanonical.lean):
  the SAME per-label occurrence count that already distinguishes the
  address-level trees survives both `GrowingTree.toWTree` and
  `WTree.canonicalize`, so distinct occurrence-times still give
  distinct CANONICALIZED trees -- the fact the final (unbounded-depth)
  reindexing argument for E[T_LOG] needs.

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.MoserTardos.Witness.RealTree
public import PPGraph.MoserTardos.Witness.Canonical
public import PPGraph.MoserTardos.Witness.Injectivity

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical
open scoped NNReal

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- Section 0: additive counterpart of PPGraphMoserTardosWeightSum.lean's
-- `toList_map_prod`, needed for the same Finset↔List reindexing but
-- for a ℕ-valued sum instead of an ℝ≥0-valued product.
-- -------------------------------------------------------------------

theorem toList_map_sum {α M : Type*} [AddCommMonoid M] (s : Finset α) (g : α → M) :
    (s.toList.map g).sum = ∑ x ∈ s, g x := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
  rfl

-- -------------------------------------------------------------------
-- Section 1: prefixes of an in-domain address are themselves in-domain
-- (the missing half of GrowingTree.Valid needed for the countLabel
-- bridge -- companion to the "prefix Finset" argument already used for
-- the depth/card bound).
-- -------------------------------------------------------------------

theorem GrowingTree.Valid.prefix_mem {ι : Type} (T : GrowingTree ι) (hV : T.Valid) :
    ∀ w ∈ T.dom, ∀ u, u <+: w → u ∈ T.dom := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro hw u hu
    rw [List.prefix_nil.mp hu]
    exact hw
  | append_singleton l a ih =>
    intro hw u hu
    rcases eq_or_ne u (l ++ [a]) with heq | hne
    · rw [heq]; exact hw
    · have hl : l ∈ T.dom := hV.2 l a hw
      have hle_prefix : l <+: l ++ [a] := ⟨[a], rfl⟩
      have hult : u.length ≤ l.length := by
        have h1 := hu.length_le
        have hlenla : (l ++ [a]).length = l.length + 1 := by simp
        rw [hlenla] at h1
        rcases eq_or_lt_of_le h1 with heq2 | hlt
        · exfalso
          exact hne (hu.eq_of_length_le (by rw [hlenla]; omega))
        · omega
      have hu' : u <+: l := List.prefix_of_prefix_length_le hu hle_prefix hult
      exact ih hl u hu'

-- -------------------------------------------------------------------
-- Section 2: the per-label occurrence count of the reconstructed
-- (sub)tree at v matches the address-level count restricted to v's
-- descendants
-- -------------------------------------------------------------------

theorem GrowingTree.toWTreeFuel_countLabel {ι : Type} [DecidableEq ι] (T : GrowingTree ι) (hV : T.Valid) (A : ι) :
    ∀ n v, v ∈ T.dom → (∀ w ∈ T.dom, w.length ≤ v.length + n) →
      WTree.countLabel A (T.toWTreeFuel n v)
        = (T.dom.filter (fun w => v <+: w ∧ T.lab w = A)).card := by
  intro n
  induction n with
  | zero =>
    intro v hv hb
    show (if T.lab v = A then 1 else 0) = (T.dom.filter (fun w => v <+: w ∧ T.lab w = A)).card
    by_cases hlabv : T.lab v = A
    · rw [ite_eq_left hlabv]
      have hset : T.dom.filter (fun w => v <+: w ∧ T.lab w = A) = {v} := by
        apply Finset.ext
        intro w
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hwdom, hpre, _⟩
          have hb' := hb w hwdom
          exact (hpre.eq_of_length_le (by omega)).symm
        · intro heq
          rw [heq]
          exact ⟨hv, List.prefix_refl v, hlabv⟩
      rw [hset, Finset.card_singleton]
    · rw [ite_eq_right hlabv]
      have hset : T.dom.filter (fun w => v <+: w ∧ T.lab w = A) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro w hwdom hcond
        obtain ⟨hpre, hlab⟩ := hcond
        have hb' := hb w hwdom
        have hweq : v = w := hpre.eq_of_length_le (by omega)
        exact hlabv (hweq ▸ hlab)
      rw [hset, Finset.card_empty]
  | succ n ih =>
    intro v hv hb
    set children := T.dom.filter (fun w => ∃ k, w = v ++ [k]) with hchildren_def
    show (if T.lab v = A then 1 else 0) +
        WTree.countLabelList A (children.toList.map (fun w => T.toWTreeFuel n w))
      = (T.dom.filter (fun w => v <+: w ∧ T.lab w = A)).card
    rw [WTree.countLabelList_eq_sum, List.map_map]
    have hstep : (children.toList.map (WTree.countLabel A ∘ fun w => T.toWTreeFuel n w))
        = children.toList.map (fun w => (T.dom.filter (fun w' => w <+: w' ∧ T.lab w' = A)).card) := by
      apply List.map_congr_left
      intro w hw
      show WTree.countLabel A (T.toWTreeFuel n w)
        = (T.dom.filter (fun w' => w <+: w' ∧ T.lab w' = A)).card
      rw [hchildren_def, Finset.mem_toList, Finset.mem_filter] at hw
      obtain ⟨hwdom, k, hwk⟩ := hw
      have hbw : ∀ w' ∈ T.dom, w'.length ≤ w.length + n := by
        intro w' hw'
        have hb' := hb w' hw'
        have hwlen : w.length = v.length + 1 := by rw [hwk]; simp
        omega
      exact ih w hwdom hbw
    rw [hstep]
    have hsplit : T.dom.filter (fun w => v <+: w ∧ T.lab w = A) =
        (if T.lab v = A then ({v} : Finset (List ℕ)) else ∅) ∪
          children.biUnion (fun u => T.dom.filter (fun w => u <+: w ∧ T.lab w = A)) := by
      apply Finset.ext
      intro w
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_biUnion]
      constructor
      · rintro ⟨hwdom, hpre, hlab⟩
        rcases eq_or_ne w v with heq | hne
        · left
          subst heq
          by_cases hlabv : T.lab w = A
          · rw [ite_eq_left hlabv]; exact Finset.mem_singleton_self w
          · exact absurd hlab hlabv
        · right
          obtain ⟨t, ht⟩ := hpre
          have ht_ne : t ≠ [] := by
            intro h
            subst h
            simp only [List.append_nil] at ht
            exact hne ht.symm
          obtain ⟨k, t', htk⟩ := List.exists_cons_of_ne_nil ht_ne
          have hkey : (v ++ [k]) ++ t' = w := by rw [← ht, htk]; simp [List.append_assoc]
          refine ⟨v ++ [k], ?_, hwdom, ⟨t', hkey⟩, hlab⟩
          rw [hchildren_def, Finset.mem_filter]
          exact ⟨GrowingTree.Valid.prefix_mem T hV w hwdom (v ++ [k]) ⟨t', hkey⟩, k, rfl⟩
      · rintro (h | ⟨u, hu, hwdom, hpre, hlab⟩)
        · by_cases hlabv : T.lab v = A
          · rw [ite_eq_left hlabv] at h
            have hwv : w = v := Finset.mem_singleton.mp h
            subst hwv
            exact ⟨hv, List.prefix_refl w, hlabv⟩
          · rw [ite_eq_right hlabv] at h
            exact absurd h (Finset.notMem_empty w)
        · rw [hchildren_def, Finset.mem_filter] at hu
          obtain ⟨_, k, huk⟩ := hu
          refine ⟨hwdom, ?_, hlab⟩
          have hvu : v <+: u := by rw [huk]; exact ⟨[k], rfl⟩
          exact hvu.trans hpre
    rw [hsplit]
    have hdisjoint : (children : Set (List ℕ)).PairwiseDisjoint
        (fun u => T.dom.filter (fun w => u <+: w ∧ T.lab w = A)) := by
      intro u1 hu1 u2 hu2 hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro w hw1 hw2
      simp only [Finset.mem_filter] at hw1 hw2
      rw [hchildren_def, Finset.mem_coe, Finset.mem_filter] at hu1 hu2
      obtain ⟨_, k1, hk1⟩ := hu1
      obtain ⟨_, k2, hk2⟩ := hu2
      apply hne
      have hlen1 : u1.length = v.length + 1 := by rw [hk1]; simp
      have hlen2 : u2.length = v.length + 1 := by rw [hk2]; simp
      have hu1u2 : u1 <+: u2 := List.prefix_of_prefix_length_le hw1.2.1 hw2.2.1 (by omega)
      exact hu1u2.eq_of_length_le (by omega)
    have hunioncard : ((if T.lab v = A then ({v} : Finset (List ℕ)) else ∅) ∪
        children.biUnion (fun u => T.dom.filter (fun w => u <+: w ∧ T.lab w = A))).card
        = (if T.lab v = A then ({v} : Finset (List ℕ)) else ∅).card +
          (children.biUnion (fun u => T.dom.filter (fun w => u <+: w ∧ T.lab w = A))).card := by
      apply Finset.card_union_of_disjoint
      simp only [Finset.disjoint_left]
      intro w hw1 hw2
      simp only [Finset.mem_biUnion] at hw2
      obtain ⟨u, hu, hw2'⟩ := hw2
      simp only [Finset.mem_filter] at hw2'
      rw [hchildren_def, Finset.mem_filter] at hu
      obtain ⟨_, k, huk⟩ := hu
      by_cases hlabv : T.lab v = A
      · rw [ite_eq_left hlabv] at hw1
        have hwv : w = v := Finset.mem_singleton.mp hw1
        have hulew : u.length ≤ w.length := hw2'.2.1.length_le
        have hulen : u.length = v.length + 1 := by rw [huk]; simp
        have hwvlen : w.length = v.length := by rw [hwv]
        omega
      · rw [ite_eq_right hlabv] at hw1
        exact absurd hw1 (Finset.notMem_empty w)
    rw [hunioncard, Finset.card_biUnion hdisjoint]
    have hif : (if T.lab v = A then ({v} : Finset (List ℕ)) else ∅).card
        = if T.lab v = A then 1 else 0 := by
      by_cases hlabv : T.lab v = A
      · rw [ite_eq_left hlabv, ite_eq_left hlabv, Finset.card_singleton]
      · rw [ite_eq_right hlabv, ite_eq_right hlabv, Finset.card_empty]
    rw [hif]
    congr 1
    rw [hchildren_def]
    exact toList_map_sum _ _

-- -------------------------------------------------------------------
-- Section 3: specialize at the root -- WTree.countLabel on the FULL
-- reconstructed tree matches the plain address-level countLabel
-- (PPGraphMoserTardosInjectivity.lean)
-- -------------------------------------------------------------------

theorem GrowingTree.toWTree_countLabel {ι : Type} [DecidableEq ι] (T : GrowingTree ι) (hV : T.Valid) (A : ι)
    (hroot : ([] : List ℕ) ∈ T.dom) :
    WTree.countLabel A (T.toWTree []) = countLabel T A := by
  have hb : ∀ w ∈ T.dom, w.length ≤ ([] : List ℕ).length + T.dom.card := by
    intro w hw
    have := GrowingTree.Valid.length_lt_card T hV hw
    simp only [List.length_nil, zero_add]
    omega
  have hkey := T.toWTreeFuel_countLabel hV A T.dom.card [] hroot hb
  have heq : T.dom.filter (fun w => ([] : List ℕ) <+: w ∧ T.lab w = A)
      = T.dom.filter (fun w => T.lab w = A) := by
    apply Finset.filter_congr
    intro w _
    simp only [List.nil_prefix, true_and]
  show WTree.countLabel A (T.toWTreeFuel T.dom.card []) = countLabel T A
  rw [hkey, heq]
  rfl

-- -------------------------------------------------------------------
-- Section 4: THE result -- distinct occurrence-times of the same
-- event give distinct CANONICALIZED trees, i.e. injectivity survives
-- the GrowingTree → WTree → wtreesUpTo conversion.
-- -------------------------------------------------------------------

theorem τC_canonicalize_toWTree_ne_of_lt {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : MTProcess S ι) (C : ℕ → ι) (t1 t2 : ℕ)
    (ht1 : 0 < t1) (ht2 : 0 < t2) (hlt : t1 < t2) (hA : C t1 = C t2) :
    WTree.canonicalize ((τC P C t1).toWTree []) ≠ WTree.canonicalize ((τC P C t2).toWTree []) := by
  classical
  intro heq
  apply τC_countLabel_ne_of_lt P C t1 t2 ht1 ht2 hlt hA
  have hpr1 : WTree.Proper ((τC P C t1).toWTree []) :=
    (τC_toWTree_wellFormed_proper P C t1).2.2.1
  have hpr2 : WTree.Proper ((τC P C t2).toWTree []) :=
    (τC_toWTree_wellFormed_proper P C t2).2.2.1
  have e1 : countLabel (τC P C t1) (C t1)
      = WTree.countLabel (C t1) (WTree.canonicalize ((τC P C t1).toWTree [])) := by
    rw [WTree.canonicalize_countLabel (C t1) _ hpr1]
    exact (GrowingTree.toWTree_countLabel (τC P C t1) (τC_valid P C t1) (C t1)
      (τC_root_mem P C t1)).symm
  have e2 : countLabel (τC P C t2) (C t2)
      = WTree.countLabel (C t1) (WTree.canonicalize ((τC P C t2).toWTree [])) := by
    rw [hA, WTree.canonicalize_countLabel (C t2) _ hpr2]
    exact (GrowingTree.toWTree_countLabel (τC P C t2) (τC_valid P C t2) (C t2)
      (τC_root_mem P C t2)).symm
  rw [e1, e2, heq]

-- -------------------------------------------------------------------
-- Section 5: the same bridge, but for WEIGHT (a product) instead of
-- countLabel (a cardinality) -- needed to connect Theorem 5.7.2's
-- ℝ≥0∞-valued product over `GrowingTree.dom` to `WTree.weight` of the
-- reconstructed tree, the form `wtreesUpTo`/`mtWeight` understand.
-- -------------------------------------------------------------------

theorem GrowingTree.toWTreeFuel_weight_eq_prod {ι : Type} [DecidableEq ι] (T : GrowingTree ι)
    (hV : T.Valid) (p : ι → ℝ≥0) :
    ∀ n v, v ∈ T.dom → (∀ w ∈ T.dom, w.length ≤ v.length + n) →
      WTree.weight p (T.toWTreeFuel n v) = ∏ w ∈ T.dom.filter (fun w => v <+: w), p (T.lab w) := by
  intro n
  induction n with
  | zero =>
    intro v hv hb
    rw [show T.toWTreeFuel 0 v = WTree.mk (T.lab v) [] from rfl, WTree.weight_singleton]
    have hset : T.dom.filter (fun w => v <+: w) = {v} := by
      apply Finset.ext
      intro w
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hwdom, hpre⟩
        have hb' := hb w hwdom
        exact (hpre.eq_of_length_le (by omega)).symm
      · intro heq
        rw [heq]
        exact ⟨hv, List.prefix_refl v⟩
    rw [hset, Finset.prod_singleton]
  | succ n ih =>
    intro v hv hb
    set children := T.dom.filter (fun w => ∃ k, w = v ++ [k]) with hchildren_def
    rw [show T.toWTreeFuel (n + 1) v =
          WTree.mk (T.lab v) (children.toList.map (fun w => T.toWTreeFuel n w)) from rfl,
        WTree.weight_children, List.map_map]
    have hstep : (children.toList.map (WTree.weight p ∘ fun w => T.toWTreeFuel n w))
        = children.toList.map (fun w => ∏ w' ∈ T.dom.filter (fun w' => w <+: w'), p (T.lab w')) := by
      apply List.map_congr_left
      intro w hw
      show WTree.weight p (T.toWTreeFuel n w)
        = ∏ w' ∈ T.dom.filter (fun w' => w <+: w'), p (T.lab w')
      rw [hchildren_def, Finset.mem_toList, Finset.mem_filter] at hw
      obtain ⟨hwdom, k, hwk⟩ := hw
      have hbw : ∀ w' ∈ T.dom, w'.length ≤ w.length + n := by
        intro w' hw'
        have hb' := hb w' hw'
        have hwlen : w.length = v.length + 1 := by rw [hwk]; simp
        omega
      exact ih w hwdom hbw
    rw [hstep]
    have hsplit : T.dom.filter (fun w => v <+: w) =
        insert v (children.biUnion (fun u => T.dom.filter (fun w => u <+: w))) := by
      apply Finset.ext
      intro w
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_biUnion]
      constructor
      · rintro ⟨hwdom, hpre⟩
        rcases eq_or_ne w v with heq | hne
        · left; exact heq
        · right
          obtain ⟨t, ht⟩ := hpre
          have ht_ne : t ≠ [] := by
            intro h
            subst h
            simp only [List.append_nil] at ht
            exact hne ht.symm
          obtain ⟨k, t', htk⟩ := List.exists_cons_of_ne_nil ht_ne
          have hkey : (v ++ [k]) ++ t' = w := by rw [← ht, htk]; simp [List.append_assoc]
          refine ⟨v ++ [k], ?_, hwdom, ⟨t', hkey⟩⟩
          rw [hchildren_def, Finset.mem_filter]
          exact ⟨GrowingTree.Valid.prefix_mem T hV w hwdom (v ++ [k]) ⟨t', hkey⟩, k, rfl⟩
      · rintro (heq | ⟨u, hu, hwdom, hpre⟩)
        · rw [heq]; exact ⟨hv, List.prefix_refl v⟩
        · rw [hchildren_def, Finset.mem_filter] at hu
          obtain ⟨_, k, huk⟩ := hu
          refine ⟨hwdom, ?_⟩
          have hvu : v <+: u := by rw [huk]; exact ⟨[k], rfl⟩
          exact hvu.trans hpre
    rw [hsplit]
    have hnotmem : v ∉ children.biUnion (fun u => T.dom.filter (fun w => u <+: w)) := by
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      rintro ⟨u, hu, hwdom, hpre⟩
      rw [hchildren_def, Finset.mem_filter] at hu
      obtain ⟨_, k, huk⟩ := hu
      have hulen : u.length = v.length + 1 := by rw [huk]; simp
      have hule : u.length ≤ v.length := hpre.length_le
      omega
    have hdisjoint : (children : Set (List ℕ)).PairwiseDisjoint
        (fun u => T.dom.filter (fun w => u <+: w)) := by
      intro u1 hu1 u2 hu2 hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro w hw1 hw2
      simp only [Finset.mem_filter] at hw1 hw2
      rw [hchildren_def, Finset.mem_coe, Finset.mem_filter] at hu1 hu2
      obtain ⟨_, k1, hk1⟩ := hu1
      obtain ⟨_, k2, hk2⟩ := hu2
      apply hne
      have hlen1 : u1.length = v.length + 1 := by rw [hk1]; simp
      have hlen2 : u2.length = v.length + 1 := by rw [hk2]; simp
      have hu1u2 : u1 <+: u2 := List.prefix_of_prefix_length_le hw1.2 hw2.2 (by omega)
      exact hu1u2.eq_of_length_le (by omega)
    rw [Finset.prod_insert hnotmem, Finset.prod_biUnion hdisjoint]
    congr 1
    rw [hchildren_def]
    exact toList_map_prod _ _

theorem GrowingTree.toWTree_weight_eq_prod {ι : Type} [DecidableEq ι] (T : GrowingTree ι) (hV : T.Valid)
    (p : ι → ℝ≥0) (hroot : ([] : List ℕ) ∈ T.dom) :
    WTree.weight p (T.toWTree []) = ∏ w ∈ T.dom, p (T.lab w) := by
  have hb : ∀ w ∈ T.dom, w.length ≤ ([] : List ℕ).length + T.dom.card := by
    intro w hw
    have := GrowingTree.Valid.length_lt_card T hV hw
    simp only [List.length_nil, zero_add]
    omega
  have hkey := T.toWTreeFuel_weight_eq_prod hV p T.dom.card [] hroot hb
  have heq : T.dom.filter (fun w => ([] : List ℕ) <+: w) = T.dom := by
    apply Finset.filter_true_of_mem
    intro w _
    exact List.nil_prefix
  show WTree.weight p (T.toWTreeFuel T.dom.card []) = ∏ w ∈ T.dom, p (T.lab w)
  rw [hkey, heq]

#check @GrowingTree.Valid.prefix_mem
#check @GrowingTree.toWTreeFuel_countLabel
#check @GrowingTree.toWTree_countLabel
#check @τC_canonicalize_toWTree_ne_of_lt
#check @GrowingTree.toWTreeFuel_weight_eq_prod
#check @GrowingTree.toWTree_weight_eq_prod

-- Explicit checks for all remaining helper theorems.
#check @toList_map_sum
