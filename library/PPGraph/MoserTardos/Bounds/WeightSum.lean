/-
  PPGraphMoserTardosWeightSum.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), Theorem 5.7.1/5.7.3 bridge.

  Connects the already-built `WTree`/`WellFormed`/`Proper`/`weight`
  machinery (PPGraphMoserTardosWitness.lean, PPGraphMoserTardosWeight.lean
  -- the book's "weak Moser tree" and p[T]) to the already-built abstract
  recursion `mtWeight` (PPGraphMoserTardosConvergence.lean, the book's
  w(D,α), equation (5.9)): the sum of weight p T over all WellFormed+Proper
  trees T of depth ≤ D rooted at α equals mtWeight P p D α. This is
  exactly the tree-enumeration step both of those files flagged as
  "not attempted yet."

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import Mathlib.Basic.NNReal.Basic
public import PPGraph.MoserTardos.Witness.Witness
public import PPGraph.MoserTardos.Witness.Weight
public import PPGraph.MoserTardos.Bounds.Convergence

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped NNReal

-- -------------------------------------------------------------------
-- Depth
-- -------------------------------------------------------------------

mutual
/-- Depth of a witness tree: 0 for a bare root (matching the book's
    w(0,α) = p(α), "the only tree with root α and depth 0"), otherwise
    1 + the maximum depth among children. Defined mutually with
    `depthList` over the children -- Lean's termination checker does
    not see through a bare `List.map WTree.depth` as structural, but
    does see this mutual shape (standard rose-tree recursion idiom). -/
def WTree.depth {ι : Type} : WTree ι → ℕ
  | mk _ cs => WTree.depthList cs

def WTree.depthList {ι : Type} : List (WTree ι) → ℕ
  | [] => 0
  | c :: cs => max (1 + WTree.depth c) (WTree.depthList cs)
end

theorem WTree.depth_singleton {ι : Type} (i : ι) :
    WTree.depth (WTree.mk i ([] : List (WTree ι))) = 0 := rfl

-- -------------------------------------------------------------------
-- Decidable equality (needed for `Finset (WTree ι)` below)
-- -------------------------------------------------------------------

variable {ι : Type} [DecidableEq ι]

mutual
def WTree.beq : WTree ι → WTree ι → Bool
  | mk i cs, mk j ds => i = j && WTree.beqList cs ds

def WTree.beqList : List (WTree ι) → List (WTree ι) → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | c :: cs, d :: ds => WTree.beq c d && WTree.beqList cs ds
end

mutual
theorem WTree.beq_iff : ∀ a b : WTree ι, WTree.beq a b = true ↔ a = b
  | mk i cs, mk j ds => by
    simp only [WTree.beq, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨rfl, hcs⟩
      rw [WTree.beqList_iff cs ds |>.mp hcs]
    · intro h
      injection h with hi hcs
      exact ⟨hi, (WTree.beqList_iff cs ds).mpr hcs⟩

theorem WTree.beqList_iff : ∀ cs ds : List (WTree ι), WTree.beqList cs ds = true ↔ cs = ds
  | [], [] => by simp [WTree.beqList]
  | [], _ :: _ => by simp [WTree.beqList]
  | _ :: _, [] => by simp [WTree.beqList]
  | c :: cs, d :: ds => by
    simp only [WTree.beqList, Bool.and_eq_true, List.cons.injEq]
    constructor
    · rintro ⟨hc, hcs⟩
      exact ⟨(WTree.beq_iff c d).mp hc, (WTree.beqList_iff cs ds).mp hcs⟩
    · rintro ⟨hc, hcs⟩
      exact ⟨(WTree.beq_iff c d).mpr hc, (WTree.beqList_iff cs ds).mpr hcs⟩
end

instance WTree.decEq : DecidableEq (WTree ι) := fun a b =>
  decidable_of_iff (WTree.beq a b = true) (WTree.beq_iff a b)

-- -------------------------------------------------------------------
-- Enumeration: all WellFormed+Proper trees of depth ≤ D rooted at α
-- -------------------------------------------------------------------

variable {V : Type} [DecidableEq V] {S : VarSpaces V} [Fintype ι]

/-- All witness trees of depth ≤ D rooted at `α`, built to satisfy
    `WellFormed P` and `Proper` by construction: at depth D+1, choose
    ANY subset `T` of `plusNeighbors P α` to be the (distinctly
    labelled, by `Finset`-ness) children, and for each `β ∈ T`
    independently choose one depth-≤D tree rooted at `β`
    (`Finset.pi`) -- exactly the combinatorial content of `mtWeight`'s
    `∏_{β ~ α} (1 + w(D,β))` factor: each neighbor is either absent
    (the "1") or present with one recursively-bounded subtree. -/
noncomputable def wtreesUpTo (P : MTProcess S ι) : ℕ → ι → Finset (WTree ι)
  | 0, α => {WTree.mk α []}
  | D + 1, α => (plusNeighbors P α).powerset.biUnion (fun T =>
      (T.pi (fun β => wtreesUpTo P D β)).image (fun choice =>
        WTree.mk α (T.attach.toList.map (fun p => choice p.1 p.2))))

theorem mem_wtreesUpTo_label (P : MTProcess S ι) :
    ∀ D α, ∀ t ∈ wtreesUpTo P D α, t.label = α := by
  intro D
  induction D with
  | zero =>
    intro α t ht
    simp only [wtreesUpTo, Finset.mem_singleton] at ht
    subst ht
    rfl
  | succ D ih =>
    intro α t ht
    simp only [wtreesUpTo, Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image] at ht
    obtain ⟨T, _, choice, _, ht⟩ := ht
    subst ht
    rfl

theorem mem_wtreesUpTo_wellFormed (P : MTProcess S ι) :
    ∀ D α, ∀ t ∈ wtreesUpTo P D α, WTree.WellFormed P t := by
  intro D
  induction D with
  | zero =>
    intro α t ht
    simp only [wtreesUpTo, Finset.mem_singleton] at ht
    subst ht
    exact WTree.wellFormed_singleton P α
  | succ D ih =>
    intro α t ht
    simp only [wtreesUpTo, Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image] at ht
    obtain ⟨T, hTsub, choice, hchoice, ht⟩ := ht
    subst ht
    rw [Finset.mem_pi] at hchoice
    unfold WTree.WellFormed
    constructor
    · intro c hc
      simp only [List.mem_map, Finset.mem_toList] at hc
      obtain ⟨p, hp, hpc⟩ := hc
      subst hpc
      have hlabel : (choice p.1 p.2).label = p.1 := mem_wtreesUpTo_label P D p.1 _ (hchoice p.1 p.2)
      rw [hlabel]
      have hpT : (p : ι) ∈ T := p.2
      have := hTsub hpT
      simp only [plusNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    · intro c hc
      simp only [List.mem_map, Finset.mem_toList] at hc
      obtain ⟨p, hp, hpc⟩ := hc
      subst hpc
      exact ih p.1 _ (hchoice p.1 p.2)

theorem mem_wtreesUpTo_proper (P : MTProcess S ι) :
    ∀ D α, ∀ t ∈ wtreesUpTo P D α, WTree.Proper t := by
  intro D
  induction D with
  | zero =>
    intro α t ht
    simp only [wtreesUpTo, Finset.mem_singleton] at ht
    subst ht
    exact WTree.proper_singleton α
  | succ D ih =>
    intro α t ht
    simp only [wtreesUpTo, Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image] at ht
    obtain ⟨T, hTsub, choice, hchoice, ht⟩ := ht
    subst ht
    rw [Finset.mem_pi] at hchoice
    unfold WTree.Proper
    constructor
    · rw [List.pairwise_map]
      have hnodup : (T.attach.toList).Pairwise (fun a b => a ≠ b) := by
        rw [← List.nodup_iff_pairwise_ne]
        exact T.attach.nodup_toList
      refine hnodup.imp ?_
      intro p q hpq
      have hlabelp : (choice p.1 p.2).label = p.1 := mem_wtreesUpTo_label P D p.1 _ (hchoice p.1 p.2)
      have hlabelq : (choice q.1 q.2).label = q.1 := mem_wtreesUpTo_label P D q.1 _ (hchoice q.1 q.2)
      rw [hlabelp, hlabelq]
      intro hcontra
      exact hpq (Subtype.ext hcontra)
    · intro c hc
      simp only [List.mem_map, Finset.mem_toList] at hc
      obtain ⟨p, hp, hpc⟩ := hc
      subst hpc
      exact ih p.1 _ (hchoice p.1 p.2)

-- -------------------------------------------------------------------
-- The sum identity: Σ_{T ∈ wtreesUpTo P D α} weight p T = mtWeight P p D α
-- -------------------------------------------------------------------

theorem list_map_eq_iff_of_mem {α β : Type*} (l : List α) (f g : α → β) :
    l.map f = l.map g ↔ ∀ a ∈ l, f a = g a := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.cons.injEq, List.mem_cons]
    constructor
    · rintro ⟨hx, hxs⟩ a (rfl | ha)
      · exact hx
      · exact (ih.mp hxs) a ha
    · intro h
      exact ⟨h x (Or.inl rfl), ih.mpr (fun a ha => h a (Or.inr ha))⟩

theorem toList_map_prod {α M : Type*} [CommMonoid M] (s : Finset α) (g : α → M) :
    (s.toList.map g).prod = ∏ x ∈ s, g x := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]
  rfl

theorem weight_mk_attach (p : ι → ℝ≥0) (α : ι) (T : Finset ι) (choice : ∀ a ∈ T, WTree ι) :
    (WTree.mk α (T.attach.toList.map (fun q => choice q.1 q.2))).weight p
      = p α * ∏ x ∈ T.attach, (choice x.1 x.2).weight p := by
  simp only [WTree.weight_children, List.map_map, toList_map_prod, Function.comp_apply]

theorem wtreesUpTo_succ_children_sub (P : MTProcess S ι) (D : ℕ) (T : Finset ι)
    (choice : ∀ a ∈ T, WTree ι) (hchoice : ∀ a (h : a ∈ T), choice a h ∈ wtreesUpTo P D a) :
    ∀ b ∈ (T.attach.toList.map (fun p => choice p.1 p.2)).map WTree.label, b ∈ T := by
  intro b hb
  simp only [List.mem_map] at hb
  obtain ⟨c, hc, hbc⟩ := hb
  simp only [Finset.mem_toList] at hc
  obtain ⟨p, _, hpc⟩ := hc
  subst hpc
  subst hbc
  rw [mem_wtreesUpTo_label P D p.1 _ (hchoice p.1 p.2)]
  exact p.2

theorem wtreesUpTo_succ_children_sup (P : MTProcess S ι) (D : ℕ) (T : Finset ι)
    (choice : ∀ a ∈ T, WTree ι) (hchoice : ∀ a (h : a ∈ T), choice a h ∈ wtreesUpTo P D a) :
    ∀ a ∈ T, a ∈ (T.attach.toList.map (fun p => choice p.1 p.2)).map WTree.label := by
  intro a ha
  simp only [List.mem_map]
  refine ⟨choice a ha, ?_, mem_wtreesUpTo_label P D a _ (hchoice a ha)⟩
  simp only [Finset.mem_toList]
  exact ⟨⟨a, ha⟩, Finset.mem_attach T ⟨a, ha⟩, rfl⟩

theorem wtreesUpTo_succ_disjoint (P : MTProcess S ι) (D : ℕ) (α : ι) :
    (↑((plusNeighbors P α).powerset) : Set (Finset ι)).PairwiseDisjoint
      (fun T => (T.pi (fun β => wtreesUpTo P D β)).image (fun choice =>
        WTree.mk α (T.attach.toList.map (fun p => choice p.1 p.2)))) := by
  intro T1 _ T2 _ hne
  simp only [Function.onFun, Finset.disjoint_left]
  intro t ht1 ht2
  simp only [Finset.mem_image, Finset.mem_pi] at ht1 ht2
  obtain ⟨choice1, hchoice1, ht1⟩ := ht1
  obtain ⟨choice2, hchoice2, ht2⟩ := ht2
  apply hne
  have heq : WTree.mk α (T1.attach.toList.map (fun p => choice1 p.1 p.2))
      = WTree.mk α (T2.attach.toList.map (fun p => choice2 p.1 p.2)) := ht1.trans ht2.symm
  injection heq with _ hcs
  have hlabeq : (T1.attach.toList.map (fun p => choice1 p.1 p.2)).map WTree.label
      = (T2.attach.toList.map (fun p => choice2 p.1 p.2)).map WTree.label := by rw [hcs]
  apply Finset.Subset.antisymm
  · intro a ha
    have h1 := wtreesUpTo_succ_children_sup P D T1 choice1 hchoice1 a ha
    rw [hlabeq] at h1
    exact wtreesUpTo_succ_children_sub P D T2 choice2 hchoice2 a h1
  · intro a ha
    have := wtreesUpTo_succ_children_sup P D T2 choice2 hchoice2 a ha
    rw [← hlabeq] at this
    exact wtreesUpTo_succ_children_sub P D T1 choice1 hchoice1 a this

theorem wtreesUpTo_succ_injOn (P : MTProcess S ι) (D : ℕ) (α : ι) (T : Finset ι) :
    Set.InjOn (fun choice : ∀ a ∈ T, WTree ι =>
        WTree.mk α (T.attach.toList.map (fun p => choice p.1 p.2)))
      (T.pi (fun β => wtreesUpTo P D β) : Finset (∀ a ∈ T, WTree ι)) := by
  intro choice1 _ choice2 _ heq
  injection heq with _ hcs
  rw [list_map_eq_iff_of_mem] at hcs
  funext a h
  exact hcs ⟨a, h⟩ (Finset.mem_toList.mpr (Finset.mem_attach T ⟨a, h⟩))

theorem sum_wtreesUpTo_weight (P : MTProcess S ι) (p : ι → ℝ≥0) :
    ∀ D α, ∑ t ∈ wtreesUpTo P D α, t.weight p = mtWeight P p D α := by
  intro D
  induction D with
  | zero =>
    intro α
    simp only [wtreesUpTo, Finset.sum_singleton, WTree.weight_singleton]
    rfl
  | succ D ih =>
    intro α
    show ∑ t ∈ (plusNeighbors P α).powerset.biUnion (fun T =>
        (T.pi (fun β => wtreesUpTo P D β)).image (fun choice =>
          WTree.mk α (T.attach.toList.map (fun p => choice p.1 p.2)))), t.weight p = _
    rw [Finset.sum_biUnion (wtreesUpTo_succ_disjoint P D α)]
    have hinner : ∀ T ∈ (plusNeighbors P α).powerset,
        ∑ t ∈ (T.pi (fun β => wtreesUpTo P D β)).image (fun choice =>
            WTree.mk α (T.attach.toList.map (fun p => choice p.1 p.2))), t.weight p
          = p α * ∏ a ∈ T, mtWeight P p D a := by
      intro T _
      rw [Finset.sum_image (fun x hx y hy => wtreesUpTo_succ_injOn P D α T hx hy)]
      simp_rw [weight_mk_attach]
      rw [← Finset.mul_sum]
      congr 1
      have goal_eq : (∏ a ∈ T, mtWeight P p D a) = ∏ a ∈ T, ∑ b ∈ wtreesUpTo P D a, b.weight p :=
        Finset.prod_congr rfl (fun a _ => (ih a).symm)
      rw [goal_eq, Finset.prod_sum]
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, ← Finset.prod_one_add]
    rfl

-- -------------------------------------------------------------------
-- Monotonicity in D: every depth-≤D tree is also depth-≤D+1 -- lets
-- the "any depth" union over D telescope cleanly (needed to bound the
-- unbounded-depth sum of ALL occurring witness trees rooted at a
-- label, Theorem 5.7.1's actual shape, by mtWeight_le UNIFORMLY in D).
-- -------------------------------------------------------------------

theorem wtreesUpTo_mono (P : MTProcess S ι) : ∀ D α, wtreesUpTo P D α ⊆ wtreesUpTo P (D + 1) α := by
  intro D
  induction D with
  | zero =>
    intro α t ht
    simp only [wtreesUpTo, Finset.mem_singleton] at ht
    subst ht
    simp only [wtreesUpTo, Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
    refine ⟨∅, Finset.empty_subset _, fun β hβ => absurd hβ (Finset.notMem_empty β), ?_, ?_⟩
    · rw [Finset.mem_pi]
      intro β hβ
      exact absurd hβ (Finset.notMem_empty β)
    · simp
  | succ D ih =>
    intro α t ht
    simp only [wtreesUpTo, Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image] at ht ⊢
    obtain ⟨T, hTsub, choice, hchoice, ht⟩ := ht
    rw [Finset.mem_pi] at hchoice
    refine ⟨T, hTsub, choice, ?_, ht⟩
    rw [Finset.mem_pi]
    intro β hβ
    exact ih β (hchoice β hβ)

theorem wtreesUpTo_mono_le (P : MTProcess S ι) :
    ∀ D D' α, D ≤ D' → wtreesUpTo P D α ⊆ wtreesUpTo P D' α := by
  intro D D' α hle
  induction D', hle using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ k _ ih => exact ih.trans (wtreesUpTo_mono P k α)

#check @wtreesUpTo_mono
#check @wtreesUpTo_mono_le

#check @WTree.depth
#check @WTree.depth_singleton
#check @wtreesUpTo
#check @mem_wtreesUpTo_label
#check @mem_wtreesUpTo_wellFormed
#check @mem_wtreesUpTo_proper
#check @sum_wtreesUpTo_weight
#check @WTree.decEq

-- Explicit checks for all remaining helper theorems.
#check @WTree.beqList_iff
#check @WTree.beq_iff
#check @list_map_eq_iff_of_mem
#check @toList_map_prod
#check @weight_mk_attach
#check @wtreesUpTo_succ_children_sub
#check @wtreesUpTo_succ_children_sup
#check @wtreesUpTo_succ_disjoint
#check @wtreesUpTo_succ_injOn
