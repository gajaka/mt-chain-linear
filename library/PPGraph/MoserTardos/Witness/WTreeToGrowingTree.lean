/-
  PPGraphMoserTardosWTreeToGrowingTree.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), a DIRECT `WTree -> GrowingTree`
  embedding -- independent of tau_Build/tau_C entirely. This is piece (a) of
  the entropy-compression "fixed representative" plan
  (PPGraphMoserTardosProbabilityGeneral.lean's header comment): given an
  abstract, already-realized canonical witness-tree SHAPE, build a concrete,
  omega-independent GrowingTree with that exact shape, by reading addresses
  off directly from the WTree's own recursive children list (child at list
  position k gets address-component k), rather than growing it via any
  simulated random process.

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.MoserTardos.Witness.Growing
public import PPGraph.MoserTardos.Witness.Witness
public import PPGraph.MoserTardos.Witness.CheckOrder

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical

-- -------------------------------------------------------------------
-- Section 1: the embedding itself. `toGT_lab` reads an address by
-- repeatedly descending into `t.children[k]?` per address component `k`
-- (structural recursion on the ADDRESS, `t` just changes along the way);
-- `toGT_dom` is the mutual-recursion mirror computing which addresses are
-- reachable this way (child at list-position `idx` contributes its own
-- domain with `idx` prepended to every address).
-- -------------------------------------------------------------------

def WTree.toGT_lab {ι : Type} (t : WTree ι) : List ℕ → ι
  | [] => t.label
  | (k :: rest) => match t.children[k]? with
      | some c => WTree.toGT_lab c rest
      | none => t.label

mutual
def WTree.toGT_dom {ι : Type} : WTree ι → Finset (List ℕ)
  | WTree.mk _ cs => insert [] (WTree.toGT_domChildren cs 0)

def WTree.toGT_domChildren {ι : Type} : List (WTree ι) → ℕ → Finset (List ℕ)
  | [], _ => ∅
  | (c :: cs), idx => (WTree.toGT_dom c).image (fun a => idx :: a) ∪ WTree.toGT_domChildren cs (idx + 1)
end

/-- The public embedding: a `GrowingTree` whose addresses/labels are read
    directly off `t`'s own recursive structure, no simulated construction
    process involved. -/
def WTree.toGrowingTree {ι : Type} (t : WTree ι) : GrowingTree ι where
  dom := WTree.toGT_dom t
  lab := WTree.toGT_lab t

-- -------------------------------------------------------------------
-- Section 2: `Valid` (root present + prefix-closed). Root membership is
-- immediate from the `insert []` in `toGT_dom`'s definition; prefix-closure
-- is a mutual induction mirroring `toGT_dom`/`toGT_domChildren`'s own shape.
-- -------------------------------------------------------------------

theorem WTree.toGT_dom_root_mem {ι : Type} (t : WTree ι) :
    ([] : List ℕ) ∈ WTree.toGT_dom t := by
  cases t with
  | mk i cs => exact Finset.mem_insert_self _ _

mutual
theorem WTree.toGT_dom_prefix_mem {ι : Type} (v : List ℕ) (k : ℕ) :
    ∀ t : WTree ι, v ++ [k] ∈ WTree.toGT_dom t → v ∈ WTree.toGT_dom t
  | WTree.mk i cs => by
      intro hmem
      show v ∈ insert ([] : List ℕ) (WTree.toGT_domChildren cs 0)
      rcases Finset.mem_insert.mp hmem with h | h
      · exact absurd h (by
          intro hcontra
          exact List.append_ne_nil_of_right_ne_nil v (by simp) hcontra)
      · rcases WTree.toGT_domChildren_prefix_mem v k cs 0 h with h0 | h0
        · rw [h0]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem h0

theorem WTree.toGT_domChildren_prefix_mem {ι : Type} (v : List ℕ) (k : ℕ) :
    ∀ (cs : List (WTree ι)) (idx0 : ℕ),
      v ++ [k] ∈ WTree.toGT_domChildren cs idx0 → v = [] ∨ v ∈ WTree.toGT_domChildren cs idx0
  | [], _ => by simp [WTree.toGT_domChildren]
  | (c :: cs), idx0 => by
      intro hmem
      show v = [] ∨ v ∈ (WTree.toGT_dom c).image (fun a => idx0 :: a) ∪ WTree.toGT_domChildren cs (idx0 + 1)
      rcases Finset.mem_union.mp hmem with h | h
      · rw [Finset.mem_image] at h
        obtain ⟨a, ha, heq⟩ := h
        rcases v with _ | ⟨v0, v'⟩
        · exact Or.inl rfl
        · refine Or.inr (Finset.mem_union_left _ ?_)
          rw [Finset.mem_image]
          have heq' : idx0 = v0 ∧ a = v' ++ [k] := by
            simpa using heq
          refine ⟨v', ?_, by rw [heq'.1]⟩
          rw [heq'.2] at ha
          exact WTree.toGT_dom_prefix_mem v' k c ha
      · rcases WTree.toGT_domChildren_prefix_mem v k cs (idx0 + 1) h with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (Finset.mem_union_right _ h0)
end

theorem WTree.toGrowingTree_valid {ι : Type} (t : WTree ι) :
    (WTree.toGrowingTree t).Valid :=
  ⟨WTree.toGT_dom_root_mem t, fun v k hvk => WTree.toGT_dom_prefix_mem v k t hvk⟩

/-- If `l.drop n = a :: l'`, then `a` sits at index `n` in `l`, and
    dropping one further from there leaves `l'`. Proved from scratch (no
    named mathlib lemma needed) by induction on `n`. -/
theorem List.getElem?_and_drop_succ_of_drop_eq_cons {α : Type} :
    ∀ (n : ℕ) (l : List α) (a : α) (l' : List α), l.drop n = a :: l' →
      l[n]? = some a ∧ l.drop (n + 1) = l'
  | 0, l, a, l', h => by
      simp only [List.drop_zero] at h
      subst h
      exact ⟨rfl, rfl⟩
  | (n + 1), l, a, l', h => by
      cases l with
      | nil => simp at h
      | cons x xs =>
          have h' : xs.drop n = a :: l' := h
          obtain ⟨h1, h2⟩ := List.getElem?_and_drop_succ_of_drop_eq_cons n xs a l' h'
          exact ⟨h1, h2⟩

/-- Every address contributed by `toGT_domChildren cs idx0` starts with
    some `k ≥ idx0` (the list-position of the child it descends into,
    offset by the starting index). -/
theorem WTree.toGT_domChildren_head_ge {ι : Type} :
    ∀ (cs : List (WTree ι)) (idx0 : ℕ) (w : List ℕ),
      w ∈ WTree.toGT_domChildren cs idx0 → ∃ k a, w = k :: a ∧ idx0 ≤ k
  | [], _, _ => by simp [WTree.toGT_domChildren]
  | (c :: cs), idx0, w => by
      intro hmem
      show ∃ k a, w = k :: a ∧ idx0 ≤ k
      rcases Finset.mem_union.mp hmem with h | h
      · rw [Finset.mem_image] at h
        obtain ⟨a, _, heq⟩ := h
        exact ⟨idx0, a, heq.symm, le_refl _⟩
      · obtain ⟨k, a, heq, hk⟩ := WTree.toGT_domChildren_head_ge cs (idx0 + 1) w h
        exact ⟨k, a, heq, by omega⟩

theorem WTree.toGT_domChildren_length_pos {ι : Type} (cs : List (WTree ι)) (idx0 : ℕ)
    (w : List ℕ) (hw : w ∈ WTree.toGT_domChildren cs idx0) : 0 < w.length := by
  obtain ⟨k, a, heq, _⟩ := WTree.toGT_domChildren_head_ge cs idx0 w hw
  rw [heq]; simp

theorem WTree.toGT_domChildren_head_disjoint {ι : Type} (c : WTree ι) (cs : List (WTree ι))
    (idx0 : ℕ) :
    Disjoint ((WTree.toGT_dom c).image (fun a => idx0 :: a))
      (WTree.toGT_domChildren cs (idx0 + 1)) := by
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rw [Finset.mem_image] at hw1
  obtain ⟨a, _, heq⟩ := hw1
  obtain ⟨k, a', heq2, hk⟩ := WTree.toGT_domChildren_head_ge cs (idx0 + 1) w hw2
  rw [← heq] at heq2
  have hkeq : idx0 = k := (List.cons.injEq _ _ _ _).mp heq2 |>.1
  omega

-- -------------------------------------------------------------------
-- Section 3: `labelsAtDepth`, a purely-structural (no addresses)
-- multiset of the labels occurring at a given depth in `t`, built with
-- the SAME mutual-recursion shape as `toGT_dom`/`toGT_domChildren`
-- (singleton/sum standing in for insert/union) so that it lines up
-- with `toGT_dom`'s own depth-`d` slice term-for-term. This is the
-- bridge letting a purely-t-level "no repeated-or-neighbor label at any
-- depth" hypothesis (stateable and provable without ever mentioning
-- `toGrowingTree`'s addresses) transfer to `SameDepthIndependent P
-- (WTree.toGrowingTree t)`.
-- -------------------------------------------------------------------

mutual
def WTree.labelsAtDepth {ι : Type} : WTree ι → ℕ → Multiset ι
  | WTree.mk i _, 0 => {i}
  | WTree.mk _ cs, (d + 1) => WTree.labelsAtDepthChildren cs d

def WTree.labelsAtDepthChildren {ι : Type} : List (WTree ι) → ℕ → Multiset ι
  | [], _ => 0
  | (c :: cs), d => WTree.labelsAtDepth c d + WTree.labelsAtDepthChildren cs d
end

mutual
/-- `labelsAtDepth t d` is exactly the multiset of labels read off the
    depth-`d` slice of `toGT_dom t`, via `toGT_lab`. Mutual induction
    mirroring `toGT_dom`/`toGT_domChildren`'s own recursive shape
    step-for-step (singleton ↔ insert-of-root, sum ↔ union-of-images). -/
theorem WTree.labelsAtDepth_eq_domFilter_map {ι : Type} (d : ℕ) :
    ∀ t : WTree ι,
      WTree.labelsAtDepth t d
        = ((WTree.toGT_dom t).filter (fun w => w.length = d)).val.map (WTree.toGT_lab t)
  | WTree.mk i cs => by
      cases d with
      | zero =>
        show ({i} : Multiset ι)
          = ((insert ([] : List ℕ) (WTree.toGT_domChildren cs 0)).filter
              (fun w => w.length = 0)).val.map (WTree.toGT_lab (WTree.mk i cs))
        have hfilter : (insert ([] : List ℕ) (WTree.toGT_domChildren cs 0)).filter
              (fun w => w.length = 0) = {([] : List ℕ)} := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hw | hw, hlen⟩
            · exact hw
            · exact absurd hlen (by
                intro hcontra
                have := WTree.toGT_domChildren_length_pos cs 0 w hw
                omega)
          · rintro rfl; exact ⟨Or.inl rfl, rfl⟩
        rw [hfilter]
        simp only [Finset.singleton_val, Multiset.map_singleton]
        rfl
      | succ d =>
        show WTree.labelsAtDepthChildren cs d
          = ((insert ([] : List ℕ) (WTree.toGT_domChildren cs 0)).filter
              (fun w => w.length = d + 1)).val.map (WTree.toGT_lab (WTree.mk i cs))
        have hfilter : (insert ([] : List ℕ) (WTree.toGT_domChildren cs 0)).filter
              (fun w => w.length = d + 1)
            = (WTree.toGT_domChildren cs 0).filter (fun w => w.length = d + 1) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hw | hw, hlen⟩
            · subst hw; simp at hlen
            · exact ⟨hw, hlen⟩
          · rintro ⟨hw, hlen⟩; exact ⟨Or.inr hw, hlen⟩
        rw [hfilter]
        exact WTree.labelsAtDepthChildren_eq_domFilter_map d (WTree.mk i cs) cs 0 rfl

/-- Generalized over an explicit FIXED `whole` (the top node relative to
    which `toGT_lab` is evaluated) together with the invariant that the
    list currently being processed, `cs`, is exactly `whole.children`
    from position `idx0` onward -- this is what lets a recursive step
    (walking down `cs`, incrementing `idx0`) still correctly read labels
    off the SAME, unchanging `whole` via `toGT_lab whole`. -/
theorem WTree.labelsAtDepthChildren_eq_domFilter_map {ι : Type} (d : ℕ) (whole : WTree ι) :
    ∀ (cs : List (WTree ι)) (idx0 : ℕ), whole.children.drop idx0 = cs →
      WTree.labelsAtDepthChildren cs d
        = ((WTree.toGT_domChildren cs idx0).filter (fun w => w.length = d + 1)).val.map
            (WTree.toGT_lab whole)
  | [], idx0, _ => by simp [WTree.labelsAtDepthChildren, WTree.toGT_domChildren]
  | (c :: cs), idx0, hsuffix => by
      obtain ⟨hget, hsuffix'⟩ :=
        List.getElem?_and_drop_succ_of_drop_eq_cons idx0 whole.children c cs hsuffix
      show WTree.labelsAtDepth c d + WTree.labelsAtDepthChildren cs d
        = (((WTree.toGT_dom c).image (fun a => idx0 :: a)
              ∪ WTree.toGT_domChildren cs (idx0 + 1)).filter
            (fun w => w.length = d + 1)).val.map (WTree.toGT_lab whole)
      have hdisj : Disjoint ((WTree.toGT_dom c).image (fun a => idx0 :: a))
          (WTree.toGT_domChildren cs (idx0 + 1)) :=
        WTree.toGT_domChildren_head_disjoint c cs idx0
      have hdisj' : Disjoint (((WTree.toGT_dom c).image (fun a => idx0 :: a)).filter
            (fun w => w.length = d + 1))
          ((WTree.toGT_domChildren cs (idx0 + 1)).filter (fun w => w.length = d + 1)) :=
        hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      rw [Finset.filter_union, ← Finset.disjUnion_eq_union _ _ hdisj', Finset.disjUnion_val,
        Multiset.map_add]
      congr 1
      · have hfilter : ((WTree.toGT_dom c).image (fun a => idx0 :: a)).filter
              (fun w => w.length = d + 1)
            = ((WTree.toGT_dom c).filter (fun a => a.length = d)).image (fun a => idx0 :: a) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_image]
          constructor
          · rintro ⟨⟨a, ha, rfl⟩, hlen⟩
            exact ⟨a, ⟨ha, by simpa using hlen⟩, rfl⟩
          · rintro ⟨a, ⟨ha, hlen⟩, rfl⟩
            exact ⟨⟨a, ha, rfl⟩, by simp [hlen]⟩
        rw [hfilter]
        have hinj : Set.InjOn (fun a => idx0 :: a)
            ((WTree.toGT_dom c).filter (fun a => a.length = d) : Set (List ℕ)) := by
          intro a _ b _ hab
          injection hab with _ hab2
        rw [Finset.image_val_of_injOn hinj]
        rw [Multiset.map_map]
        have hlabeq : WTree.labelsAtDepth c d
            = ((WTree.toGT_dom c).filter (fun a => a.length = d)).val.map (WTree.toGT_lab c) :=
          WTree.labelsAtDepth_eq_domFilter_map d c
        rw [hlabeq]
        apply Multiset.map_congr rfl
        intro a ha
        simp only [Finset.mem_val, Finset.mem_filter] at ha
        show WTree.toGT_lab c a = WTree.toGT_lab whole (idx0 :: a)
        simp [WTree.toGT_lab, hget]
      · exact WTree.labelsAtDepthChildren_eq_domFilter_map d whole cs (idx0 + 1) hsuffix'
end

-- -------------------------------------------------------------------
-- Section 4: the result -- a purely-t-level, address-free hypothesis
-- (no two DISTINCT nodes at the same depth in `t` share a label, or are
-- neighbors) is exactly what `SameDepthIndependent P (toGrowingTree t)`
-- needs, transported via `labelsAtDepth_eq_domFilter_map` and
-- `Multiset.inj_on_of_nodup_map`. No canonicalize, no `toWTreeFuel`
-- roundtrip -- `toGT_dom`/`toGT_lab` read `t`'s OWN structure directly,
-- so this bridge is unconditional (holds for every WTree `t`, not just
-- canonicalized ones).
-- -------------------------------------------------------------------

theorem WTree.toGrowingTree_sameDepthIndependent_of_labelsAtDepth
    {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type} (P : MTProcess S ι) (t : WTree ι)
    (hnodup : ∀ d, (WTree.labelsAtDepth t d).Nodup)
    (hnbr : ∀ d (i j : ι), i ∈ WTree.labelsAtDepth t d → j ∈ WTree.labelsAtDepth t d →
      i ≠ j → ¬ neighbor P i j) :
    SameDepthIndependent P (WTree.toGrowingTree t) := by
  intro u v hu hv hlen hne
  have hu' : u ∈ ((WTree.toGT_dom t).filter (fun w => w.length = u.length)).val := by
    simp only [Finset.mem_val, Finset.mem_filter]
    exact ⟨hu, trivial⟩
  have hv' : v ∈ ((WTree.toGT_dom t).filter (fun w => w.length = u.length)).val := by
    simp only [Finset.mem_val, Finset.mem_filter]
    exact ⟨hv, hlen.symm⟩
  have hueq : WTree.toGT_lab t u ∈ WTree.labelsAtDepth t u.length := by
    rw [WTree.labelsAtDepth_eq_domFilter_map]
    exact Multiset.mem_map.mpr ⟨u, hu', rfl⟩
  have hveq : WTree.toGT_lab t v ∈ WTree.labelsAtDepth t u.length := by
    rw [WTree.labelsAtDepth_eq_domFilter_map]
    exact Multiset.mem_map.mpr ⟨v, hv', rfl⟩
  have hlabne : WTree.toGT_lab t u ≠ WTree.toGT_lab t v := by
    intro heq
    have hmapNodup : Multiset.Nodup
        (((WTree.toGT_dom t).filter (fun w => w.length = u.length)).val.map (WTree.toGT_lab t)) := by
      rw [← WTree.labelsAtDepth_eq_domFilter_map]; exact hnodup u.length
    exact hne (Multiset.inj_on_of_nodup_map hmapNodup u hu' v hv' heq)
  exact ⟨hlabne, hnbr u.length (WTree.toGT_lab t u) (WTree.toGT_lab t v) hueq hveq hlabne⟩

#check @WTree.toGT_lab
#check @WTree.toGT_dom
#check @WTree.toGrowingTree
#check @WTree.toGrowingTree_valid
#check @WTree.labelsAtDepth
#check @WTree.labelsAtDepth_eq_domFilter_map
#check @WTree.toGrowingTree_sameDepthIndependent_of_labelsAtDepth

-- Explicit checks for all remaining helper theorems.
#check @List.getElem?_and_drop_succ_of_drop_eq_cons
#check @WTree.labelsAtDepthChildren_eq_domFilter_map
#check @WTree.toGT_domChildren_head_disjoint
#check @WTree.toGT_domChildren_head_ge
#check @WTree.toGT_domChildren_length_pos
#check @WTree.toGT_domChildren_prefix_mem
#check @WTree.toGT_dom_prefix_mem
#check @WTree.toGT_dom_root_mem
