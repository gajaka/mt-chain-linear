/-
  PPGraphMoserTardosCheckBirth.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), Theorem 5.7.2, Lemma 2.1(ii).

  FIRST increment toward the correspondence proof (real trajectory
  occurrence ⟹ τ-check passes): "when was a tree vertex born", and the
  direct consequence that its label matches the scheduling function `C`
  at that real time. Both are genuine prerequisites for the eventual
  correspondence -- `checkState`/`τCheck` (PPGraphMoserTardosCheck.lean)
  are stated purely in terms of `T.lab w`, so nothing about how `T.lab w`
  relates to `C` can be assumed for free; it has to be established from
  `τBuild`'s own construction.

  `birthStep P C t w hw` is the SMALLEST construction step n at which w
  first appears in `τBuild P C t n`'s domain (`Nat.find` against the
  monotone-domain fact `dom_subset_τBuild_of_le`,
  PPGraphMoserTardosCheckOrder.lean). `birthTime` converts that step
  index into the REAL time it corresponds to, matching `τBuild`'s own
  `t - 1 - n` convention for step n+1 (uniformly `t - birthStep`, since
  the root's step 0 also matches `t - 0 = t`, its own real time in the
  paper's τ_C^{(t)}(t) := [C(t)] base case).

  `birth_label`: the vertex's label in the FINAL tree is exactly
  `C(birthTime w)` -- proved via `attachAt_lab_new_addr` (label at the
  moment of attachment) plus `label_stable_after_birth` (labels, once
  set, are frozen by every later `attachAt`, via `attachAt_lab_old`).

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.MoserTardos.Witness.Check

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- birthStep: the smallest construction step at which w is present
-- -------------------------------------------------------------------

/-- `w`'s birth step: the smallest `n` with `w ∈ (τBuild P C t n).dom`.
    Requires `w` to already be present in the FINAL tree `τC P C t`
    (`hw`) to supply `Nat.find`'s existence witness (step `t - 1`, since
    `τC P C t` unfolds to exactly `τBuild P C t (t - 1)`). -/
noncomputable def birthStep {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w : List ℕ)
    (hw : w ∈ (τC P C t).dom) : ℕ :=
  Nat.find (⟨t - 1, hw⟩ : ∃ n, w ∈ (τBuild P C t n).dom)

theorem birthStep_mem {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w : List ℕ) (hw : w ∈ (τC P C t).dom) :
    w ∈ (τBuild P C t (birthStep P C t w hw)).dom :=
  Nat.find_spec (⟨t - 1, hw⟩ : ∃ n, w ∈ (τBuild P C t n).dom)

/-- Minimality: `w` is absent at every step strictly before its birth. -/
theorem birthStep_not_mem_before {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w : List ℕ) (hw : w ∈ (τC P C t).dom)
    (m : ℕ) (hm : m < birthStep P C t w hw) :
    w ∉ (τBuild P C t m).dom :=
  Nat.find_min (⟨t - 1, hw⟩ : ∃ n, w ∈ (τBuild P C t n).dom) hm

/-- Once born, `w` stays present forever after (immediate from
    `birthStep_mem` plus dom-monotonicity). -/
theorem mem_τBuild_of_birthStep_le {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w : List ℕ) (hw : w ∈ (τC P C t).dom)
    (m : ℕ) (hm : birthStep P C t w hw ≤ m) :
    w ∈ (τBuild P C t m).dom :=
  dom_subset_τBuild_of_le P C t (birthStep P C t w hw) m hm (birthStep_mem P C t w hw)

/-- The root's birth step is 0 -- it is present from the very start
    (`τBuild P C t 0 = GrowingTree.singleton (C t)`, whose domain is
    exactly `{[]}`). -/
theorem birthStep_root {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (hw : ([] : List ℕ) ∈ (τC P C t).dom) :
    birthStep P C t [] hw = 0 := by
  have h0 : ([] : List ℕ) ∈ (τBuild P C t 0).dom := by
    show ([] : List ℕ) ∈ (GrowingTree.singleton (C t)).dom
    simp [GrowingTree.singleton]
  exact Nat.le_zero.mp (Nat.find_min' _ h0)

-- -------------------------------------------------------------------
-- birthTime: the real (chronological) time a vertex corresponds to
-- -------------------------------------------------------------------

/-- The real time `w` corresponds to: uniformly `t - birthStep`. Matches
    `τBuild`'s own indexing both at the root (step 0 ↦ real time `t`,
    since `t - 0 = t`) and at every later step (step `n + 1` ↦ real time
    `t - 1 - n`, since `t - (n + 1) = t - 1 - n` in `ℕ` whenever
    `n + 1 ≤ t`, which holds here because `birthStep ≤ t - 1 < t` by
    `Nat.find_min'` against the witness `t - 1`). -/
noncomputable def birthTime {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w : List ℕ) (hw : w ∈ (τC P C t).dom) : ℕ :=
  t - birthStep P C t w hw

-- -------------------------------------------------------------------
-- Labels are frozen once set: an `attachAt` never changes an OLD
-- vertex's label, so by induction a vertex's label at its birth step
-- persists to every later step, in particular to the final tree.
-- -------------------------------------------------------------------

/-- If `w` is already present at step `n`, its label at every LATER
    step `m ≥ n` equals its label at step `n` -- labels, once set, are
    never revisited by later attachments (`attachAt_lab_old`: an
    attachment only ever touches the ONE fresh address it inserts). -/
theorem τBuild_lab_stable {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w : List ℕ) (n : ℕ) (hw : w ∈ (τBuild P C t n).dom) :
    ∀ m, n ≤ m → (τBuild P C t m).lab w = (τBuild P C t n).lab w := by
  intro m hnm
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
      have hwk : w ∈ (τBuild P C t k).dom := dom_subset_τBuild_of_le P C t n k hk hw
      show ((τBuild P C t k).attachAt P (C (t - 1 - k))).lab w = (τBuild P C t n).lab w
      by_cases h : ((τBuild P C t k).candidates P (C (t - 1 - k))).Nonempty
      · rw [attachAt_lab_old P (τBuild P C t k) (C (t - 1 - k)) h w
              (fun he => newAttachAddr_not_mem P _ _ h (he ▸ hwk))]
        exact ih
      · have heq : (τBuild P C t k).attachAt P (C (t - 1 - k)) = τBuild P C t k := by
          rw [GrowingTree.attachAt, dite_eq_right h]
        rw [heq]
        exact ih

-- -------------------------------------------------------------------
-- birth_label: a vertex's label in the FINAL tree is exactly `C`
-- applied to its birth time -- the result of birthStep/birthTime/
-- τBuild_lab_stable, and the last ingredient before `τCheck`'s
-- `T.lab w` can be related to the real trajectory's scheduling at all.
-- -------------------------------------------------------------------

theorem birth_label {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w : List ℕ) (hw : w ∈ (τC P C t).dom) :
    (τC P C t).lab w = C (birthTime P C t w hw) := by
  have hle : birthStep P C t w hw ≤ t - 1 :=
    Nat.find_min' (⟨t - 1, hw⟩ : ∃ n, w ∈ (τBuild P C t n).dom) hw
  have hstable := τBuild_lab_stable P C t w (birthStep P C t w hw)
    (birthStep_mem P C t w hw) (t - 1) hle
  show (τBuild P C t (t - 1)).lab w = C (birthTime P C t w hw)
  rw [hstable]
  unfold birthTime
  generalize hn : birthStep P C t w hw = n
  rw [hn] at hstable
  match n, hn with
  | 0, hn0 =>
      have hmem0 : w ∈ (τBuild P C t 0).dom := hn0 ▸ birthStep_mem P C t w hw
      have hmem0' : w ∈ (GrowingTree.singleton (C t)).dom := hmem0
      have hw0 : w = [] := by
        simpa [GrowingTree.singleton] using hmem0'
      subst hw0
      show (GrowingTree.singleton (C t)).lab [] = C (t - 0)
      simp [GrowingTree.singleton]
  | m + 1, hnsucc =>
      have hmem : w ∈ (τBuild P C t (m + 1)).dom := hnsucc ▸ birthStep_mem P C t w hw
      have hnotmem : w ∉ (τBuild P C t m).dom :=
        birthStep_not_mem_before P C t w hw m (hnsucc ▸ Nat.lt_succ_self m)
      have hcand : ((τBuild P C t m).candidates P (C (t - 1 - m))).Nonempty := by
        by_contra hempty
        apply hnotmem
        have heq : (τBuild P C t m).attachAt P (C (t - 1 - m)) = τBuild P C t m := by
          rw [GrowingTree.attachAt, dite_eq_right hempty]
        have hmem' : w ∈ ((τBuild P C t m).attachAt P (C (t - 1 - m))).dom := hmem
        rw [heq] at hmem'
        exact hmem'
      have hweq : w = newAttachAddr P (τBuild P C t m) (C (t - 1 - m)) hcand := by
        have hins := attachAt_dom_eq_insert P (τBuild P C t m) (C (t - 1 - m)) hcand
        have hmem' : w ∈ ((τBuild P C t m).attachAt P (C (t - 1 - m))).dom := hmem
        rw [hins, Finset.mem_insert] at hmem'
        rcases hmem' with h | h
        · exact h
        · exact absurd h hnotmem
      show ((τBuild P C t m).attachAt P (C (t - 1 - m))).lab w = C (t - (m + 1))
      rw [hweq, attachAt_lab_new_addr]
      congr 1
      omega

-- -------------------------------------------------------------------
-- birthStep/birthTime injectivity: distinct tree vertices are born at
-- distinct steps, hence at distinct real times -- each construction
-- step adds AT MOST ONE new vertex, so `birthStep` is genuinely a
-- per-vertex "birth certificate". Needed later to turn `localCount`'s
-- tree-based counting into a real-time-based one: birth times form a
-- genuine INJECTION from `T.dom` into `{0, ..., t}`, so "how many
-- deeper vertices" can be read off as "how many distinct earlier birth
-- times" without double-counting.
-- -------------------------------------------------------------------

theorem birthStep_eq_zero_iff {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w : List ℕ) (hw : w ∈ (τC P C t).dom) :
    birthStep P C t w hw = 0 ↔ w = [] := by
  constructor
  · intro h0
    have hmem0 : w ∈ (τBuild P C t 0).dom := h0 ▸ birthStep_mem P C t w hw
    have hmem0' : w ∈ (GrowingTree.singleton (C t)).dom := hmem0
    simpa [GrowingTree.singleton] using hmem0'
  · intro hw0
    subst hw0
    exact birthStep_root P C t hw

theorem birthStep_inj {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w1 w2 : List ℕ)
    (hw1 : w1 ∈ (τC P C t).dom) (hw2 : w2 ∈ (τC P C t).dom)
    (heq : birthStep P C t w1 hw1 = birthStep P C t w2 hw2) : w1 = w2 := by
  rcases Nat.eq_zero_or_pos (birthStep P C t w1 hw1) with h0 | hpos
  · have hw10 : w1 = [] := (birthStep_eq_zero_iff P C t w1 hw1).mp h0
    have h0' : birthStep P C t w2 hw2 = 0 := by rw [← heq]; exact h0
    have hw20 : w2 = [] := (birthStep_eq_zero_iff P C t w2 hw2).mp h0'
    rw [hw10, hw20]
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [Nat.succ_eq_add_one] at hm
    have hm2 : birthStep P C t w2 hw2 = m + 1 := by rw [← heq]; exact hm
    have hmem1 : w1 ∈ (τBuild P C t (m + 1)).dom := hm ▸ birthStep_mem P C t w1 hw1
    have hmem2 : w2 ∈ (τBuild P C t (m + 1)).dom := hm2 ▸ birthStep_mem P C t w2 hw2
    have hnotmem1 : w1 ∉ (τBuild P C t m).dom :=
      birthStep_not_mem_before P C t w1 hw1 m (hm ▸ Nat.lt_succ_self m)
    have hnotmem2 : w2 ∉ (τBuild P C t m).dom :=
      birthStep_not_mem_before P C t w2 hw2 m (hm2 ▸ Nat.lt_succ_self m)
    have hcand : ((τBuild P C t m).candidates P (C (t - 1 - m))).Nonempty := by
      by_contra hempty
      apply hnotmem1
      have heqT : (τBuild P C t m).attachAt P (C (t - 1 - m)) = τBuild P C t m := by
        rw [GrowingTree.attachAt, dite_eq_right hempty]
      have hmem1' : w1 ∈ ((τBuild P C t m).attachAt P (C (t - 1 - m))).dom := hmem1
      rw [heqT] at hmem1'
      exact hmem1'
    have hins := attachAt_dom_eq_insert P (τBuild P C t m) (C (t - 1 - m)) hcand
    have hweq1 : w1 = newAttachAddr P (τBuild P C t m) (C (t - 1 - m)) hcand := by
      have hmem1' : w1 ∈ ((τBuild P C t m).attachAt P (C (t - 1 - m))).dom := hmem1
      rw [hins, Finset.mem_insert] at hmem1'
      rcases hmem1' with h | h
      · exact h
      · exact absurd h hnotmem1
    have hweq2 : w2 = newAttachAddr P (τBuild P C t m) (C (t - 1 - m)) hcand := by
      have hmem2' : w2 ∈ ((τBuild P C t m).attachAt P (C (t - 1 - m))).dom := hmem2
      rw [hins, Finset.mem_insert] at hmem2'
      rcases hmem2' with h | h
      · exact h
      · exact absurd h hnotmem2
    rw [hweq1, hweq2]

theorem birthTime_inj {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w1 w2 : List ℕ)
    (hw1 : w1 ∈ (τC P C t).dom) (hw2 : w2 ∈ (τC P C t).dom)
    (heq : birthTime P C t w1 hw1 = birthTime P C t w2 hw2) : w1 = w2 := by
  have hle1 : birthStep P C t w1 hw1 ≤ t - 1 :=
    Nat.find_min' (⟨t - 1, hw1⟩ : ∃ n, w1 ∈ (τBuild P C t n).dom) hw1
  have hle2 : birthStep P C t w2 hw2 ≤ t - 1 :=
    Nat.find_min' (⟨t - 1, hw2⟩ : ∃ n, w2 ∈ (τBuild P C t n).dom) hw2
  apply birthStep_inj P C t w1 w2 hw1 hw2
  unfold birthTime at heq
  omega

-- -------------------------------------------------------------------
-- Reusable birth-step case-split helpers -- the SAME "w born at a
-- successor step ⟹ w is exactly the new address" argument that
-- birth_label and birthStep_inj each re-derive inline, factored out
-- since the depth/birth-order correspondence below needs it a third
-- time.
-- -------------------------------------------------------------------

theorem candidates_nonempty_of_birthStep_eq_succ {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w : List ℕ) (hw : w ∈ (τC P C t).dom)
    (m : ℕ) (hm : birthStep P C t w hw = m + 1) :
    ((τBuild P C t m).candidates P (C (t - 1 - m))).Nonempty := by
  have hmem : w ∈ (τBuild P C t (m + 1)).dom := hm ▸ birthStep_mem P C t w hw
  have hnotmem : w ∉ (τBuild P C t m).dom :=
    birthStep_not_mem_before P C t w hw m (hm ▸ Nat.lt_succ_self m)
  by_contra hempty
  apply hnotmem
  have heqT : (τBuild P C t m).attachAt P (C (t - 1 - m)) = τBuild P C t m := by
    rw [GrowingTree.attachAt, dite_eq_right hempty]
  have hmem' : w ∈ ((τBuild P C t m).attachAt P (C (t - 1 - m))).dom := hmem
  rw [heqT] at hmem'
  exact hmem'

theorem eq_newAttachAddr_of_birthStep_eq_succ {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w : List ℕ) (hw : w ∈ (τC P C t).dom)
    (m : ℕ) (hm : birthStep P C t w hw = m + 1)
    (hcand : ((τBuild P C t m).candidates P (C (t - 1 - m))).Nonempty) :
    w = newAttachAddr P (τBuild P C t m) (C (t - 1 - m)) hcand := by
  have hmem : w ∈ (τBuild P C t (m + 1)).dom := hm ▸ birthStep_mem P C t w hw
  have hnotmem : w ∉ (τBuild P C t m).dom :=
    birthStep_not_mem_before P C t w hw m (hm ▸ Nat.lt_succ_self m)
  have hins := attachAt_dom_eq_insert P (τBuild P C t m) (C (t - 1 - m)) hcand
  have hmem' : w ∈ ((τBuild P C t m).attachAt P (C (t - 1 - m))).dom := hmem
  rw [hins, Finset.mem_insert] at hmem'
  rcases hmem' with h | h
  · exact h
  · exact absurd h hnotmem

theorem birthStep_le_pred {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w : List ℕ) (hw : w ∈ (τC P C t).dom) :
    birthStep P C t w hw ≤ t - 1 :=
  Nat.find_min' (⟨t - 1, hw⟩ : ∃ n, w ∈ (τBuild P C t n).dom) hw

/-- Two events sharing a variable are either equal or dependency-graph
    neighbors -- the direct bridge from `localCount`'s "same VARIABLE"
    bookkeeping to `candidates`'s "same-or-neighboring LABEL" test. -/
theorem footprint_common_var_same_or_neighbor {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (a b : ι) (v : V) (hva : v ∈ P.footprint a) (hvb : v ∈ P.footprint b) :
    a = b ∨ neighbor P a b := by
  by_cases hab : a = b
  · exact Or.inl hab
  · refine Or.inr (fun hdisj => ?_)
    exact (Finset.disjoint_left.mp hdisj hva) hvb

-- -------------------------------------------------------------------
-- The depth/birth-order correspondence for SAME-VARIABLE vertices:
-- Moser-Tardos's "q(u) < q(v) and vbl(u), vbl(v) overlap ⟹ d(u) >
-- d(v)" (Lemma 2.1's proof), now stated directly against REAL TIME
-- (`birthStep`) rather than abstract construction order. Proved via
-- `τBuild_attach_deeper_than_prior` (the single-step fact) applied at
-- the exact step where the later-born vertex is attached: labels are
-- frozen (`τBuild_lab_stable`) so `w`'s label at that step is its
-- FINAL label, and a shared variable forces same-or-neighbor labels
-- (`footprint_common_var_same_or_neighbor`), giving `w` as a genuine
-- candidate at that step -- hence `w` ends up strictly shallower than
-- the newly attached `w'`.
-- -------------------------------------------------------------------

theorem birthStep_lt_imp_length_lt {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w w' : List ℕ)
    (hw : w ∈ (τC P C t).dom) (hw' : w' ∈ (τC P C t).dom)
    (v : V) (hvw : v ∈ P.footprint ((τC P C t).lab w))
    (hvw' : v ∈ P.footprint ((τC P C t).lab w'))
    (hlt : birthStep P C t w hw < birthStep P C t w' hw') :
    w.length < w'.length := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (show birthStep P C t w' hw' ≠ 0 by omega)
  rw [Nat.succ_eq_add_one] at hk
  have hcand := candidates_nonempty_of_birthStep_eq_succ P C t w' hw' k hk
  have hweq' := eq_newAttachAddr_of_birthStep_eq_succ P C t w' hw' k hk hcand
  have hkle : birthStep P C t w hw ≤ k := by omega
  have hwmem : w ∈ (τBuild P C t (birthStep P C t w hw)).dom := birthStep_mem P C t w hw
  have hwle : birthStep P C t w hw ≤ t - 1 := birthStep_le_pred P C t w hw
  have hlabk : (τBuild P C t k).lab w = (τC P C t).lab w := by
    have h1 := τBuild_lab_stable P C t w (birthStep P C t w hw) hwmem k hkle
    have h2 := τBuild_lab_stable P C t w (birthStep P C t w hw) hwmem (t - 1) hwle
    show (τBuild P C t k).lab w = (τBuild P C t (t - 1)).lab w
    rw [h1, ← h2]
  have hlabw' : C (t - 1 - k) = (τC P C t).lab w' := by
    have hbt := birth_label P C t w' hw'
    have hbteq : birthTime P C t w' hw' = t - 1 - k := by
      unfold birthTime
      omega
    rw [hbteq] at hbt
    exact hbt.symm
  have hlab : (τBuild P C t k).lab w = C (t - 1 - k) ∨
      neighbor P ((τBuild P C t k).lab w) (C (t - 1 - k)) := by
    rw [hlabk, hlabw']
    exact footprint_common_var_same_or_neighbor P ((τC P C t).lab w) ((τC P C t).lab w') v hvw hvw'
  have hdeep := τBuild_attach_deeper_than_prior P C t k hcand w
    (birthStep P C t w hw) hkle hwmem hlab
  rw [← hweq'] at hdeep
  exact hdeep

/-- The full order-isomorphism: for two DISTINCT vertices sharing a
    variable, earlier birth ⟺ shallower depth. The forward direction is
    `birthStep_lt_imp_length_lt`; the reverse follows from trichotomy on
    `birthStep` (`birthStep_inj` rules out equality for `w ≠ w'`) plus
    the same forward fact applied with the roles of `w`, `w'` swapped --
    no separate use of `τBuild_sameDepthIndependent` is needed, since
    `birthStep_lt_imp_length_lt` already pins down a STRICT depth
    ordering in both directions. -/
theorem birthStep_lt_iff_length_lt {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w w' : List ℕ)
    (hw : w ∈ (τC P C t).dom) (hw' : w' ∈ (τC P C t).dom) (hne : w ≠ w')
    (v : V) (hvw : v ∈ P.footprint ((τC P C t).lab w))
    (hvw' : v ∈ P.footprint ((τC P C t).lab w')) :
    birthStep P C t w hw < birthStep P C t w' hw' ↔ w.length < w'.length := by
  constructor
  · exact birthStep_lt_imp_length_lt P C t w w' hw hw' v hvw hvw'
  · intro hlen
    by_contra hnotlt
    have hstepge : birthStep P C t w' hw' ≤ birthStep P C t w hw := by omega
    rcases hstepge.lt_or_eq with hstepslt | hstepseq
    · have := birthStep_lt_imp_length_lt P C t w' w hw' hw v hvw' hvw hstepslt
      omega
    · have heqw := birthStep_inj P C t w' w hw' hw hstepseq
      exact hne heqw.symm

-- -------------------------------------------------------------------
-- Towards SURJECTIVITY: every real occurrence of a variable already
-- used by an EXISTING tree vertex is guaranteed to get attached. Two
-- pieces: (1) sharing a variable with an already-present vertex is
-- enough for `candidates` to be nonempty at that step; (2) a vertex
-- attached AT a given construction step has EXACTLY that step as its
-- `birthStep` (the converse of `eq_newAttachAddr_of_birthStep_eq_succ`).
-- Together these will let a later theorem show: for w ∈ T.dom using v,
-- EVERY real time s < birthTime(w) with v ∈ footprint(C(s)) has SOME
-- tree vertex born there -- no induction needed, since w's own
-- presence (by dom-monotonicity, its birthStep is fixed) already
-- supplies the needed candidate at every such earlier step.
-- -------------------------------------------------------------------

/-- If SOME already-present vertex `w` shares variable `v` with the
    label `a` about to be processed, `a` has a candidate (namely `w`
    itself) -- so `attachAt` is guaranteed to attach a new vertex. -/
theorem candidates_nonempty_of_var_used {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (a : ι) (v : V) (hva : v ∈ P.footprint a)
    (w : List ℕ) (hw : w ∈ T.dom) (hwv : v ∈ P.footprint (T.lab w)) :
    (T.candidates P a).Nonempty := by
  refine ⟨w, ?_⟩
  rw [mem_candidates_iff]
  exact ⟨hw, footprint_common_var_same_or_neighbor P (T.lab w) a v hwv hva⟩

/-- Converse of `eq_newAttachAddr_of_birthStep_eq_succ`: a vertex that
    IS the address `attachAt` inserts at construction step `n+1` has
    `birthStep` exactly `n+1` -- it is present from step `n+1` on
    (`newAttachAddr_mem_attachAt_dom`) and absent at step `n`
    (`newAttachAddr_not_mem`), and `birthStep` is the LEAST step of
    presence, so no step `≤ n` can already contain it. -/
theorem birthStep_eq_succ_of_new_attach {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (n : ℕ)
    (hcand : ((τBuild P C t n).candidates P (C (t - 1 - n))).Nonempty)
    (u : List ℕ) (hu_eq : u = newAttachAddr P (τBuild P C t n) (C (t - 1 - n)) hcand)
    (hu : u ∈ (τC P C t).dom) :
    birthStep P C t u hu = n + 1 := by
  have hmem_succ : u ∈ (τBuild P C t (n + 1)).dom := by
    rw [hu_eq]
    exact newAttachAddr_mem_attachAt_dom P (τBuild P C t n) (C (t - 1 - n)) hcand
  have hnotmem_n : u ∉ (τBuild P C t n).dom := by
    rw [hu_eq]
    exact newAttachAddr_not_mem P (τBuild P C t n) (C (t - 1 - n)) hcand
  have hle : birthStep P C t u hu ≤ n + 1 :=
    Nat.find_min' (⟨n + 1, hmem_succ⟩ : ∃ k, u ∈ (τBuild P C t k).dom) hmem_succ
  by_contra hne
  have hlt : birthStep P C t u hu ≤ n := by omega
  exact hnotmem_n (mem_τBuild_of_birthStep_le P C t u hu n hlt)

-- -------------------------------------------------------------------
-- SURJECTIVITY: every real time strictly between w's birth and the
-- root, whose event shares w's variable, has SOME tree vertex born
-- there. Needed (alongside `birthStep_lt_iff_length_lt`) to turn
-- `localCount`'s tree-based count into a genuine bijection with real
-- occurrences -- PPGraphMoserTardosCorrespondence.lean's job.
-- -------------------------------------------------------------------

/-- A vertex's label at any earlier-or-equal construction step already
    equals its FINAL label -- `τBuild_lab_stable` specialized against
    `birthStep`'s own minimality (via `Nat.find_min'`) instead of
    requiring the caller to separately track `w`'s birth step. -/
theorem τBuild_lab_eq_final {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w : List ℕ) (hw : w ∈ (τC P C t).dom)
    (n : ℕ) (hwn : w ∈ (τBuild P C t n).dom) :
    (τBuild P C t n).lab w = (τC P C t).lab w := by
  have hble : birthStep P C t w hw ≤ n :=
    Nat.find_min' (⟨t - 1, hw⟩ : ∃ k, w ∈ (τBuild P C t k).dom) hwn
  have h1 := τBuild_lab_stable P C t w (birthStep P C t w hw) (birthStep_mem P C t w hw) n hble
  have h2 := τBuild_lab_stable P C t w (birthStep P C t w hw) (birthStep_mem P C t w hw)
    (t - 1) (birthStep_le_pred P C t w hw)
  show (τBuild P C t n).lab w = (τBuild P C t (t - 1)).lab w
  rw [h1, ← h2]

/-- SURJECTIVITY: given `w ∈ T.dom` using variable `v`, every real time
    `r` strictly between `1` and `w`'s own birth time whose event ALSO
    uses `v` has a tree vertex born there. Proof: `w` is already
    present (by dom-monotonicity, its `birthStep` is fixed) at the
    construction step that processes time `r`, so it directly supplies
    a candidate (`candidates_nonempty_of_var_used`) -- forcing
    `attachAt` to attach a new vertex there, which
    `birthStep_eq_succ_of_new_attach` identifies as having `birthStep`
    exactly matching, and `birthStep_lt_imp_length_lt` places strictly
    deeper than `w`. The `1 ≤ r` bound is essential: real time `0` is
    never scanned by `τC` (it runs indices `t-1` down to `1`, matching
    Moser-Tardos's own 1-indexed convention), so no vertex can ever be
    born there. -/
theorem exists_birth_of_earlier_real_time {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w : List ℕ) (hw : w ∈ (τC P C t).dom)
    (v : V) (hwv : v ∈ P.footprint ((τC P C t).lab w))
    (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r < birthTime P C t w hw) (hrv : v ∈ P.footprint (C r)) :
    ∃ (w' : List ℕ) (hw' : w' ∈ (τC P C t).dom),
      (τC P C t).lab w' = C r ∧ birthTime P C t w' hw' = r ∧ w.length < w'.length := by
  have hr2' : r < t - birthStep P C t w hw := by
    have h := hr2
    unfold birthTime at h
    exact h
  have hwle : birthStep P C t w hw ≤ t - 1 - r := by omega
  have hwmem_n : w ∈ (τBuild P C t (t - 1 - r)).dom :=
    mem_τBuild_of_birthStep_le P C t w hw (t - 1 - r) hwle
  have hlab_n : (τBuild P C t (t - 1 - r)).lab w = (τC P C t).lab w :=
    τBuild_lab_eq_final P C t w hw (t - 1 - r) hwmem_n
  have hva : v ∈ P.footprint (C (t - 1 - (t - 1 - r))) := by
    rw [show t - 1 - (t - 1 - r) = r by omega]
    exact hrv
  have hwv_n : v ∈ P.footprint ((τBuild P C t (t - 1 - r)).lab w) := by
    rw [hlab_n]; exact hwv
  have hcand : ((τBuild P C t (t - 1 - r)).candidates P (C (t - 1 - (t - 1 - r)))).Nonempty :=
    candidates_nonempty_of_var_used P (τBuild P C t (t - 1 - r)) (C (t - 1 - (t - 1 - r))) v hva
      w hwmem_n hwv_n
  set w' := newAttachAddr P (τBuild P C t (t - 1 - r)) (C (t - 1 - (t - 1 - r))) hcand with hw'def
  have hw'_mem_succ : w' ∈ (τBuild P C t (t - 1 - r + 1)).dom :=
    newAttachAddr_mem_attachAt_dom P (τBuild P C t (t - 1 - r)) (C (t - 1 - (t - 1 - r))) hcand
  have hn1t : t - 1 - r + 1 ≤ t - 1 := by omega
  have hw'_mem_final : w' ∈ (τC P C t).dom :=
    dom_subset_τBuild_of_le P C t (t - 1 - r + 1) (t - 1) hn1t hw'_mem_succ
  have hbirthstep : birthStep P C t w' hw'_mem_final = t - 1 - r + 1 :=
    birthStep_eq_succ_of_new_attach P C t (t - 1 - r) hcand w' hw'def hw'_mem_final
  have hbirthtime : birthTime P C t w' hw'_mem_final = r := by
    unfold birthTime
    omega
  have hlabel : (τC P C t).lab w' = C r := by
    have hbl := birth_label P C t w' hw'_mem_final
    rw [hbirthtime] at hbl
    exact hbl
  have hvw' : v ∈ P.footprint ((τC P C t).lab w') := by rw [hlabel]; exact hrv
  have hlt : birthStep P C t w hw < birthStep P C t w' hw'_mem_final := by omega
  have hdepth : w.length < w'.length :=
    birthStep_lt_imp_length_lt P C t w w' hw hw'_mem_final v hwv hvw' hlt
  exact ⟨w', hw'_mem_final, hlabel, hbirthtime, hdepth⟩

-- -------------------------------------------------------------------
-- Towards Lemma 2.1(ii)'s PROBABILITY half: the log-coordinate pairs
-- `(v, localCount P T w v)` that `checkState`/`τCheck` read are
-- PAIRWISE DISTINCT across `(w, v)` -- the combinatorial prerequisite
-- for the independence argument (`Pr[τ-check passes] = ∏ Pr[bad]`)
-- that the FULL probability bound needs. First a fact about ANY
-- GrowingTree (no `τC`-specific machinery at all): among vertices
-- sharing a variable, `localCount` is STRICTLY ANTITONE in depth,
-- straight from Finset containment. Then, specialized to `τC`-built
-- trees via `τBuild_sameDepthIndependent`, this becomes genuine
-- injectivity.
-- -------------------------------------------------------------------

/-- General fact about ANY `GrowingTree`: if two in-domain vertices
    share a variable and one is strictly shallower than the other, the
    shallower one's `localCount` for that variable is STRICTLY BIGGER
    -- the deeper vertex `w2` is itself one of the extra elements
    counted from `w1`'s (lower) depth threshold but excluded from its
    own, so `localCount`'s underlying Finset strictly shrinks with
    depth. -/
theorem localCount_strict_anti {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (w1 w2 : List ℕ)
    (hw1 : w1 ∈ T.dom) (hw2 : w2 ∈ T.dom) (v : V)
    (hv1 : v ∈ P.footprint (T.lab w1)) (hv2 : v ∈ P.footprint (T.lab w2))
    (hlt : w1.length < w2.length) :
    localCount P T w2 v < localCount P T w1 v := by
  unfold localCount
  have hsub : (T.dom.filter (fun w' => w2.length < w'.length ∧ v ∈ P.footprint (T.lab w')))
      ⊆ (T.dom.filter (fun w' => w1.length < w'.length ∧ v ∈ P.footprint (T.lab w'))) := by
    intro w' hw'
    rw [Finset.mem_filter] at hw' ⊢
    exact ⟨hw'.1, hlt.trans hw'.2.1, hw'.2.2⟩
  have hmem : w2 ∈ T.dom.filter (fun w' => w1.length < w'.length ∧ v ∈ P.footprint (T.lab w')) :=
    Finset.mem_filter.mpr ⟨hw2, hlt, hv2⟩
  have hnotmem : w2 ∉ T.dom.filter (fun w' => w2.length < w'.length ∧ v ∈ P.footprint (T.lab w')) := by
    intro h
    exact absurd (Finset.mem_filter.mp h).2.1 (lt_irrefl _)
  exact Finset.card_lt_card (Finset.ssubset_iff_of_subset hsub |>.mpr ⟨w2, hmem, hnotmem⟩)

/-- Specialized to `τC`-built trees: DISTINCT vertices sharing a
    variable always have DIFFERENT `localCount` for it. Combines
    `localCount_strict_anti` (handles the case of different depths)
    with `τBuild_sameDepthIndependent` (rules out the SAME-depth case
    entirely, since sharing a variable there would already be a
    contradiction). -/
theorem localCount_ne_of_ne {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (w1 w2 : List ℕ)
    (hw1 : w1 ∈ (τC P C t).dom) (hw2 : w2 ∈ (τC P C t).dom) (hne : w1 ≠ w2)
    (v : V) (hv1 : v ∈ P.footprint ((τC P C t).lab w1))
    (hv2 : v ∈ P.footprint ((τC P C t).lab w2)) :
    localCount P (τC P C t) w1 v ≠ localCount P (τC P C t) w2 v := by
  rcases lt_trichotomy w1.length w2.length with hlt | heqlen | hgt
  · exact ne_of_gt (localCount_strict_anti P (τC P C t) w1 w2 hw1 hw2 v hv1 hv2 hlt)
  · exfalso
    have hind := τBuild_sameDepthIndependent P C t (t - 1)
    obtain ⟨hlabne, hnotneighbor⟩ := hind w1 w2 hw1 hw2 heqlen hne
    rcases footprint_common_var_same_or_neighbor P ((τC P C t).lab w1) ((τC P C t).lab w2) v hv1 hv2
      with heq' | hneighbor'
    · exact hlabne heq'
    · exact hnotneighbor hneighbor'
  · exact ne_of_lt (localCount_strict_anti P (τC P C t) w2 w1 hw2 hw1 v hv2 hv1 hgt)

/-- THE distinctness fact `τCheck`'s independence argument needs:
    the log-coordinate pair `(v, localCount)` a vertex `w` reads for
    variable `v` uniquely identifies `w` -- two vertices reading the
    SAME variable at the SAME index must be the SAME vertex. -/
theorem checkState_indices_injective {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ)
    (w1 w2 : List ℕ) (hw1 : w1 ∈ (τC P C t).dom) (hw2 : w2 ∈ (τC P C t).dom)
    (v1 v2 : V) (hv1 : v1 ∈ P.footprint ((τC P C t).lab w1))
    (hv2 : v2 ∈ P.footprint ((τC P C t).lab w2))
    (hveq : v1 = v2)
    (hidxeq : localCount P (τC P C t) w1 v1 = localCount P (τC P C t) w2 v2) :
    w1 = w2 := by
  by_contra hne
  subst hveq
  exact localCount_ne_of_ne P C t w1 w2 hw1 hw2 hne v1 hv1 hv2 hidxeq

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @birthStep
#check @birthStep_mem
#check @birthStep_not_mem_before
#check @mem_τBuild_of_birthStep_le
#check @birthStep_root
#check @birthTime
#check @birthStep_eq_zero_iff
#check @birthStep_inj
#check @birthTime_inj
#check @τBuild_lab_stable
#check @birth_label
#check @candidates_nonempty_of_birthStep_eq_succ
#check @eq_newAttachAddr_of_birthStep_eq_succ
#check @birthStep_le_pred
#check @footprint_common_var_same_or_neighbor
#check @birthStep_lt_imp_length_lt
#check @birthStep_lt_iff_length_lt
#check @candidates_nonempty_of_var_used
#check @birthStep_eq_succ_of_new_attach
#check @τBuild_lab_eq_final
#check @exists_birth_of_earlier_real_time
#check @localCount_strict_anti
#check @localCount_ne_of_ne
#check @checkState_indices_injective
