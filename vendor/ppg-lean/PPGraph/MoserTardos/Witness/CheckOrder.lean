/-
  PPGraphMoserTardosCheckOrder.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), Theorem 5.7.2 groundwork.

  Verified directly against the source (Moser-Tardos, "A constructive
  proof of the general Lovász Local Lemma", arXiv:0903.0544v3, Section 2,
  Lemma 2.1), not reconstructed from memory - read on 2026-09-20 before
  writing anything here. Lemma 2.1(i)'s properness claim ("if q(u) < q(v)
  and vbl(u), vbl(v) overlap, then d(u) > d(v)") rests on ONE single-step
  fact about `GrowingTree.attachAt`: when a new vertex is attached, EVERY
  candidate for that attachment (in particular any already-present vertex
  sharing a variable with the new label) has address-length at most the
  chosen (max-depth) candidate's - so the newly attached vertex, one level
  deeper than whichever candidate was actually chosen, is STRICTLY deeper
  than every candidate, chosen or not. This file proves exactly that
  single-step fact from the existing `attachAt`/`candidates`/
  `exists_max_depth_candidate` machinery (PPGraphMoserTardosGrowing.lean) -
  no new construction needed, only a genuinely new theorem about the
  existing one.

  Scope, deliberately: this is the LOCAL, single-attachment-step version
  of Lemma 2.1(i), the actual combinatorial engine underneath it. The full
  GLOBAL statement (q(u) < q(v) globally across the whole τ_C(t)
  construction, and its corollary that same-depth vertices have pairwise
  disjoint variable sets) is NOT attempted here - that needs threading
  this single-step fact through the τBuild recursion, a separate,
  substantial next increment. Likewise the τ-check procedure itself
  (Lemma 2.1's "decreasing depth, S(P)-indexed" reading) and its
  correspondence to the real trajectory's per-variable counters
  (`randStep`/`randCount_le`, PPGraphMoserTardosRandomTrajectory.lean) are
  future work, not attempted in this file.

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.MoserTardos.Witness.Growing

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- The single-attachment-step depth fact (core of Lemma 2.1(i))
-- -------------------------------------------------------------------

/-- Every candidate for an attachment has address-length at most the
    CHOSEN (max-depth) candidate's - immediate from
    `exists_max_depth_candidate`'s own spec, isolated here so the main
    theorem's proof is a clean two-line arithmetic step. -/
theorem candidate_length_le_chosen {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (a : ι)
    (h : (T.candidates P a).Nonempty) (v : List ℕ) (hv : v ∈ T.candidates P a) :
    v.length ≤ (Classical.choose (exists_max_depth_candidate (T.candidates P a) h)).length :=
  (Classical.choose_spec (exists_max_depth_candidate (T.candidates P a) h)).2 v hv

/-- The address `attachAt` actually inserts, when it does insert one -
    the chosen candidate's address with a fresh child index appended.
    Named separately so later theorems can refer to "the new vertex"
    without re-deriving this from `attachAt`'s `if`/`dif` unfolding
    every time. -/
noncomputable def newAttachAddr {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (a : ι)
    (h : (T.candidates P a).Nonempty) : List ℕ :=
  let chosen := Classical.choose (exists_max_depth_candidate (T.candidates P a) h)
  chosen ++ [T.freshIndex chosen]

theorem newAttachAddr_mem_attachAt_dom {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (a : ι) (h : (T.candidates P a).Nonempty) :
    newAttachAddr P T a h ∈ (T.attachAt P a).dom := by
  unfold GrowingTree.attachAt
  rw [dite_eq_left h]
  unfold GrowingTree.attachChild newAttachAddr
  exact Finset.mem_insert_self _ _

theorem attachAt_lab_new_addr {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (a : ι) (h : (T.candidates P a).Nonempty) :
    (T.attachAt P a).lab (newAttachAddr P T a h) = a := by
  unfold GrowingTree.attachAt
  rw [dite_eq_left h]
  unfold GrowingTree.attachChild newAttachAddr
  simp

/-- THE core single-step fact: whenever an attachment actually happens,
    the newly attached vertex is STRICTLY deeper than every candidate for
    that attachment - not just the one chosen. Verified against
    Moser-Tardos arXiv:0903.0544v3 Lemma 2.1's proof: this is exactly the
    mechanism behind "if q(u) < q(v) [u attached later, so v was already
    a candidate when u was attached] and vbl(u), vbl(v) overlap [so v IS
    a candidate for u's label], then d(u) > d(v)". -/
theorem attachAt_new_vertex_deeper_than_any_candidate {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (a : ι) (h : (T.candidates P a).Nonempty)
    (v : List ℕ) (hv : v ∈ T.candidates P a) :
    v.length < (newAttachAddr P T a h).length := by
  unfold newAttachAddr
  rw [List.length_append, List.length_singleton]
  have := candidate_length_le_chosen P T a h v hv
  omega

/-- Candidacy is exactly shared-or-equal labels - restates `candidates`'
    own definition as membership plus a disjunction, so callers reasoning
    about `dependent`/`neighbor` (the actual CPS-level vocabulary from
    PPGraphProbabilistic.lean / PPGraphMoserTardosWitness.lean) don't need
    to unfold `GrowingTree.candidates` by hand. -/
theorem mem_candidates_iff {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (a : ι) (v : List ℕ) :
    v ∈ T.candidates P a ↔ v ∈ T.dom ∧ (T.lab v = a ∨ neighbor P (T.lab v) a) := by
  unfold GrowingTree.candidates
  rw [Finset.mem_filter]

/-- `newAttachAddr` is genuinely fresh - never already in `T.dom` - by
    `freshIndex_spec` applied to the chosen candidate. -/
theorem newAttachAddr_not_mem {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (a : ι) (h : (T.candidates P a).Nonempty) :
    newAttachAddr P T a h ∉ T.dom := by
  unfold newAttachAddr
  exact T.freshIndex_spec _

/-- The attach-case `dom` is exactly the old `dom` plus `newAttachAddr` -
    an explicit rewrite lemma so later proofs don't have to re-derive
    this unfold each time. -/
theorem attachAt_dom_eq_insert {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (a : ι) (h : (T.candidates P a).Nonempty) :
    (T.attachAt P a).dom = insert (newAttachAddr P T a h) T.dom := by
  unfold GrowingTree.attachAt
  rw [dite_eq_left h]
  rfl

/-- Labels of OLD addresses are unchanged by an attachment - the other
    half of `attachAt_lab_new_addr`. Unfolds `newAttachAddr` INSIDE the
    hypothesis first, so the later `attachChild`-unfold on the goal
    produces an `if` whose condition is syntactically the same term
    `hw` already talks about. -/
theorem attachAt_lab_old {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (a : ι) (h : (T.candidates P a).Nonempty)
    (w : List ℕ) (hw : w ≠ newAttachAddr P T a h) :
    (T.attachAt P a).lab w = T.lab w := by
  unfold newAttachAddr at hw
  unfold GrowingTree.attachAt
  rw [dite_eq_left h]
  unfold GrowingTree.attachChild
  simp only
  rw [ite_eq_right hw]

-- -------------------------------------------------------------------
-- Threading the single-step fact through the REAL τC(t) construction
-- (dom only grows across steps, so "present at an earlier step" is the
-- operational meaning of Moser-Tardos's "q(v) is at most this step" -
-- no separate q-function needs to be built to state the global fact).
-- -------------------------------------------------------------------

theorem dom_subset_attachAt {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (a : ι) :
    T.dom ⊆ (T.attachAt P a).dom := by
  unfold GrowingTree.attachAt
  by_cases h : (T.candidates P a).Nonempty
  · rw [dite_eq_left h]
    unfold GrowingTree.attachChild
    exact Finset.subset_insert _ _
  · rw [dite_eq_right h]

theorem dom_subset_τBuild_succ {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (n : ℕ) :
    (τBuild P C t n).dom ⊆ (τBuild P C t (n + 1)).dom :=
  dom_subset_attachAt P (τBuild P C t n) (C (t - 1 - n))

/-- `dom` only grows across the construction: everything present at an
    earlier-or-equal step is still present at any later step. The
    operational stand-in for Moser-Tardos's "q(v) ≤ this step". -/
theorem dom_subset_τBuild_of_le {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t n : ℕ) :
    ∀ m, n ≤ m → (τBuild P C t n).dom ⊆ (τBuild P C t m).dom := by
  intro m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ k _ ih => exact ih.trans (dom_subset_τBuild_succ P C t k)

/-- THE GLOBAL FACT, threaded through the actual τC(t) construction (not
    just an abstract single tree `T`): a vertex `v` present at ANY step
    `m` at-or-before `n`, whose label matches-or-neighbors the label
    `C (t-1-n)` being attached at step `n+1`, is STRICTLY shallower than
    the vertex newly attached at step `n+1`. This is Moser-Tardos Lemma
    2.1(i)'s "q(u) < q(v) [i.e. v present since step m ≤ n, u attached at
    step n+1 > n] and vbl(u), vbl(v) overlap ⟹ d(u) > d(v)", stated
    operationally against the real construction. -/
theorem τBuild_attach_deeper_than_prior {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t n : ℕ)
    (h : ((τBuild P C t n).candidates P (C (t - 1 - n))).Nonempty)
    (v : List ℕ) (m : ℕ) (hmn : m ≤ n) (hv : v ∈ (τBuild P C t m).dom)
    (hlab : (τBuild P C t n).lab v = C (t - 1 - n)
              ∨ neighbor P ((τBuild P C t n).lab v) (C (t - 1 - n))) :
    v.length < (newAttachAddr P (τBuild P C t n) (C (t - 1 - n)) h).length := by
  apply attachAt_new_vertex_deeper_than_any_candidate P (τBuild P C t n) (C (t - 1 - n)) h
  rw [mem_candidates_iff]
  exact ⟨dom_subset_τBuild_of_le P C t m n hmn hv, hlab⟩

-- -------------------------------------------------------------------
-- Lemma 2.1(i)'s CONCLUSION: same-depth vertices never share a variable.
-- Proved as an invariant maintained at every step of the construction,
-- not extracted after the fact - avoids needing to name "which step
-- attached this vertex" at all.
-- -------------------------------------------------------------------

/-- Same-depth vertices of a GrowingTree never share a variable. Stated
    for an arbitrary tree so the induction below can invoke it as its
    own hypothesis at each step of the construction. -/
def SameDepthIndependent {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) : Prop :=
  ∀ u v, u ∈ T.dom → v ∈ T.dom → u.length = v.length → u ≠ v →
    T.lab u ≠ T.lab v ∧ ¬ neighbor P (T.lab u) (T.lab v)

/-- Helper for the step case: an OLD vertex `u` at the SAME depth as the
    address about to be freshly attached (with label `a`) cannot share a
    label with `a` - `u` would otherwise be a candidate, but every
    candidate is STRICTLY shallower than the new address
    (`attachAt_new_vertex_deeper_than_any_candidate`), contradicting equal
    depth. Isolated so it is proved once and reused for both orderings of
    the pair (new-then-old and old-then-new) in the main induction. -/
theorem attachAt_new_old_sameDepth_indep {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (T : GrowingTree ι) (a : ι) (h : (T.candidates P a).Nonempty)
    (u : List ℕ) (hu : u ∈ T.dom) (hlen : u.length = (newAttachAddr P T a h).length) :
    T.lab u ≠ a ∧ ¬ neighbor P (T.lab u) a := by
  constructor
  · intro heq
    have hcand : u ∈ T.candidates P a := (mem_candidates_iff P T a u).mpr ⟨hu, Or.inl heq⟩
    have := attachAt_new_vertex_deeper_than_any_candidate P T a h u hcand
    omega
  · intro hnb
    have hcand : u ∈ T.candidates P a := (mem_candidates_iff P T a u).mpr ⟨hu, Or.inr hnb⟩
    have := attachAt_new_vertex_deeper_than_any_candidate P T a h u hcand
    omega

/-- Moser-Tardos Lemma 2.1(i)'s conclusion, proved as an invariant of the
    τC(t) construction: at every step, same-depth vertices are
    label-independent. Base case: the singleton root has only one
    address, so the `u ≠ v` hypothesis is vacuous. Step case, attach
    branch: `attachAt_new_old_sameDepth_indep` handles the two mixed
    (new/old) orderings directly; both-old falls back to the induction
    hypothesis (labels there are literally unchanged by the attachment);
    both-new is excluded since there is only ever ONE new address. -/
theorem τBuild_sameDepthIndependent {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) :
    ∀ n, SameDepthIndependent P (τBuild P C t n)
  | 0 => by
      intro u v hu hv _ huv
      simp only [τBuild, GrowingTree.singleton, Finset.mem_singleton] at hu hv
      exact absurd (hu.trans hv.symm) huv
  | (n + 1) => by
      have ih := τBuild_sameDepthIndependent P C t n
      show SameDepthIndependent P ((τBuild P C t n).attachAt P (C (t - 1 - n)))
      by_cases h : ((τBuild P C t n).candidates P (C (t - 1 - n))).Nonempty
      · intro u v hu hv hlen huv
        rw [attachAt_dom_eq_insert P (τBuild P C t n) (C (t - 1 - n)) h, Finset.mem_insert] at hu hv
        rcases hu with hu | hu <;> rcases hv with hv | hv
        · exact absurd (hu.trans hv.symm) huv
        · -- u = new address, v old
          subst hu
          rw [attachAt_lab_new_addr,
              attachAt_lab_old P _ _ h v (fun he => newAttachAddr_not_mem P _ _ h (he ▸ hv))]
          have := attachAt_new_old_sameDepth_indep P (τBuild P C t n) (C (t - 1 - n)) h v hv hlen.symm
          exact ⟨fun heq => this.1 heq.symm, fun hnb => this.2 (neighbor_symm P _ _ hnb)⟩
        · -- v = new address, u old
          subst hv
          rw [attachAt_lab_new_addr,
              attachAt_lab_old P _ _ h u (fun he => newAttachAddr_not_mem P _ _ h (he ▸ hu))]
          exact attachAt_new_old_sameDepth_indep P (τBuild P C t n) (C (t - 1 - n)) h u hu hlen
        · rw [attachAt_lab_old P _ _ h u (fun he => newAttachAddr_not_mem P _ _ h (he ▸ hu)),
              attachAt_lab_old P _ _ h v (fun he => newAttachAddr_not_mem P _ _ h (he ▸ hv))]
          exact ih u v hu hv hlen huv
      · rwa [GrowingTree.attachAt, dite_eq_right h]

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @candidate_length_le_chosen
#check @newAttachAddr
#check @newAttachAddr_mem_attachAt_dom
#check @attachAt_lab_new_addr
#check @attachAt_new_vertex_deeper_than_any_candidate
#check @mem_candidates_iff
#check @dom_subset_τBuild_of_le
#check @τBuild_attach_deeper_than_prior
#check @τBuild_sameDepthIndependent

-- Explicit checks for all remaining helper theorems.
#check @attachAt_dom_eq_insert
#check @attachAt_lab_old
#check @attachAt_new_old_sameDepth_indep
#check @dom_subset_attachAt
#check @dom_subset_τBuild_succ
#check @newAttachAddr_not_mem
