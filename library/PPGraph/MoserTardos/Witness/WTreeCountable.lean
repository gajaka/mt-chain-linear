/-
  PPGraphMoserTardosWTreeCountable.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), `Countable (WTree ι)`.

  Needed for E[T_LOG]'s final assembly (step 3's summability over WTree
  shapes, per PPGraphMoserTardosProbabilityGeneral.lean's roadmap) -- flagged
  in PPGraphMoserTardosToGrowingTreeCheckBridge.lean's own session notes as
  NOT auto-derivable, since WTree's constructor takes a `List (WTree ι)`
  argument (a nested recursive occurrence Lean's automatic
  Countable/Encodable deriving does not handle).

  Proof strategy (stratify by WTree.size, not a flattened S-expression
  encoding -- simpler to make rigorous without a hand-written decoder):
  for each n, the set of trees with size <= n is Countable, by induction
  on n. A tree of size <= n+1 decomposes into a label plus a list of
  children, EACH of size <= n (since a child's size is at most the sum of
  all children's sizes, which is at most n); Countable is closed under
  List and Prod, so the induction step is a `Countable.of_injective` into
  `ι × List (Bounded n)`. Every tree trivially has size <= its own size,
  so `WTree ι` embeds into the countable sigma type `Σ n, Bounded n` via
  `t ↦ ⟨t.size, t, le_refl _⟩` -- injective since the second component
  alone already recovers `t`.

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.MoserTardos.Witness.Witness
public import Mathlib.Tactic
public import Mathlib.Logic.Equiv.List

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {ι : Type} [Countable ι]

-- -------------------------------------------------------------------
-- Section 1: a child's size is bounded by the sum of all children's
-- sizes (simple list fact, stated directly on WTree.size).
-- -------------------------------------------------------------------

theorem WTree.size_le_sum_children {ι : Type} (cs : List (WTree ι)) (c : WTree ι)
    (hc : c ∈ cs) : c.size ≤ (cs.map WTree.size).sum := by
  induction cs with
  | nil => cases hc
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hc with rfl | hc'
    · omega
    · have := ih hc'
      omega

-- -------------------------------------------------------------------
-- Section 2: trees bounded by size n, and their countability by
-- induction on n.
-- -------------------------------------------------------------------

/-- Trees of size at most `n`, as a subtype. `abbrev` (not `def`) so `simp`/unification see
    straight through to the underlying `Subtype` -- a plain `def` here blocked `List.map_map`
    from matching during the injectivity proof below (confirmed via an isolated scratch repro:
    the identical simp call succeeded against a bare `{t // t.size ≤ n}` but stalled against this
    same type spelled as a `def`-wrapped abbreviation). -/
abbrev WTree.Bounded (ι : Type) (n : ℕ) : Type := {t : WTree ι // t.size ≤ n}

instance WTree.instCountableBounded (n : ℕ) : Countable (WTree.Bounded ι n) := by
  induction n with
  | zero =>
    have : IsEmpty (WTree.Bounded ι 0) :=
      ⟨fun t => absurd t.2 (Nat.not_le.mpr (WTree.size_pos t.1))⟩
    infer_instance
  | succ n ih =>
    let f : WTree.Bounded ι (n + 1) → ι × List (WTree.Bounded ι n) := fun t =>
      match t with
      | ⟨WTree.mk i cs, h⟩ =>
        (i, cs.attach.map (fun c =>
          (⟨c.1, by
            have hsum : (cs.map WTree.size).sum ≤ n := by
              have hsize : (WTree.mk i cs).size = 1 + (cs.map WTree.size).sum := by
                simp only [WTree.size]
              rw [hsize] at h
              omega
            exact le_trans (WTree.size_le_sum_children cs c.1 c.2) hsum⟩ :
            WTree.Bounded ι n)))
    have hf : Function.Injective f := by
      intro a b heq
      obtain ⟨ta, ha⟩ := a
      obtain ⟨tb, hb⟩ := b
      cases ta with
      | mk i1 cs1 =>
        cases tb with
        | mk i2 cs2 =>
          simp only [f, Prod.mk.injEq] at heq
          obtain ⟨hi, hcs⟩ := heq
          have hcs' : cs1 = cs2 := by
            have h2 := congrArg (List.map (Subtype.val (p := fun t : WTree ι => t.size ≤ n)))
              hcs
            simp [List.map_map] at h2
            exact h2
          subst hi hcs'
          rfl
    exact hf.countable

-- -------------------------------------------------------------------
-- Section 3: every tree embeds into the countable sigma type over its
-- own size -- the final instance.
-- -------------------------------------------------------------------

instance WTree.instCountable : Countable (WTree ι) := by
  have hinj : Function.Injective (fun t : WTree ι =>
      (⟨t.size, t, le_refl t.size⟩ : Σ n : ℕ, WTree.Bounded ι n)) := by
    intro a b hab
    have := congrArg (fun x : Σ n : ℕ, WTree.Bounded ι n => x.2.1) hab
    simpa using this
  exact hinj.countable

#check @WTree.instCountable

-- Explicit checks for all remaining helper theorems.
#check @WTree.size_le_sum_children
