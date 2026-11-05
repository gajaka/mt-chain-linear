/-
  PPGraphComplementarySlackness.lean
  Complementary Slackness for Optimal Transport

  A zero weighted slack at an entry with positive mass implies that entry's
  dual constraint is tight. The other results derive entry-cost equality
  and uniqueness properties for a supplied Monge plan.

  The statements are pointwise on Fin N and Fin M. This file does not
  define aggregate primal/dual objectives or prove strong duality.
-/

module

public import Mathlib.Tactic

@[expose] public section

set_option linter.unusedVariables false

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Types and Definitions
-- ═══════════════════════════════════════════════════════════════════

variable (N M_dim : Nat)

/-- Transport plan: N × M matrix of nonneg reals -/
def Transport (N M_dim : Nat) := Fin N → Fin M_dim → Real

/-- Cost matrix -/
def CostMatrix (N M_dim : Nat) := Fin N → Fin M_dim → Real

/-- Marginals -/
def MarginalA (N : Nat) := Fin N → Real
def MarginalB (M_dim : Nat) := Fin M_dim → Real

/-- Dual variables -/
def DualU (N : Nat) := Fin N → Real
def DualV (M_dim : Nat) := Fin M_dim → Real

variable {N M_dim : Nat}

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Feasibility
-- ═══════════════════════════════════════════════════════════════════

/-- Nonneg transport -/
def nonneg (P : Transport N M_dim) : Prop :=
  ∀ i j, P i j ≥ 0

/-- Dual feasibility: u(i) + v(j) ≤ C(i,j) for all i,j -/
def dual_feasible (u : DualU N) (v : DualV M_dim) (C : CostMatrix N M_dim) : Prop :=
  ∀ i j, u i + v j ≤ C i j

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Complementary Slackness (Pointwise)
-- ═══════════════════════════════════════════════════════════════════

/-- CS condition: wherever mass flows, dual constraint is tight -/
def cs_condition (P : Transport N M_dim) (u : DualU N) (v : DualV M_dim)
    (C : CostMatrix N M_dim) : Prop :=
  ∀ i j, P i j > 0 → u i + v j = C i j

/-- Main theorem: dual feasible + zero gap at entry (i,j) implies CS at (i,j).
    This is the pointwise version that avoids sum manipulation. -/
theorem cs_pointwise (P : Transport N M_dim) (u : DualU N) (v : DualV M_dim)
    (C : CostMatrix N M_dim) (i : Fin N) (j : Fin M_dim)
    (h_df : dual_feasible u v C)
    (h_nonneg : nonneg P)
    (h_pos : P i j > 0)
    (h_tight : P i j * (C i j - (u i + v j)) = 0) :
    u i + v j = C i j := by
  have h_le : u i + v j ≤ C i j := h_df i j
  have h_diff_nonneg : C i j - (u i + v j) ≥ 0 := by linarith
  have h_prod_zero := h_tight
  -- P(i,j) > 0 and P(i,j) * slack = 0 implies slack = 0
  have h_slack_zero : C i j - (u i + v j) = 0 := by
    by_contra h_ne
    have h_slack_pos : C i j - (u i + v j) > 0 := by
      cases lt_or_eq_of_le h_diff_nonneg with
      | inl h => exact h
      | inr h => exact absurd h.symm h_ne
    have h_prod_pos : P i j * (C i j - (u i + v j)) > 0 :=
      mul_pos h_pos h_slack_pos
    linarith
  linarith

/-- If all entries satisfy the pointwise tight condition, CS holds -/
theorem cs_from_pointwise_tight (P : Transport N M_dim) (u : DualU N)
    (v : DualV M_dim) (C : CostMatrix N M_dim)
    (h_df : dual_feasible u v C)
    (h_nonneg : nonneg P)
    (h_tight : ∀ i j, P i j * (C i j - (u i + v j)) = 0) :
    cs_condition P u v C := by
  intro i j h_pos
  exact cs_pointwise P u v C i j h_df h_nonneg h_pos (h_tight i j)

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: CS implies optimality gap contribution is zero (pointwise)
-- ═══════════════════════════════════════════════════════════════════

/-- Under CS, each entry contributes zero gap: P(i,j)*C(i,j) = P(i,j)*(u(i)+v(j)) -/
theorem cs_entry_cost (P : Transport N M_dim) (u : DualU N) (v : DualV M_dim)
    (C : CostMatrix N M_dim) (i : Fin N) (j : Fin M_dim)
    (h_nonneg : nonneg P)
    (h_cs : cs_condition P u v C) :
    P i j * C i j = P i j * (u i + v j) := by
  by_cases h : P i j > 0
  · have h_eq := h_cs i j h
    rw [h_eq]
  · push Not at h
    have h_zero : P i j = 0 := le_antisymm h (h_nonneg i j)
    rw [h_zero]
    ring

-- ═══════════════════════════════════════════════════════════════════
-- Section 5: Monge Structure
-- ═══════════════════════════════════════════════════════════════════

/-- Monge map: each row has exactly one nonzero entry -/
def is_monge (P : Transport N M_dim) : Prop :=
  ∀ i : Fin N, ∃ j_star : Fin M_dim,
    P i j_star > 0 ∧ ∀ j, j ≠ j_star → P i j = 0

/-- Under CS, Monge entry is the one where dual is tight -/
theorem monge_cs_tight_entry (P : Transport N M_dim) (u : DualU N)
    (v : DualV M_dim) (C : CostMatrix N M_dim) (i : Fin N)
    (h_monge : is_monge P) (h_cs : cs_condition P u v C) :
    ∃ j_star : Fin M_dim,
      P i j_star > 0 ∧ u i + v j_star = C i j_star := by
  obtain ⟨j_star, h_pos, _⟩ := h_monge i
  exact ⟨j_star, h_pos, h_cs i j_star h_pos⟩

/-- Strict CS: zero-mass entries have strict slack -/
def cs_strict (P : Transport N M_dim) (u : DualU N) (v : DualV M_dim)
    (C : CostMatrix N M_dim) : Prop :=
  ∀ i j, P i j = 0 → u i + v j < C i j

/-- Under CS + strict CS + Monge, the selected entry is unique tight -/
theorem monge_cs_strict_unique (P : Transport N M_dim) (u : DualU N)
    (v : DualV M_dim) (C : CostMatrix N M_dim) (i : Fin N)
    (h_monge : is_monge P) (h_cs : cs_condition P u v C)
    (h_strict : cs_strict P u v C) :
    ∃ j_star : Fin M_dim,
      P i j_star > 0 ∧ u i + v j_star = C i j_star ∧
      ∀ j, j ≠ j_star → u i + v j < C i j := by
  obtain ⟨j_star, h_pos, h_others_zero⟩ := h_monge i
  refine ⟨j_star, h_pos, h_cs i j_star h_pos, ?_⟩
  intro j h_ne
  exact h_strict i j (h_others_zero j h_ne)

-- ═══════════════════════════════════════════════════════════════════
-- Section 6: Certificate Predicate
-- ═══════════════════════════════════════════════════════════════════

/-- C_CS certificate -/
def cert_cs (P : Transport N M_dim) (u : DualU N) (v : DualV M_dim)
    (C : CostMatrix N M_dim) : Prop := cs_condition P u v C

-- ═══════════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════════

#check @cs_pointwise
#check @cs_from_pointwise_tight
#check @cs_entry_cost
#check @monge_cs_tight_entry
#check @monge_cs_strict_unique
