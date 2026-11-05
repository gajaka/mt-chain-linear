/-
  PPGraphBDDMatrix.lean
  Matrix representation of the BDD dependency graph: an incidence matrix
  M : C -> V -> R (rows = certificates, columns = variables, M c v = 1 iff
  v in vars c) whose Gram matrix M * Mᵀ recovers `dependent` exactly:
  (M * Mᵀ) c1 c2 = |vars c1 ∩ vars c2|, and that is positive iff c1, c2
  are dependent (PPGraphProbabilistic.lean's `dependent`, restated as a
  Nonempty intersection). This is a restatement, not a new mathematical
  fact - the point is to make the existing CoupledIn/dependent structure
  visible to linear-algebra/spectral-graph-theory tooling (e.g. Mathlib's
  `SimpleGraph.lapMatrix` and `card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`,
  which already proves "component count = Laplacian nullspace dimension"
  for a SimpleGraph - not attempted here, this file only builds the bridge
  that a future file could use to connect BDD's `SameComponent` to that
  theorem, should the `SimpleGraph.ConnectedComponent` overhead ever be
  judged worth paying).

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.Dependency.Probabilistic
public import Mathlib.Data.Matrix.Basic

@[expose] public section

open scoped Classical Matrix

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {C V : Type} [DecidableEq C] [DecidableEq V] [Fintype V]

/-- The incidence matrix of a `CertVars` assignment: rows indexed by
    certificates, columns by variables, entry 1 iff the certificate
    depends on that variable. -/
def incidenceMatrix (vars : CertVars C V) : Matrix C V ℝ :=
  fun c v => if v ∈ vars c then 1 else 0

/-- Entrywise product of two incidence-matrix rows collapses to the
    indicator of membership in the intersection - the algebraic core of
    the bridge, isolated so the main proof is a clean rewrite. -/
theorem incidenceMatrix_entry_mul (vars : CertVars C V) (c1 c2 : C) (v : V) :
    incidenceMatrix vars c1 v * incidenceMatrix vars c2 v
      = if v ∈ vars c1 ∩ vars c2 then (1 : ℝ) else 0 := by
  unfold incidenceMatrix
  by_cases h1 : v ∈ vars c1 <;> by_cases h2 : v ∈ vars c2 <;>
    simp [h1, h2, Finset.mem_inter]

/-- The Gram entry `(M * Mᵀ) c1 c2` of the incidence matrix equals the
    number of variables shared by `c1` and `c2`. This is the "M Mᵀ"
    formula: dependency structure is literally the Gram matrix of the
    incidence matrix. -/
theorem incidence_mul_transpose_apply (vars : CertVars C V) (c1 c2 : C) :
    (incidenceMatrix vars * (incidenceMatrix vars)ᵀ) c1 c2
      = ((vars c1 ∩ vars c2).card : ℝ) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  calc ∑ v, incidenceMatrix vars c1 v * incidenceMatrix vars c2 v
      = ∑ v : V, if v ∈ vars c1 ∩ vars c2 then (1 : ℝ) else 0 :=
        Finset.sum_congr rfl (fun v _ => incidenceMatrix_entry_mul vars c1 c2 v)
    _ = ((vars c1 ∩ vars c2).card : ℝ) := by
        rw [Finset.sum_boole, Finset.filter_univ_mem]

/-- THE BRIDGE: two certificates are `dependent` (share a variable) iff
    the corresponding entry of the incidence matrix's Gram matrix M Mᵀ
    is positive. Matches `CoupledIn` (`PPGraphBDD.lean`), which is
    `dependent` restricted to B - so `CoupledIn vars B c1 c2` holds iff
    `c1, c2 ∈ B` and `(M Mᵀ) c1 c2 > 0`. -/
theorem dependent_iff_incidence_pos (vars : CertVars C V) (c1 c2 : C) :
    dependent vars c1 c2 ↔ 0 < (incidenceMatrix vars * (incidenceMatrix vars)ᵀ) c1 c2 := by
  rw [incidence_mul_transpose_apply]
  unfold dependent
  exact Finset.card_pos.symm.trans Nat.cast_pos.symm

#check @dependent_iff_incidence_pos

-- Explicit checks for all remaining helper theorems.
#check @incidenceMatrix_entry_mul
#check @incidence_mul_transpose_apply
