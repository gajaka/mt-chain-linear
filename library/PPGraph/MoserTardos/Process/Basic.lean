/-
  PPGraphMoserTardos.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos)

  Layer 1: product probability space + resample operator.
  Builds on PPGraphProbabilistic.lean (CertVars, dependent, independent)
  and PPGraphLLL.lean (all_pass, BadEvents, lll_feasible).

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.CompleteLattice
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Filter
public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OuterMeasure
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.MeasureTheory.Constructions.Pi
public import PPGraph.Dependency.Probabilistic
public import PPGraph.LLL.General

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory

-- -------------------------------------------------------------------
-- Layer 1: Product state space and resampling
-- -------------------------------------------------------------------

variable {V : Type} [DecidableEq V]

/-- Per-variable probability spaces for the Moser-Tardos product model.
    Each underlying random variable v has its own domain and distribution;
    the full state is a point in the product of all of them. -/
structure VarSpaces (V : Type) where
  space : V → Type
  measSpace : ∀ v, MeasurableSpace (space v)
  measure : ∀ v, Measure (space v)
  isProb : ∀ v, IsProbabilityMeasure (measure v)

/-- The product state space Ω = Π v, space v. -/
def MTState (S : VarSpaces V) := ∀ v, S.space v

/-- Resample coordinates in F: take fresh values from ω' on F,
    keep the original ω elsewhere. This is the one operation the
    Moser-Tardos algorithm performs at every step. -/
def resample {S : VarSpaces V} (F : Finset V) (ω ω' : MTState S) : MTState S :=
  fun v => if v ∈ F then ω' v else ω v

/-- An event depends only on its footprint: changing coordinates
    OUTSIDE the footprint cannot change membership. This is exactly
    what makes "resample c's footprint" a meaningful, contained
    operation with respect to A_c. -/
def depends_only_on {S : VarSpaces V} (A : Set (MTState S)) (F : Finset V) : Prop :=
  ∀ ω ω' : MTState S, (∀ v ∈ F, ω v = ω' v) → (ω ∈ A ↔ ω' ∈ A)

/-- Resampling a footprint disjoint from A's own footprint cannot
    change whether A holds. This is the formal seed of "resampling a
    violated event doesn't disturb non-neighbors" -- the same fact
    `lll_independence` assumes probabilistically, now stated
    operationally at the level of the resample function itself. -/
theorem resample_preserves_disjoint {S : VarSpaces V} (A : Set (MTState S))
    (F Fc : Finset V) (h_dep : depends_only_on A Fc) (h_disj : Disjoint F Fc)
    (ω ω' : MTState S) :
    ω ∈ A ↔ resample F ω ω' ∈ A := by
  apply h_dep
  intro v hv
  simp only [resample]
  rw [ite_eq_right]
  intro hvF
  exact (Finset.disjoint_left.mp h_disj hvF) hv

/-- resample is idempotent-ish on the footprint: after resampling F
    using ω', the new state agrees with ω' exactly on F. -/
theorem resample_agrees_on {S : VarSpaces V} (F : Finset V) (ω ω' : MTState S) :
    ∀ v ∈ F, resample F ω ω' v = ω' v := by
  intro v hv
  simp only [resample]
  rw [ite_eq_left hv]

/-- resample leaves everything outside F exactly as ω had it. -/
theorem resample_fixes_outside {S : VarSpaces V} (F : Finset V) (ω ω' : MTState S) :
    ∀ v ∉ F, resample F ω ω' v = ω v := by
  intro v hv
  simp only [resample]
  rw [ite_eq_right hv]

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @resample
#check @depends_only_on
#check @resample_preserves_disjoint
#check @resample_agrees_on
#check @resample_fixes_outside
