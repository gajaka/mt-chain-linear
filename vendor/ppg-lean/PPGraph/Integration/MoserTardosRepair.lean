/-
  PPGraphMoserTardosRepairBridge.lean

  Moser-Tardos as an instance of the abstract PPG repair relation.

  Finite expected running time for random initialization supplies a
  good state. A separate constant-log descent argument then supplies
  an existential path to a good state from every initial state.

  The graph's edges remain a parameter; MT supplies reachability and
  the invariant "no bad event holds". Certificate interpretation,
  route-bypass edges, and preservation of a separate certified core
  require their own model-specific hypotheses.

  The later mtEdgeRepairGraph bridge makes reachability the finite directed
  closure of supplied operational edges. A primitive-step compatibility proof
  then converts the actual constant-log prefix into a path in that topology.

  The existing repair_target still uses Classical.choose. The new
  result supplies its existence premise and an MT reachability witness;
  it does not turn the chosen target into an executable solver.
-/

module

public import PPGraph.Core.Repair
public import PPGraph.MoserTardos.Bounds.ConstantLog
public import Mathlib.Logic.Relation

@[expose] public section

open MeasureTheory Classical
open scoped NNReal ENNReal

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Existential MT reachability. The log is arbitrary; this relation
    does not require its realization to have positive probability. -/
def mtReach (P : MTProcess S ι) (v w : MTState S) : Prop :=
  ∃ (ω : LogSpace S) (T : ℕ), randTraj P v ω T = w

/-- The abstract repair graph instantiated with MT reachability and
    the invariant that every bad event is absent. -/
def mtRepairGraph (P : MTProcess S ι)
    (edges : MTState S → MTState S → Prop) : RepairGraph (MTState S) where
  edges := edges
  reach_rel := mtReach P
  invariant_holds := MTGood P

theorem mtReach_refl (P : MTProcess S ι) (v : MTState S) : mtReach P v v := by
  exact ⟨constantLog v, 0, rfl⟩

/-- One good target suffices for existential reachability from every
    initial state when the variable set is finite. -/
theorem exists_mtReach_good_of_good_target [Fintype V]
    (P : MTProcess S ι) (z : MTState S) (hz : MTGood P z) (v : MTState S) :
    ∃ w : MTState S, mtReach P v w ∧ MTGood P w := by
  obtain ⟨T, _, hgood⟩ := exists_good_randTraj_constantLog P z hz v
  exact ⟨randTraj P v (constantLog z) T, ⟨constantLog z, T, rfl⟩, hgood⟩

/-- An isolated state has a distinct reachable good replacement.
    Distinctness follows from the failed and restored invariants. -/
theorem mtRepairGraph_repair_possible_of_good_target [Fintype V]
    (P : MTProcess S ι) (edges : MTState S → MTState S → Prop)
    (z : MTState S) (hz : MTGood P z) (v : MTState S)
    (hiso : isolated (mtRepairGraph P edges) v) :
    repair_possible (mtRepairGraph P edges) v := by
  obtain ⟨w, hreach, hgood⟩ := exists_mtReach_good_of_good_target P z hz v
  refine ⟨hiso, w, ?_, hreach, hgood⟩
  intro heq
  apply hiso
  change MTGood P v
  simpa only [heq] using hgood

theorem mtRepairGraph_globally_repairable_of_good_target [Fintype V]
    (P : MTProcess S ι) (edges : MTState S → MTState S → Prop)
    (z : MTState S) (hz : MTGood P z) :
    globally_repairable (mtRepairGraph P edges) := by
  intro v hiso
  exact mtRepairGraph_repair_possible_of_good_target P edges z hz v hiso

/-- The expectation result is used for random initialization only.
    The transition to arbitrary starts is the constant-log theorem. -/
theorem mtRepairGraph_globally_repairable_of_randomInitETLog_lt_top [Fintype V]
    (P : MTProcess S ι) (edges : MTState S → MTState S → Prop)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (hfinite : randomInitETLog P < ⊤) :
    globally_repairable (mtRepairGraph P edges) := by
  obtain ⟨z, hz⟩ := exists_MTGood_of_randomInitETLog_lt_top P hbad hfinite
  exact mtRepairGraph_globally_repairable_of_good_target P edges z hz

/-- The MT probability and budget hypotheses imply global abstract
    repairability for this concrete reachability/invariant pair. -/
theorem mtRepairGraph_globally_repairable [Fintype V]
    (P : MTProcess S ι) (edges : MTState S → MTState S → Prop)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (p x : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun u => S.measure u) (P.bad i) ≤ (p i : ℝ≥0∞))
    (h_dom : ∀ α, p α ≤ x α)
    (h_self : ∀ α, p α * ∏ β ∈ plusNeighbors P α, (1 + x β) ≤ x α) :
    globally_repairable (mtRepairGraph P edges) := by
  exact mtRepairGraph_globally_repairable_of_randomInitETLog_lt_top P edges hbad
    (randomInitETLog_lt_top P hbad p x hp h_dom h_self)

theorem mtRepairGraph_repair_possible [Fintype V]
    (P : MTProcess S ι) (edges : MTState S → MTState S → Prop)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (p x : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun u => S.measure u) (P.bad i) ≤ (p i : ℝ≥0∞))
    (h_dom : ∀ α, p α ≤ x α)
    (h_self : ∀ α, p α * ∏ β ∈ plusNeighbors P α, (1 + x β) ≤ x α)
    (v : MTState S) (hiso : isolated (mtRepairGraph P edges) v) :
    repair_possible (mtRepairGraph P edges) v := by
  exact mtRepairGraph_globally_repairable P edges hbad p x hp h_dom h_self v hiso

/-- The existing abstractly chosen repair target comes with a genuine
    MT log/time witness, a restored invariant, and distinctness. -/
theorem mtRepairGraph_repair_target_spec
    (P : MTProcess S ι) (edges : MTState S → MTState S → Prop)
    (v : MTState S) (h : repair_possible (mtRepairGraph P edges) v) :
    ∃ (ω : LogSpace S) (T : ℕ),
      randTraj P v ω T = repair_target (mtRepairGraph P edges) v h ∧
      MTGood P (repair_target (mtRepairGraph P edges) v h) ∧
      repair_target (mtRepairGraph P edges) v h ≠ v := by
  have hvalid := repair_target_valid (mtRepairGraph P edges) v h
  rcases hvalid with ⟨hne, hreach, hgood⟩
  rcases hreach with ⟨ω, T, hT⟩
  exact ⟨ω, T, hT, hgood, hne⟩

-- Directed operational topology is a separate bridge. Its intermediate states
-- may still violate the invariant, so this is a raw repair path, not a pp-walk.

/-- A single legal resampling chooses a currently violated event. -/
def mtResampleEdge (P : MTProcess S ι) (s t : MTState S) : Prop :=
  ∃ (i : ι) (z : MTState S), s ∈ P.bad i ∧ t = resample (P.footprint i) s z

/-- A concrete edge relation admits each such primitive resampling step.
    This is a one-step implementation obligation, not a reachability assumption. -/
def MTStepRespected (P : MTProcess S ι)
    (edges : MTState S → MTState S → Prop) : Prop :=
  ∀ (s z : MTState S) (i : ι), s ∈ P.bad i → edges s (resample (P.footprint i) s z)

/-- Here reachability is the finite directed closure of the supplied edges. -/
def mtEdgeRepairGraph (P : MTProcess S ι)
    (edges : MTState S → MTState S → Prop) : RepairGraph (MTState S) where
  edges := edges
  reach_rel := Relation.ReflTransGen edges
  invariant_holds := MTGood P

/-- The constant-log trajectory up to its first good state follows the declared
    topology. This witnesses both MT reachability and an actual finite edge path. -/
theorem exists_edgeReach_good_of_good_target [Fintype V]
    (P : MTProcess S ι) (edges : MTState S → MTState S → Prop)
    (hstep : MTStepRespected P edges)
    (z : MTState S) (hz : MTGood P z) (v : MTState S) :
    ∃ w : MTState S, mtReach P v w ∧ Relation.ReflTransGen edges v w ∧ MTGood P w := by
  classical
  obtain ⟨T, _, hT⟩ := exists_good_randTraj_constantLog P z hz v
  have hex : ∃ n : ℕ, MTGood P (randTraj P v (constantLog z) n) := ⟨T, hT⟩
  have hpath : ∀ k : ℕ, k ≤ Nat.find hex →
      Relation.ReflTransGen edges v (randTraj P v (constantLog z) k) := by
    intro k
    induction k with
    | zero =>
        intro _
        exact Relation.ReflTransGen.refl
    | succ k ih =>
        intro hk
        have hkg : k < Nat.find hex := by omega
        have hbad : randTraj P v (constantLog z) k ∈
            P.bad (pickFirstViolated P (randTraj P v (constantLog z) k)) := by
          by_contra hn
          exact Nat.find_min hex hkg
            ((pickFirstViolated_notMem_bad_iff P (randTraj P v (constantLog z) k)).mp hn)
        apply (ih (by omega)).tail
        rw [randTraj_constantLog_succ]
        exact hstep _ z _ hbad
  exact ⟨randTraj P v (constantLog z) (Nat.find hex),
    ⟨constantLog z, Nat.find hex, rfl⟩, hpath _ le_rfl, Nat.find_spec hex⟩

theorem mtEdgeRepairGraph_globally_repairable_of_good_target [Fintype V]
    (P : MTProcess S ι) (edges : MTState S → MTState S → Prop)
    (hstep : MTStepRespected P edges) (z : MTState S) (hz : MTGood P z) :
    globally_repairable (mtEdgeRepairGraph P edges) := by
  intro v hiso
  obtain ⟨w, _, hreach, hgood⟩ := exists_edgeReach_good_of_good_target P edges hstep z hz v
  refine ⟨hiso, w, ?_, hreach, hgood⟩
  intro heq
  apply hiso
  change MTGood P v
  simpa only [heq] using hgood

/-- MT budgets supply a good target; the one-step topology contract converts
    its constant-log witness into a path in the concrete edge relation. -/
theorem mtEdgeRepairGraph_globally_repairable [Fintype V]
    (P : MTProcess S ι) (edges : MTState S → MTState S → Prop)
    (hstep : MTStepRespected P edges)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (p x : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun u => S.measure u) (P.bad i) ≤ (p i : ℝ≥0∞))
    (h_dom : ∀ α, p α ≤ x α)
    (h_self : ∀ α, p α * ∏ β ∈ plusNeighbors P α, (1 + x β) ≤ x α) :
    globally_repairable (mtEdgeRepairGraph P edges) := by
  obtain ⟨z, hz⟩ := exists_MTGood_of_mt_budget P hbad p x hp h_dom h_self
  exact mtEdgeRepairGraph_globally_repairable_of_good_target P edges hstep z hz

/-- In the canonical operational graph, every edge is a violated-event
    resampling and the repair witness follows those edges. -/
theorem mtResampleRepairGraph_globally_repairable [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (p x : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun u => S.measure u) (P.bad i) ≤ (p i : ℝ≥0∞))
    (h_dom : ∀ α, p α ≤ x α)
    (h_self : ∀ α, p α * ∏ β ∈ plusNeighbors P α, (1 + x β) ≤ x α) :
    globally_repairable (mtEdgeRepairGraph P (mtResampleEdge P)) := by
  apply mtEdgeRepairGraph_globally_repairable P (mtResampleEdge P) ?_ hbad p x hp h_dom h_self
  intro s z i hi
  exact ⟨i, z, hi, rfl⟩

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @mtReach
#check @mtRepairGraph
#check @mtReach_refl
#check @exists_mtReach_good_of_good_target
#check @mtRepairGraph_repair_possible_of_good_target
#check @mtRepairGraph_globally_repairable_of_good_target
#check @mtRepairGraph_globally_repairable_of_randomInitETLog_lt_top
#check @mtRepairGraph_globally_repairable
#check @mtRepairGraph_repair_possible
#check @mtRepairGraph_repair_target_spec
#check @exists_edgeReach_good_of_good_target
#check @mtEdgeRepairGraph_globally_repairable_of_good_target
#check @mtEdgeRepairGraph_globally_repairable
#check @mtResampleRepairGraph_globally_repairable
