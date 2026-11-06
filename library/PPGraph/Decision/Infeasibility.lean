/-
  Semantic infeasibility, relative to explicitly admissible states.
  Sources: Liffiton--Sakallah, JAR 40 (2008), Sections 1--2;
  Cimatti--Griggio--Sebastiani, arXiv:1401.3878, Sections 2--3.
  An unsuccessful sufficient test is never used as a refutation.
-/
module

public import PPGraph.Core.Repair

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RepairFeasibility

variable {State C : Type} [DecidableEq C]

def Satisfiable (allowed : State → Prop) (sat : C → State → Prop)
    (B : Finset C) : Prop :=
  ∃ z, allowed z ∧ ∀ c ∈ B, sat c z

def Infeasible (allowed : State → Prop) (sat : C → State → Prop)
    (B : Finset C) : Prop := ¬ Satisfiable allowed sat B

/-- Every admissible state violates some obligation; the obligation may vary. -/
def Unavoidable (allowed : State → Prop) (sat : C → State → Prop)
    (B : Finset C) : Prop := ∀ z, allowed z → ∃ c ∈ B, ¬ sat c z

theorem satisfiable_mono_obligations (allowed : State → Prop)
    (sat : C → State → Prop) {A B : Finset C} (hAB : A ⊆ B)
    (h : Satisfiable allowed sat B) : Satisfiable allowed sat A := by
  obtain ⟨z, hz, hs⟩ := h
  exact ⟨z, hz, fun c hc => hs c (hAB hc)⟩

theorem infeasible_mono_obligations (allowed : State → Prop)
    (sat : C → State → Prop) {A B : Finset C} (hAB : A ⊆ B)
    (h : Infeasible allowed sat A) : Infeasible allowed sat B :=
  fun hb => h (satisfiable_mono_obligations allowed sat hAB hb)

theorem satisfiable_mono_allowed (a b : State → Prop)
    (sat : C → State → Prop) (B : Finset C) (hab : ∀ z, a z → b z)
    (h : Satisfiable a sat B) : Satisfiable b sat B := by
  obtain ⟨z, hz, hs⟩ := h
  exact ⟨z, hab z hz, hs⟩

theorem infeasible_of_allowed_subset (a b : State → Prop)
    (sat : C → State → Prop) (B : Finset C) (hab : ∀ z, a z → b z)
    (h : Infeasible b sat B) : Infeasible a sat B :=
  fun ha => h (satisfiable_mono_allowed a b sat B hab ha)

theorem infeasible_iff_unavoidable (allowed : State → Prop)
    (sat : C → State → Prop) (B : Finset C) :
    Infeasible allowed sat B ↔ Unavoidable allowed sat B := by
  classical
  constructor
  · intro h z hz
    by_contra hn
    apply h
    refine ⟨z, hz, ?_⟩
    intro c hc
    by_contra hs
    exact hn ⟨c, hc, hs⟩
  · intro h ⟨z, hz, hs⟩
    obtain ⟨c, hc, hn⟩ := h z hz
    exact hn (hs c hc)

theorem infeasible_iff_bad_cover (allowed : State → Prop)
    (sat : C → State → Prop) (B : Finset C) :
    Infeasible allowed sat B ↔
      {z | allowed z} ⊆ ⋃ c ∈ (B : Set C), {z | ¬ sat c z} := by
  rw [infeasible_iff_unavoidable]
  simp only [Unavoidable, Set.subset_def, Set.mem_ofPred_eq, Set.mem_iUnion,
    Finset.mem_coe, exists_prop]

theorem satisfiable_empty_iff (allowed : State → Prop) (sat : C → State → Prop) :
    Satisfiable allowed sat ∅ ↔ ∃ z, allowed z := by
  simp [Satisfiable]

theorem infeasible_nonempty (allowed : State → Prop) (sat : C → State → Prop)
    (B : Finset C) (ha : ∃ z, allowed z) (h : Infeasible allowed sat B) :
    B.Nonempty := by
  by_contra hn
  have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  exact h (he ▸ (satisfiable_empty_iff allowed sat).mpr ha)

theorem satisfiable_not_infeasible (allowed : State → Prop)
    (sat : C → State → Prop) (B : Finset C) (h : Satisfiable allowed sat B) :
    ¬ Infeasible allowed sat B := fun hn => hn h

/-- Absence of a reachable good target, even if good states exist elsewhere. -/
def NoReachableGood (G : RepairGraph State) (v : State) : Prop :=
  ¬ ∃ w, G.reach_rel v w ∧ G.invariant_holds w

theorem noReachableGood_iff (G : RepairGraph State) (v : State) :
    NoReachableGood G v ↔ ∀ w, G.reach_rel v w → ¬ G.invariant_holds w := by
  simp [NoReachableGood]

theorem reachable_good_iff_repair_possible (G : RepairGraph State)
    (v : State) (hiso : isolated G v) :
    (∃ w, G.reach_rel v w ∧ G.invariant_holds w) ↔ repair_possible G v := by
  constructor
  · rintro ⟨w, hr, hg⟩
    refine ⟨hiso, w, ?_, hr, hg⟩
    intro he
    exact hiso (he ▸ hg)
  · rintro ⟨_, w, _, hr, hg⟩
    exact ⟨w, hr, hg⟩

theorem noReachableGood_iff_no_repair (G : RepairGraph State)
    (v : State) (hiso : isolated G v) :
    NoReachableGood G v ↔ ¬ repair_possible G v := by
  exact not_congr (reachable_good_iff_repair_possible G v hiso)

theorem infeasible_reachable_iff (G : RepairGraph State)
    (sat : C → State → Prop) (B : Finset C)
    (hinv : ∀ w, G.invariant_holds w ↔ ∀ c ∈ B, sat c w) (v : State) :
    Infeasible (G.reach_rel v) sat B ↔ NoReachableGood G v := by
  simp only [Infeasible, Satisfiable, NoReachableGood, hinv]

theorem global_infeasible_implies_noReachableGood (G : RepairGraph State)
    (sat : C → State → Prop) (B : Finset C)
    (hinv : ∀ w, G.invariant_holds w ↔ ∀ c ∈ B, sat c w)
    (h : Infeasible (fun _ => True) sat B) (v : State) : NoReachableGood G v := by
  apply (infeasible_reachable_iff G sat B hinv v).mp
  exact infeasible_of_allowed_subset _ _ sat B (fun _ _ => trivial) h

end RepairFeasibility

#check @RepairFeasibility.satisfiable_mono_obligations
#check @RepairFeasibility.infeasible_mono_obligations
#check @RepairFeasibility.satisfiable_mono_allowed
#check @RepairFeasibility.infeasible_of_allowed_subset
#check @RepairFeasibility.infeasible_iff_unavoidable
#check @RepairFeasibility.infeasible_iff_bad_cover
#check @RepairFeasibility.satisfiable_empty_iff
#check @RepairFeasibility.infeasible_nonempty
#check @RepairFeasibility.satisfiable_not_infeasible
#check @RepairFeasibility.noReachableGood_iff
#check @RepairFeasibility.reachable_good_iff_repair_possible
#check @RepairFeasibility.noReachableGood_iff_no_repair
#check @RepairFeasibility.infeasible_reachable_iff
#check @RepairFeasibility.global_infeasible_implies_noReachableGood
