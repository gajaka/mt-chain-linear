/-
  RISC-style repair hazard calculation and checked issue semantics.

  RAW/WAR/WAW describe possible interference between atomic repair actions.
  Action fields require proofs of the actual write frame and read locality;
  a declared footprint alone does not establish either property. Certificate
  locality is the existing PPG Local predicate, with the full core set
  supplied separately from the target and its currently failing obligations.

  The computed recheck scope is exact for the declared footprint overlaps.
  An overlap is not a claim that a certificate actually fails. Hazard-free
  actions commute; a checked commit establishes the target and preserves
  every previously true core obligation, including those outside scope.
  No stochastic law, successful repair, physical effect or eventual progress
  is a premise hidden in the hazard calculation.

  Architectural analogy: HASE DLX scoreboard model, University of Edinburgh:
  https://www.icsa.inf.ed.ac.uk/research/groups/hase/models/dlx-scb/index.html
  This module formalizes the PPG read/write abstraction, not that processor.
-/
module

public import PPGraph.Dependency.Decomposition

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RepairHazard

variable {V C α : Type} [DecidableEq V] [DecidableEq C]

abbrev State (V α : Type) := V → α

def Framed (writes : Finset V) (before after : State V α) : Prop :=
  ∀ v, v ∉ writes → after v = before v

structure Action (V α : Type) [DecidableEq V] where
  reads : Finset V
  writes : Finset V
  run : State V α → State V α
  frame : ∀ s, Framed writes s (run s)
  read_local : ∀ s t, (∀ v ∈ reads, s v = t v) →
    ∀ v ∈ writes, run s v = run t v

/-- Possible producer-to-consumer conflict for actions issued as a, then b. -/
def rawHazard (a b : Action V α) : Bool :=
  decide (a.writes ∩ b.reads).Nonempty

def warHazard (a b : Action V α) : Bool := rawHazard b a

def wawHazard (a b : Action V α) : Bool :=
  decide (a.writes ∩ b.writes).Nonempty

def canSwap (a b : Action V α) : Bool :=
  decide (Disjoint a.writes b.reads ∧ Disjoint b.writes a.reads ∧
    Disjoint a.writes b.writes)

theorem rawHazard_eq_false_iff (a b : Action V α) :
    rawHazard a b = false ↔ Disjoint a.writes b.reads := by
  simp [rawHazard, Finset.disjoint_iff_inter_eq_empty,
    Finset.nonempty_iff_ne_empty]

theorem warHazard_eq_false_iff (a b : Action V α) :
    warHazard a b = false ↔ Disjoint b.writes a.reads :=
  rawHazard_eq_false_iff b a

theorem wawHazard_eq_false_iff (a b : Action V α) :
    wawHazard a b = false ↔ Disjoint a.writes b.writes := by
  simp [wawHazard, Finset.disjoint_iff_inter_eq_empty,
    Finset.nonempty_iff_ne_empty]

theorem canSwap_eq_true_iff (a b : Action V α) :
    canSwap a b = true ↔ Disjoint a.writes b.reads ∧
      Disjoint b.writes a.reads ∧ Disjoint a.writes b.writes := by
  simp [canSwap]

theorem canSwap_iff_no_hazards (a b : Action V α) :
    canSwap a b = true ↔ rawHazard a b = false ∧
      warHazard a b = false ∧ wawHazard a b = false := by
  rw [canSwap_eq_true_iff, rawHazard_eq_false_iff,
    warHazard_eq_false_iff, wawHazard_eq_false_iff]

/-- Equivalence of atomic orders, not a hardware interleaving theorem. -/
theorem canSwap_commute (a b : Action V α) (h : canSwap a b = true)
    (s : State V α) : a.run (b.run s) = b.run (a.run s) := by
  obtain ⟨hab, hba, hww⟩ := (canSwap_eq_true_iff a b).mp h
  funext v
  by_cases hva : v ∈ a.writes
  · have hvb : v ∉ b.writes := fun hb => Finset.disjoint_left.mp hww hva hb
    rw [b.frame (a.run s) v hvb]
    apply a.read_local (b.run s) s _ v hva
    intro u hu
    exact b.frame s u (fun hw => Finset.disjoint_left.mp hba hw hu)
  · rw [a.frame (b.run s) v hva]
    by_cases hvb : v ∈ b.writes
    · symm
      apply b.read_local (a.run s) s _ v hvb
      intro u hu
      exact a.frame s u (fun hw => Finset.disjoint_left.mp hab hw hu)
    · rw [b.frame s v hvb, b.frame (a.run s) v hvb, a.frame s v hva]

/-- All core certificates potentially affected by a write footprint. -/
def affected (vars : CertVars C V) (core : Finset C) (writes : Finset V) :
    Finset C := core.filter (fun c => (writes ∩ vars c).Nonempty)

theorem mem_affected_iff (vars : CertVars C V) (core : Finset C)
    (writes : Finset V) (c : C) :
    c ∈ affected vars core writes ↔
      c ∈ core ∧ (writes ∩ vars c).Nonempty := by
  simp [affected]

theorem affected_subset (vars : CertVars C V) (core : Finset C)
    (writes : Finset V) : affected vars core writes ⊆ core :=
  Finset.filter_subset _ _

theorem affected_mono_writes (vars : CertVars C V) (core : Finset C)
    (w₁ w₂ : Finset V) (hw : w₁ ⊆ w₂) :
    affected vars core w₁ ⊆ affected vars core w₂ := by
  intro c hc
  obtain ⟨hp, v, hv⟩ := (mem_affected_iff vars core w₁ c).mp hc
  exact (mem_affected_iff vars core w₂ c).mpr
    ⟨hp, v, Finset.mem_inter.mpr ⟨hw (Finset.mem_inter.mp hv).1,
      (Finset.mem_inter.mp hv).2⟩⟩

theorem affected_union (vars : CertVars C V) (core : Finset C)
    (w₁ w₂ : Finset V) :
    affected vars core (w₁ ∪ w₂) =
      affected vars core w₁ ∪ affected vars core w₂ := by
  ext c
  simp only [mem_affected_iff, Finset.mem_union]
  constructor
  · rintro ⟨hp, v, hv⟩
    obtain ⟨hw, hc⟩ := Finset.mem_inter.mp hv
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Or.inl ⟨hp, v, Finset.mem_inter.mpr ⟨hw, hc⟩⟩
    · exact Or.inr ⟨hp, v, Finset.mem_inter.mpr ⟨hw, hc⟩⟩
  · rintro (⟨hp, v, hv⟩ | ⟨hp, v, hv⟩)
    · exact ⟨hp, v, Finset.mem_inter.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hv).1,
          (Finset.mem_inter.mp hv).2⟩⟩
    · exact ⟨hp, v, Finset.mem_inter.mpr
        ⟨Finset.mem_union_right _ (Finset.mem_inter.mp hv).1,
          (Finset.mem_inter.mp hv).2⟩⟩

theorem preserved_of_disjoint (vars : CertVars C V)
    (sat : C → State V α → Prop) (hloc : Local vars sat)
    (writes : Finset V) (before after : State V α) (hf : Framed writes before after)
    (c : C) (hd : Disjoint writes (vars c)) : sat c after ↔ sat c before := by
  apply hloc c after before
  intro v hv
  exact hf v (fun hw => Finset.disjoint_left.mp hd hw hv)

theorem preserved_outside_affected (vars : CertVars C V)
    (sat : C → State V α → Prop) (hloc : Local vars sat)
    (core : Finset C) (writes : Finset V) (before after : State V α)
    (hf : Framed writes before after) (c : C) (hc : c ∈ core)
    (ha : c ∉ affected vars core writes) : sat c after ↔ sat c before := by
  apply preserved_of_disjoint vars sat hloc writes before after hf c
  apply Finset.disjoint_left.mpr
  intro v hw hv
  exact ha ((mem_affected_iff vars core writes c).mpr
    ⟨hc, v, Finset.mem_inter.mpr ⟨hw, hv⟩⟩)

/-- The scope cannot be reduced uniformly using footprints alone. Every included
    obligation has some local Boolean interpretation that an allowed write can
    invalidate. This quantifies over interpretations, not the actual domain sat. -/
theorem affected_iff_possible_invalidation (vars : CertVars C V) (core : Finset C)
    (writes : Finset V) (c : C) :
    c ∈ affected vars core writes ↔ c ∈ core ∧
      ∃ (sat : C → State V Bool → Prop) (before after : State V Bool),
        Local vars sat ∧ Framed writes before after ∧ sat c before ∧ ¬ sat c after := by
  constructor
  · intro hc
    obtain ⟨hcore, v, hv⟩ := (mem_affected_iff vars core writes c).mp hc
    obtain ⟨hwrites, hreads⟩ := Finset.mem_inter.mp hv
    let sat : C → State V Bool → Prop := fun d s => if d = c then s v = false else True
    let before : State V Bool := fun _ => false
    let after : State V Bool := Function.update before v true
    refine ⟨hcore, sat, before, after, ?_, ?_, ?_, ?_⟩
    · intro d s t h
      by_cases hd : d = c
      · subst d
        simp only [sat, ite_eq_left rfl]
        rw [h v hreads]
      · simp [sat, hd]
    · intro w hw
      have hne : w ≠ v := by
        intro he
        subst w
        exact hw hwrites
      simp [after, hne]
    · simp [sat, before]
    · simp [sat, after]
  · rintro ⟨hc, sat, before, after, hloc, hf, hb, ha⟩
    by_contra hout
    exact ha ((preserved_outside_affected vars sat hloc core writes
      before after hf c hc hout).mpr hb)

def runPlan : List (Action V α) → State V α → State V α
  | [], s => s
  | a :: rest, s => runPlan rest (a.run s)

def planWrites : List (Action V α) → Finset V
  | [] => ∅
  | a :: rest => a.writes ∪ planWrites rest

theorem runPlan_frame (plan : List (Action V α)) (s : State V α) :
    Framed (planWrites plan) s (runPlan plan s) := by
  induction plan generalizing s with
  | nil => intro v _; rfl
  | cons a rest ih =>
    intro v hv
    have hn : v ∉ a.writes ∧ v ∉ planWrites rest := by
      simpa only [planWrites, Finset.mem_union, not_or] using hv
    exact (ih (a.run s) v hn.2).trans (a.frame s v hn.1)

theorem runPlan_swap_adjacent (a b : Action V α) (rest : List (Action V α))
    (h : canSwap a b = true) (s : State V α) :
    runPlan (a :: b :: rest) s = runPlan (b :: a :: rest) s := by
  change runPlan rest (b.run (a.run s)) = runPlan rest (a.run (b.run s))
  rw [canSwap_commute a b h s]

theorem runPlan_preserved_outside_affected (vars : CertVars C V)
    (sat : C → State V α → Prop) (hloc : Local vars sat) (core : Finset C)
    (plan : List (Action V α)) (s : State V α) (c : C) (hc : c ∈ core)
    (ha : c ∉ affected vars core (planWrites plan)) :
    sat c (runPlan plan s) ↔ sat c s :=
  preserved_outside_affected vars sat hloc core (planWrites plan)
    s (runPlan plan s) (runPlan_frame plan s) c hc ha

def FullContract (sat : C → State V α → Prop) (target core : Finset C)
    (before after : State V α) : Prop :=
  (∀ c ∈ target, sat c after) ∧ ∀ c ∈ core, sat c before → sat c after

def ScopedContract (vars : CertVars C V) (sat : C → State V α → Prop)
    (target core : Finset C) (writes : Finset V)
    (before after : State V α) : Prop :=
  (∀ c ∈ target, sat c after) ∧
    ∀ c ∈ affected vars core writes, sat c before → sat c after

theorem scopedContract_iff_fullContract (vars : CertVars C V)
    (sat : C → State V α → Prop) (hloc : Local vars sat)
    (target core : Finset C) (writes : Finset V) (before after : State V α)
    (hf : Framed writes before after) :
    ScopedContract vars sat target core writes before after ↔
      FullContract sat target core before after := by
  constructor
  · rintro ⟨ht, hp⟩
    refine ⟨ht, ?_⟩
    intro c hc hb
    by_cases ha : c ∈ affected vars core writes
    · exact hp c ha hb
    · exact (preserved_outside_affected vars sat hloc core writes
        before after hf c hc ha).mpr hb
  · rintro ⟨ht, hp⟩
    exact ⟨ht, fun c hc => hp c (affected_subset vars core writes hc)⟩

variable (sat : C → State V α → Prop) [∀ c, DecidablePred (sat c)]

/-- Only affected core obligations need rechecking; all targets are checked. -/
def checkCommit (vars : CertVars C V) (target core : Finset C)
    (writes : Finset V) (before after : State V α) : Bool :=
  decide ((∀ c ∈ target, sat c after) ∧
    ∀ c ∈ affected vars core writes, sat c before → sat c after)

theorem checkCommit_iff_scopedContract (vars : CertVars C V)
    (target core : Finset C) (writes : Finset V) (before after : State V α) :
    checkCommit sat vars target core writes before after = true ↔
      ScopedContract vars sat target core writes before after := by
  simp [checkCommit, ScopedContract]

theorem checkCommit_iff_fullContract (vars : CertVars C V) (hloc : Local vars sat)
    (target core : Finset C) (writes : Finset V) (before after : State V α)
    (hf : Framed writes before after) :
    checkCommit sat vars target core writes before after = true ↔
      FullContract sat target core before after := by
  rw [checkCommit_iff_scopedContract]
  exact scopedContract_iff_fullContract vars sat hloc target core writes before after hf

theorem checkCommit_sound (vars : CertVars C V) (hloc : Local vars sat)
    (target core : Finset C) (a : Action V α) (before : State V α)
    (h : checkCommit sat vars target core a.writes before (a.run before) = true) :
    FullContract sat target core before (a.run before) :=
  (checkCommit_iff_fullContract sat vars hloc target core a.writes
    before (a.run before) (a.frame before)).mp h

theorem checkCommit_plan_sound (vars : CertVars C V) (hloc : Local vars sat)
    (target core : Finset C) (plan : List (Action V α)) (before : State V α)
    (h : checkCommit sat vars target core (planWrites plan)
      before (runPlan plan before) = true) :
    FullContract sat target core before (runPlan plan before) :=
  (checkCommit_iff_fullContract sat vars hloc target core (planWrites plan)
    before (runPlan plan before) (runPlan_frame plan before)).mp h

/-- An atomic model-state commit. Physical actions need their own realization. -/
def checkedStep (vars : CertVars C V) (target core : Finset C)
    (a : Action V α) (before : State V α) : State V α :=
  if checkCommit sat vars target core a.writes before (a.run before) = true
  then a.run before else before

theorem checkedStep_preserves (vars : CertVars C V) (hloc : Local vars sat)
    (target core : Finset C) (a : Action V α) (before : State V α) :
    ∀ c ∈ core, sat c before →
      sat c (checkedStep sat vars target core a before) := by
  by_cases h : checkCommit sat vars target core a.writes before (a.run before) = true
  · simp only [checkedStep, ite_eq_left h]
    exact (checkCommit_sound sat vars hloc target core a before h).2
  · simp only [checkedStep, ite_eq_right h]
    exact fun _ _ hb => hb

theorem checkedStep_target_of_accepted (vars : CertVars C V) (hloc : Local vars sat)
    (target core : Finset C) (a : Action V α) (before : State V α)
    (h : checkCommit sat vars target core a.writes before (a.run before) = true) :
    ∀ c ∈ target, sat c (checkedStep sat vars target core a before) := by
  simp only [checkedStep, ite_eq_left h]
  exact (checkCommit_sound sat vars hloc target core a before h).1

end RepairHazard

#check @RepairHazard.State
#check @RepairHazard.Framed
#check @RepairHazard.Action
#check @RepairHazard.rawHazard
#check @RepairHazard.warHazard
#check @RepairHazard.wawHazard
#check @RepairHazard.canSwap
#check @RepairHazard.affected
#check @RepairHazard.runPlan
#check @RepairHazard.planWrites
#check @RepairHazard.FullContract
#check @RepairHazard.ScopedContract
#check @RepairHazard.checkCommit
#check @RepairHazard.checkedStep
#check @RepairHazard.rawHazard_eq_false_iff
#check @RepairHazard.warHazard_eq_false_iff
#check @RepairHazard.wawHazard_eq_false_iff
#check @RepairHazard.canSwap_eq_true_iff
#check @RepairHazard.canSwap_iff_no_hazards
#check @RepairHazard.canSwap_commute
#check @RepairHazard.mem_affected_iff
#check @RepairHazard.affected_subset
#check @RepairHazard.affected_mono_writes
#check @RepairHazard.affected_union
#check @RepairHazard.preserved_of_disjoint
#check @RepairHazard.preserved_outside_affected
#check @RepairHazard.affected_iff_possible_invalidation
#check @RepairHazard.runPlan_frame
#check @RepairHazard.runPlan_swap_adjacent
#check @RepairHazard.runPlan_preserved_outside_affected
#check @RepairHazard.scopedContract_iff_fullContract
#check @RepairHazard.checkCommit_iff_scopedContract
#check @RepairHazard.checkCommit_iff_fullContract
#check @RepairHazard.checkCommit_sound
#check @RepairHazard.checkCommit_plan_sound
#check @RepairHazard.checkedStep_preserves
#check @RepairHazard.checkedStep_target_of_accepted
