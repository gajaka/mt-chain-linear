/-
  Concrete kernel-checked boundaries of the repair scoreboard.
  Two natural-valued coordinates suffice to exhibit a real RAW order effect,
  safe independent writes, a target repair that destroys a protected fact,
  harmless footprint overlap, and hazard-free failure to make progress.
  These are mathematical examples, not fabricated LUCES measurements.
-/
module

public import PPGraph.Repair.Hazards

@[expose] public section

set_option autoImplicit false

namespace RepairHazardExamples

open RepairHazard

abbrev Coordinate := Fin 2

abbrev Snapshot := State Coordinate ℕ

def setAt (v : Coordinate) (n : ℕ) : Action Coordinate ℕ where
  reads := ∅
  writes := {v}
  run := fun s => Function.update s v n
  frame := by
    intro s w hw
    have hne : w ≠ v := by simpa using hw
    simp [hne]
  read_local := by
    intro s t _ w hw
    have he : w = v := Finset.mem_singleton.mp hw
    subst w
    simp

def copy (src dst : Coordinate) : Action Coordinate ℕ where
  reads := {src}
  writes := {dst}
  run := fun s => Function.update s dst (s src)
  frame := by
    intro s w hw
    have hne : w ≠ dst := by simpa using hw
    simp [hne]
  read_local := by
    intro s t h w hw
    have he : w = dst := Finset.mem_singleton.mp hw
    subst w
    simpa using h src (Finset.mem_singleton_self src)

def idle : Action Coordinate ℕ where
  reads := ∅
  writes := ∅
  run := id
  frame := by intro _ _ _; rfl
  read_local := by intro _ _ _ v hv; simp at hv

def zero : Snapshot := fun _ => 0

def ones : Snapshot := fun _ => 1

def before : Snapshot := Function.update zero 1 1

/-- Repairs coordinate zero while destroying the previously true coordinate one. -/
def damaging : Action Coordinate ℕ where
  reads := ∅
  writes := Finset.univ
  run := fun _ v => if v = 0 then 1 else 0
  frame := by intro _ v hv; simp at hv
  read_local := by intro _ _ _ _ _; rfl

def vars : CertVars Coordinate Coordinate := fun c => {c}

def sat (c : Coordinate) (s : Snapshot) : Prop := s c = 1

instance (c : Coordinate) : DecidablePred (sat c) := fun _ => inferInstanceAs (Decidable (_ = _))

theorem sat_local : Local vars sat := by
  intro c s t h
  unfold sat
  rw [h c (Finset.mem_singleton_self c)]

theorem independent_writes_canSwap : canSwap (setAt 0 1) (setAt 1 2) = true := by
  decide

theorem independent_writes_commute (s : Snapshot) :
    (setAt 0 1).run ((setAt 1 2).run s) = (setAt 1 2).run ((setAt 0 1).run s) :=
  canSwap_commute _ _ independent_writes_canSwap s

theorem raw_is_detected : rawHazard (setAt 0 1) (copy 0 1) = true := by
  decide

theorem raw_changes_result :
    (copy 0 1).run ((setAt 0 1).run zero) 1 = 1 ∧
      (setAt 0 1).run ((copy 0 1).run zero) 1 = 0 := by
  decide

theorem war_is_detected : warHazard (copy 0 1) (setAt 0 1) = true := by
  decide

theorem waw_is_detected : wawHazard (setAt 0 1) (setAt 0 2) = true := by
  decide

theorem scoped_repair_is_accepted :
    affected vars {1} (setAt 0 1).writes = ∅ ∧
      checkCommit sat vars {0} {1} (setAt 0 1).writes before ((setAt 0 1).run before) = true := by
  decide

theorem scoped_repair_has_full_contract :
    FullContract sat {0} {1} before ((setAt 0 1).run before) :=
  checkCommit_sound sat vars sat_local {0} {1} (setAt 0 1) before
    scoped_repair_is_accepted.2

theorem target_only_would_accept_damage :
    checkCommit sat vars {0} ∅ damaging.writes before (damaging.run before) = true ∧
      sat 1 before ∧ ¬ sat 1 (damaging.run before) := by
  decide

theorem protected_damage_is_rejected :
    checkCommit sat vars {0} {1} damaging.writes before (damaging.run before) = false ∧
      checkedStep sat vars {0} {1} damaging before = before := by
  constructor
  · decide
  · rfl

theorem overlap_need_not_violate :
    affected vars {1} (setAt 1 1).writes = {1} ∧
      checkCommit sat vars ∅ {1} (setAt 1 1).writes ones ((setAt 1 1).run ones) = true := by
  decide

theorem no_hazards_need_not_repair :
    canSwap idle idle = true ∧
      checkCommit sat vars {0} {1} idle.writes before (idle.run before) = false := by
  decide

end RepairHazardExamples

#check @RepairHazardExamples.Coordinate
#check @RepairHazardExamples.Snapshot
#check @RepairHazardExamples.setAt
#check @RepairHazardExamples.copy
#check @RepairHazardExamples.idle
#check @RepairHazardExamples.zero
#check @RepairHazardExamples.ones
#check @RepairHazardExamples.before
#check @RepairHazardExamples.damaging
#check @RepairHazardExamples.vars
#check @RepairHazardExamples.sat
#check @RepairHazardExamples.sat_local
#check @RepairHazardExamples.independent_writes_canSwap
#check @RepairHazardExamples.independent_writes_commute
#check @RepairHazardExamples.raw_is_detected
#check @RepairHazardExamples.raw_changes_result
#check @RepairHazardExamples.war_is_detected
#check @RepairHazardExamples.waw_is_detected
#check @RepairHazardExamples.scoped_repair_is_accepted
#check @RepairHazardExamples.scoped_repair_has_full_contract
#check @RepairHazardExamples.target_only_would_accept_damage
#check @RepairHazardExamples.protected_damage_is_rejected
#check @RepairHazardExamples.overlap_need_not_violate
#check @RepairHazardExamples.no_hazards_need_not_repair
