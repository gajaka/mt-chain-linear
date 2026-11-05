/-
  Adaptive consumption of independent per-variable resampling tables.

  The footprint is a deterministic function of the current finite state.
  Each selected variable consumes its next unused table entry. An initializer
  may read slot zero only (including a constant initializer). A state prefix
  determines its counters and depends only on the entries already consumed.
  No probability-law, convergence, or repair premise is a field of this model.

  This is the per-variable table construction in Moser--Tardos,
  arXiv:0903.0544v3, Section 2. The probability bridge is separate.
-/

module

public import PPGraph.Finite.Resampling.Basic
public import PPGraph.MoserTardos.Process.RandomTrajectory

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory Classical

namespace FiniteTable

noncomputable instance stateFintype {V : Type} [Fintype V] {S : VarSpaces V}
    [∀ v, Fintype (S.space v)] : Fintype (MTState S) :=
  inferInstanceAs (Fintype (∀ v, S.space v))

noncomputable instance stateDecidableEq {V : Type} [Fintype V] {S : VarSpaces V}
    [∀ v, DecidableEq (S.space v)] : DecidableEq (MTState S) :=
  inferInstanceAs (DecidableEq (∀ v, S.space v))

instance stateMeasurableSingleton {V : Type} [Fintype V] {S : VarSpaces V}
    [∀ v, MeasurableSingletonClass (S.space v)] : MeasurableSingletonClass (MTState S) :=
  inferInstanceAs (MeasurableSingletonClass (∀ v, S.space v))

variable {V : Type} [Fintype V] [DecidableEq V] {S : VarSpaces V}
  [∀ v, Fintype (S.space v)] [∀ v, DecidableEq (S.space v)]
  [∀ v, MeasurableSingletonClass (S.space v)]

def InitialLocal (init : LogSpace S → MTState S) : Prop :=
  ∀ ω₁ ω₂, (∀ v, ω₁ (0, v) = ω₂ (0, v)) → init ω₁ = init ω₂

theorem initialLocal_const (s₀ : MTState S) : InitialLocal (fun _ => s₀) := by
  intro _ _ _
  rfl

def run (F : MTState S → Finset V) (init : LogSpace S → MTState S)
    (ω : LogSpace S) : ℕ → MTState S × (V → ℕ)
  | 0 => (init ω, fun _ => 0)
  | n + 1 =>
    let prev := run F init ω n
    (FiniteResampling.coordinateUpdate (F prev.1) prev.1
      (drawFrom ω (fun v => prev.2 v + 1)),
      fun v => if v ∈ F prev.1 then prev.2 v + 1 else prev.2 v)

def trajectory (F : MTState S → Finset V) (init : LogSpace S → MTState S)
    (n : ℕ) (ω : LogSpace S) : MTState S := (run F init ω n).1

def count (F : MTState S → Finset V) (init : LogSpace S → MTState S)
    (n : ℕ) (ω : LogSpace S) (v : V) : ℕ := (run F init ω n).2 v

def nextDraw (F : MTState S → Finset V) (init : LogSpace S → MTState S)
    (n : ℕ) (ω : LogSpace S) : MTState S :=
  drawFrom ω (fun v => count F init n ω v + 1)

theorem trajectory_zero (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (ω : LogSpace S) :
    trajectory F init 0 ω = init ω := rfl

theorem trajectory_step (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (n : ℕ) (ω : LogSpace S) :
    trajectory F init (n + 1) ω =
      FiniteResampling.coordinateUpdate (F (trajectory F init n ω))
        (trajectory F init n ω) (nextDraw F init n ω) := rfl

theorem count_zero (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (ω : LogSpace S) (v : V) :
    count F init 0 ω v = 0 := rfl

theorem count_step (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (n : ℕ) (ω : LogSpace S) (v : V) :
    count F init (n + 1) ω v = count F init n ω v +
      if v ∈ F (trajectory F init n ω) then 1 else 0 := by
  change (if v ∈ F (trajectory F init n ω) then count F init n ω v + 1
    else count F init n ω v) = _
  split_ifs <;> omega

theorem count_mono_step (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (n : ℕ) (ω : LogSpace S) (v : V) :
    count F init n ω v ≤ count F init (n + 1) ω v := by
  rw [count_step]
  omega

theorem count_le_time (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (n : ℕ) (ω : LogSpace S) (v : V) :
    count F init n ω v ≤ n := by
  induction n with
  | zero => simp [count_zero]
  | succ n ih => rw [count_step]; split_ifs <;> omega

theorem measurable_run (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (hi : Measurable init) (n : ℕ) :
    Measurable (fun ω => (run F init ω n).1) ∧
      ∀ v, Measurable (fun ω => (run F init ω n).2 v) := by
  induction n with
  | zero => exact ⟨hi, fun _ => measurable_const⟩
  | succ n ih =>
    have hd : Measurable (nextDraw F init n) := by
      apply Measurable.of_eval
      intro v
      exact measurable_eval_bounded v (n + 1) (fun ω => count F init n ω v + 1)
        ((ih.2 v).add_const 1) (fun ω => by have := count_le_time F init n ω v; omega)
    have hu := (measurable_of_finite (fun p : MTState S × MTState S =>
      FiniteResampling.coordinateUpdate (F p.1) p.1 p.2)).comp (ih.1.prodMk hd)
    refine ⟨hu, ?_⟩
    intro v
    have hm : MeasurableSet {ω | v ∈ F (trajectory F init n ω)} :=
      ih.1 (Set.toFinite {s : MTState S | v ∈ F s}).measurableSet
    exact Measurable.ite hm ((ih.2 v).add_const 1) (ih.2 v)

theorem measurable_trajectory (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (hi : Measurable init) (n : ℕ) :
    Measurable (trajectory F init n) := (measurable_run F init hi n).1

theorem measurable_nextDraw (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (hi : Measurable init) (n : ℕ) :
    Measurable (nextDraw F init n) := by
  apply Measurable.of_eval
  intro v
  exact measurable_eval_bounded v (n + 1) (fun ω => count F init n ω v + 1)
    (((measurable_run F init hi n).2 v).add_const 1)
    (fun ω => by have := count_le_time F init n ω v; omega)

/-- Changing unused entries cannot change any state or counter already reached. -/
theorem run_prefix_stable (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (hl : InitialLocal init) (n : ℕ)
    (ω₁ ω₂ : LogSpace S)
    (ha : ∀ v j, j ≤ count F init n ω₁ v → ω₁ (j, v) = ω₂ (j, v)) :
    ∀ k ≤ n, run F init ω₁ k = run F init ω₂ k := by
  induction n with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    exact Prod.ext (hl ω₁ ω₂ (fun v => ha v 0 (Nat.zero_le _))) rfl
  | succ n ih =>
    have hp : ∀ k ≤ n, run F init ω₁ k = run F init ω₂ k :=
      ih (fun v j hj => ha v j (hj.trans (count_mono_step F init n ω₁ v)))
    intro k hk
    by_cases hkn : k ≤ n
    · exact hp k hkn
    · have hk1 : k = n + 1 := by omega
      subst k
      have he := hp n le_rfl
      have hs : trajectory F init n ω₁ = trajectory F init n ω₂ := congrArg Prod.fst he
      have hc : ∀ v, count F init n ω₁ v = count F init n ω₂ v :=
        fun v => congrFun (congrArg Prod.snd he) v
      apply Prod.ext
      · change FiniteResampling.coordinateUpdate (F (trajectory F init n ω₁))
          (trajectory F init n ω₁) (nextDraw F init n ω₁) =
          FiniteResampling.coordinateUpdate (F (trajectory F init n ω₂))
          (trajectory F init n ω₂) (nextDraw F init n ω₂)
        funext v
        by_cases hv : v ∈ F (trajectory F init n ω₁)
        · have hj : count F init n ω₁ v + 1 ≤ count F init (n + 1) ω₁ v := by
            rw [count_step]; simp [hv]
          simp only [FiniteResampling.coordinateUpdate, ← hs, hv, ↓reduceIte]
          change ω₁ (count F init n ω₁ v + 1, v) = ω₂ (count F init n ω₂ v + 1, v)
          rw [← hc v]
          exact ha v _ hj
        · simp only [FiniteResampling.coordinateUpdate, ← hs, hv, ↓reduceIte]
      · funext v
        change (if v ∈ F (trajectory F init n ω₁) then count F init n ω₁ v + 1
          else count F init n ω₁ v) =
          (if v ∈ F (trajectory F init n ω₂) then count F init n ω₂ v + 1
          else count F init n ω₂ v)
        rw [hs, hc v]

def uses (F : MTState S → Finset V) (p : ℕ → MTState S) : ℕ → V → ℕ
  | 0, _ => 0
  | n + 1, v => uses F p n v + if v ∈ F (p n) then 1 else 0

theorem uses_congr (F : MTState S → Finset V) (p q : ℕ → MTState S) (n : ℕ)
    (ha : ∀ k < n, p k = q k) : uses F p n = uses F q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he := ih (fun k hk => ha k (by omega))
    funext v
    simp only [uses, he, ha n (by omega)]

theorem count_eq_uses (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (ω : LogSpace S) (n : ℕ) :
    count F init n ω = uses F (fun k => trajectory F init k ω) n := by
  induction n with
  | zero => rfl
  | succ n ih => funext v; rw [count_step, uses, congrFun ih v]

theorem run_eq_of_footprints_agree (F G : MTState S → Finset V)
    (init : LogSpace S → MTState S) (ω : LogSpace S) (n : ℕ)
    (ha : ∀ k < n, F (trajectory F init k ω) = G (trajectory F init k ω)) :
    run F init ω n = run G init ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := ih (fun k hk => ha k (by omega))
    have hf := ha n (by omega)
    change F (run F init ω n).1 = G (run F init ω n).1 at hf
    simp only [run, ← hp, hf]

abbrev Path (S : VarSpaces V) (n : ℕ) := Fin (n + 1) → MTState S

def statePrefix (F : MTState S → Finset V) (init : LogSpace S → MTState S)
    (n : ℕ) (ω : LogSpace S) : Path S n := fun k => trajectory F init k.val ω

def pathState {n : ℕ} (p : Path S n) (k : ℕ) : MTState S :=
  p ⟨min k n, by omega⟩

theorem pathState_at {n : ℕ} (p : Path S n) (k : ℕ) (hk : k ≤ n) :
    pathState p k = p ⟨k, by omega⟩ := by
  simp only [pathState, min_eq_left hk]

def pathCount (F : MTState S → Finset V) {n : ℕ} (p : Path S n) : V → ℕ :=
  uses F (pathState p) n

theorem count_of_prefix (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (n : ℕ) (ω : LogSpace S) (p : Path S n)
    (hp : statePrefix F init n ω = p) : count F init n ω = pathCount F p := by
  rw [count_eq_uses]
  apply uses_congr
  intro k hk
  rw [pathState_at p k (by omega)]
  exact congrFun hp ⟨k, by omega⟩

def consumedBlock (c : V → ℕ) : Finset (ℕ × V) :=
  Finset.univ.biUnion (fun v => (Finset.range (c v + 1)).image (fun j => (j, v)))

theorem mem_consumedBlock (c : V → ℕ) (j : ℕ) (v : V) :
    (j, v) ∈ consumedBlock c ↔ j ≤ c v := by
  simp [consumedBlock, Finset.mem_biUnion, Finset.mem_image]

theorem measurable_prefix (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (hi : Measurable init) (n : ℕ) :
    Measurable (statePrefix F init n) := by
  apply Measurable.of_eval
  intro k
  exact measurable_trajectory F init hi k.val

theorem prefix_event_depends_consumed (F : MTState S → Finset V)
    (init : LogSpace S → MTState S) (hl : InitialLocal init) (n : ℕ) (p : Path S n)
    (ω₁ ω₂ : LogSpace S)
    (ha : ∀ i ∈ consumedBlock (pathCount F p), ω₁ i = ω₂ i) :
    statePrefix F init n ω₁ = p ↔ statePrefix F init n ω₂ = p := by
  have go (x y : LogSpace S)
      (hag : ∀ i ∈ consumedBlock (pathCount F p), x i = y i)
      (hp : statePrefix F init n x = p) : statePrefix F init n y = p := by
    have hc := count_of_prefix F init n x p hp
    have hs := run_prefix_stable F init hl n x y (by
      intro v j hj
      apply hag (j, v)
      rw [mem_consumedBlock, ← congrFun hc v]
      exact hj)
    calc statePrefix F init n y = statePrefix F init n x := by
           funext k
           exact (congrArg Prod.fst (hs k.val (by omega))).symm
         _ = p := hp
  exact ⟨go ω₁ ω₂ ha, go ω₂ ω₁ (fun i hi => (ha i hi).symm)⟩

end FiniteTable

#check @FiniteTable.initialLocal_const
#check @FiniteTable.trajectory_zero
#check @FiniteTable.trajectory_step
#check @FiniteTable.count_zero
#check @FiniteTable.count_step
#check @FiniteTable.count_mono_step
#check @FiniteTable.count_le_time
#check @FiniteTable.measurable_run
#check @FiniteTable.measurable_trajectory
#check @FiniteTable.measurable_nextDraw
#check @FiniteTable.run_prefix_stable
#check @FiniteTable.uses_congr
#check @FiniteTable.count_eq_uses
#check @FiniteTable.run_eq_of_footprints_agree
#check @FiniteTable.pathState_at
#check @FiniteTable.count_of_prefix
#check @FiniteTable.mem_consumedBlock
#check @FiniteTable.measurable_prefix
#check @FiniteTable.prefix_event_depends_consumed
