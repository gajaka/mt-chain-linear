/-
  Observable algebras for deterministic repair.

  Pullback acts on functions contravariantly. Stable subalgebras retain the
  information needed for subsequent observable updates; fixed subalgebras
  retain every observable value. These are different obligations.

  The stable hull is the least stable subalgebra containing supplied
  generators. It is a mathematical construction, not an algorithm for
  finding a small hull. It can equal the full observable algebra.

  Stability makes observational equivalence compatible with repair and
  therefore gives an exact deterministic quotient. Footprint locality
  connects this algebraic result to the existing repair hazard layer.
  No gradient, probability law, successful repair or physical realization
  is assumed. Numeric margins require their own link to certificate truth.
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import PPGraph.Repair.Hazards

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RepairObservable

variable {R S T U I : Type*} [CommSemiring R]

/-- A state map induces an algebra homomorphism in the opposite direction. -/
def pullback (q : S → T) : (T → R) →ₐ[R] (S → R) where
  toFun f := f ∘ q
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]

theorem pullback_apply (q : S → T) (f : T → R) (s : S) :
    pullback q f s = f (q s) := rfl

theorem pullback_comp (q : S → T) (r : T → U) :
    pullback (R := R) (r ∘ q) = (pullback q).comp (pullback r) := rfl

def Stable (ops : I → S → S) (B : Subalgebra R (S → R)) : Prop :=
  ∀ i f, f ∈ B → pullback (ops i) f ∈ B

def Fixed (run : S → S) (B : Subalgebra R (S → R)) : Prop :=
  ∀ f, f ∈ B → pullback run f = f

def fixedAlgebra (run : S → S) : Subalgebra R (S → R) :=
  AlgHom.equalizer (pullback run) (AlgHom.id R (S → R))

@[simp]

theorem mem_fixedAlgebra (run : S → S) (f : S → R) :
    f ∈ fixedAlgebra run ↔ pullback run f = f := Iff.rfl

theorem fixed_adjoin_iff (run : S → S) (G : Set (S → R)) :
    Fixed run (Algebra.adjoin R G) ↔ ∀ f ∈ G, pullback run f = f := by
  constructor
  · intro h f hf
    exact h f (Algebra.subset_adjoin hf)
  · intro h
    have hle : Algebra.adjoin R G ≤ fixedAlgebra run :=
      Algebra.adjoin_le_iff.mpr h
    exact fun f hf => (mem_fixedAlgebra run f).mp (hle hf)

/-- To establish stability, it suffices to check the algebra generators. -/
theorem stable_adjoin_iff (ops : I → S → S) (G : Set (S → R)) :
    Stable ops (Algebra.adjoin R G) ↔
      ∀ i f, f ∈ G → pullback (ops i) f ∈ Algebra.adjoin R G := by
  constructor
  · intro h i f hf
    exact h i f (Algebra.subset_adjoin hf)
  · intro h i f hf
    have hle : Algebra.adjoin R G ≤
        (Algebra.adjoin R G).comap (pullback (ops i)) :=
      Algebra.adjoin_le_iff.mpr (h i)
    exact hle hf

def stableHull (ops : I → S → S) (G : Set (S → R)) :
    Subalgebra R (S → R) :=
  sInf {B | G ⊆ B ∧ Stable ops B}

theorem subset_stableHull (ops : I → S → S) (G : Set (S → R)) :
    G ⊆ stableHull ops G := by
  intro f hf
  exact Algebra.mem_sInf.mpr (fun B hB => hB.1 hf)

theorem stable_stableHull (ops : I → S → S) (G : Set (S → R)) :
    Stable ops (stableHull ops G) := by
  intro i f hf
  apply Algebra.mem_sInf.mpr
  intro B hB
  exact hB.2 i f (Algebra.mem_sInf.mp hf B hB)

theorem stableHull_le (ops : I → S → S) (G : Set (S → R))
    (B : Subalgebra R (S → R)) (hG : G ⊆ B) (hB : Stable ops B) :
    stableHull ops G ≤ B := sInf_le ⟨hG, hB⟩

theorem stableHull_mono (ops : I → S → S) {G H : Set (S → R)} (h : G ⊆ H) :
    stableHull ops G ≤ stableHull ops H :=
  stableHull_le ops G _ (fun _ hf => subset_stableHull ops H (h hf))
    (stable_stableHull ops H)

theorem stableHull_idempotent (ops : I → S → S) (G : Set (S → R)) :
    stableHull ops (stableHull ops G : Set (S → R)) = stableHull ops G := by
  apply le_antisymm
  · exact stableHull_le ops _ _ (fun _ h => h) (stable_stableHull ops G)
  · exact subset_stableHull ops _

def ObsEq (B : Subalgebra R (S → R)) (s t : S) : Prop :=
  ∀ f ∈ B, f s = f t

def observableSetoid (B : Subalgebra R (S → R)) : Setoid S where
  r := ObsEq B
  iseqv := ⟨fun _ _ _ => rfl,
    fun h f hf => (h f hf).symm,
    fun h₁ h₂ f hf => (h₁ f hf).trans (h₂ f hf)⟩

theorem obsEq_adjoin_iff (G : Set (S → R)) (s t : S) :
    ObsEq (Algebra.adjoin R G) s t ↔ ∀ f ∈ G, f s = f t := by
  constructor
  · exact fun h f hf => h f (Algebra.subset_adjoin hf)
  · intro h
    have hle : Algebra.adjoin R G ≤ AlgHom.equalizer
        (Pi.evalAlgHom R (fun _ : S => R) s)
        (Pi.evalAlgHom R (fun _ : S => R) t) := Algebra.adjoin_le_iff.mpr h
    exact fun f hf => hle hf

/-- Stability prevents a repair from revealing information omitted by B. -/
theorem obsEq_after (ops : I → S → S) (B : Subalgebra R (S → R))
    (hB : Stable ops B) (i : I) {s t : S} (h : ObsEq B s t) :
    ObsEq B (ops i s) (ops i t) := by
  intro f hf
  exact h (pullback (ops i) f) (hB i f hf)

def quotientStep (ops : I → S → S) (B : Subalgebra R (S → R))
    (hB : Stable ops B) (i : I) :
    Quotient (observableSetoid B) → Quotient (observableSetoid B) :=
  Quotient.map (ops i) (fun _ _ h => obsEq_after ops B hB i h)

theorem quotientStep_mk (ops : I → S → S) (B : Subalgebra R (S → R))
    (hB : Stable ops B) (i : I) (s : S) :
    quotientStep ops B hB i (Quotient.mk _ s) = Quotient.mk _ (ops i s) := rfl

def quotientObservable (B : Subalgebra R (S → R)) (f : S → R) (hf : f ∈ B) :
    Quotient (observableSetoid B) → R :=
  Quotient.lift f (fun _ _ h => h f hf)

theorem quotientObservable_mk (B : Subalgebra R (S → R))
    (f : S → R) (hf : f ∈ B) (s : S) :
    quotientObservable B f hf (Quotient.mk _ s) = f s := rfl

theorem observable_test_congr (B : Subalgebra R (S → R))
    (f : S → R) (hf : f ∈ B) (test : R → Prop) {s t : S} (h : ObsEq B s t) :
    test (f s) ↔ test (f t) := by rw [h f hf]

def runWord (ops : I → S → S) : List I → S → S
  | [], s => s
  | i :: rest, s => runWord ops rest (ops i s)

theorem stable_runWord (ops : I → S → S) (B : Subalgebra R (S → R))
    (hB : Stable ops B) (word : List I) (f : S → R) (hf : f ∈ B) :
    pullback (runWord ops word) f ∈ B := by
  induction word with
  | nil => exact hf
  | cons i rest ih => exact hB i _ ih

theorem obsEq_runWord (ops : I → S → S) (B : Subalgebra R (S → R))
    (hB : Stable ops B) (word : List I) {s t : S} (h : ObsEq B s t) :
    ObsEq B (runWord ops word s) (runWord ops word t) := by
  intro f hf
  exact h _ (stable_runWord ops B hB word f hf)

/-- Pullbacks of the original observables along all finite repair words. -/
def orbitGenerators (ops : I → S → S) (G : Set (S → R)) : Set (S → R) :=
  {f | ∃ word g, g ∈ G ∧ pullback (runWord ops word) g = f}

theorem subset_orbitGenerators (ops : I → S → S) (G : Set (S → R)) :
    G ⊆ orbitGenerators ops G := fun f hf => ⟨[], f, hf, rfl⟩

theorem orbit_adjoin_stable (ops : I → S → S) (G : Set (S → R)) :
    Stable ops (Algebra.adjoin R (orbitGenerators ops G)) := by
  apply (stable_adjoin_iff ops _).mpr
  rintro i f ⟨word, g, hg, rfl⟩
  exact Algebra.subset_adjoin ⟨i :: word, g, hg, rfl⟩

theorem stableHull_eq_adjoin_orbit (ops : I → S → S) (G : Set (S → R)) :
    stableHull ops G = Algebra.adjoin R (orbitGenerators ops G) := by
  apply le_antisymm
  · exact stableHull_le ops G _
      (fun _ hf => Algebra.subset_adjoin (subset_orbitGenerators ops G hf))
      (orbit_adjoin_stable ops G)
  · apply Algebra.adjoin_le_iff.mpr
    rintro f ⟨word, g, hg, rfl⟩
    exact stable_runWord ops _ (stable_stableHull ops G) word g
      (subset_stableHull ops G hg)

/-- The hull retains exactly the distinctions visible after finite repair words. -/
theorem obsEq_stableHull_iff_future (ops : I → S → S) (G : Set (S → R)) (s t : S) :
    ObsEq (stableHull ops G) s t ↔
      ∀ word f, f ∈ G → f (runWord ops word s) = f (runWord ops word t) := by
  rw [stableHull_eq_adjoin_orbit, obsEq_adjoin_iff]
  constructor
  · intro h word f hf
    exact h _ ⟨word, f, hf, rfl⟩
  · rintro h f ⟨word, g, hg, rfl⟩
    exact h word g hg

/-- All functions of a supplied summary; this is not merely its polynomial algebra. -/
def projectionAlgebra (q : S → T) : Subalgebra R (S → R) :=
  (pullback (R := R) q).range

theorem mem_projectionAlgebra (q : S → T) (f : S → R) :
    f ∈ projectionAlgebra q ↔ ∃ g : T → R, pullback q g = f := Iff.rfl

theorem obsEq_of_projection_eq (q : S → T) {s t : S} (h : q s = q t) :
    ObsEq (projectionAlgebra (R := R) q) s t := by
  rintro f ⟨g, rfl⟩
  exact congrArg g h

theorem obsEq_projectionAlgebra_iff [Nontrivial R] (q : S → T) (s t : S) :
    ObsEq (projectionAlgebra (R := R) q) s t ↔ q s = q t := by
  classical
  constructor
  · intro h
    by_contra hne
    let g : T → R := fun a => if a = q s then 1 else 0
    have hv := h (pullback q g) ⟨g, rfl⟩
    simp [g, Ne.symm hne] at hv
  · exact obsEq_of_projection_eq q

theorem projection_stable_of_factor (ops : I → S → S) (q : S → T)
    (reduced : I → T → T) (h : ∀ i s, q (ops i s) = reduced i (q s)) :
    Stable ops (projectionAlgebra (R := R) q) := by
  rintro i f ⟨g, rfl⟩
  refine ⟨pullback (reduced i) g, ?_⟩
  funext s
  exact congrArg g (h i s).symm

section Footprints

variable {V α : Type} [DecidableEq V]

def Reads (vars : Finset V) (f : RepairHazard.State V α → R) : Prop :=
  ∀ s t, (∀ v ∈ vars, s v = t v) → f s = f t

def localAlgebra (vars : Finset V) :
    Subalgebra R (RepairHazard.State V α → R) where
  carrier := {f | Reads vars f}
  zero_mem' := fun _ _ _ => rfl
  one_mem' := fun _ _ _ => rfl
  add_mem' hf hg := fun s t h => congrArg₂ (· + ·) (hf s t h) (hg s t h)
  mul_mem' hf hg := fun s t h => congrArg₂ (· * ·) (hf s t h) (hg s t h)
  algebraMap_mem' _ := fun _ _ _ => rfl

theorem reads_mono {vars more : Finset V} (h : vars ⊆ more)
    {f : RepairHazard.State V α → R} (hf : Reads vars f) : Reads more f :=
  fun s t he => hf s t (fun v hv => he v (h hv))

theorem pullback_fixed_of_disjoint (a : RepairHazard.Action V α)
    (vars : Finset V) (f : RepairHazard.State V α → R) (hf : Reads vars f)
    (hd : Disjoint a.writes vars) : pullback a.run f = f := by
  funext s
  apply hf
  intro v hv
  exact a.frame s v (fun hw => Finset.disjoint_left.mp hd hw hv)

theorem disjoint_fixes_localAlgebra (a : RepairHazard.Action V α)
    (vars : Finset V) (hd : Disjoint a.writes vars) :
    Fixed a.run (localAlgebra (R := R) vars) :=
  fun f hf => pullback_fixed_of_disjoint a vars f hf hd

/-- A sound backward dependency envelope, not a semantic minimality claim. -/
def readEnvelope (a : RepairHazard.Action V α) (vars : Finset V) : Finset V :=
  (vars \ a.writes) ∪ a.reads

theorem pullback_reads (a : RepairHazard.Action V α) (vars : Finset V)
    (f : RepairHazard.State V α → R) (hf : Reads vars f) :
    Reads (readEnvelope a vars) (pullback a.run f) := by
  intro s t h
  apply hf
  intro v hv
  by_cases hw : v ∈ a.writes
  · apply a.read_local s t _ v hw
    intro u hu
    exact h u (Finset.mem_union_right _ hu)
  · rw [a.frame s v hw, a.frame t v hw]
    exact h v (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv, hw⟩))

theorem reads_subset_stable_localAlgebra (ops : I → RepairHazard.Action V α)
    (vars : Finset V) (hscope : ∀ i, Disjoint (ops i).writes vars ∨
      (ops i).reads ⊆ vars) :
    Stable (fun i => (ops i).run) (localAlgebra (R := R) vars) := by
  intro i f hf
  rcases hscope i with hd | hr
  · rw [pullback_fixed_of_disjoint (ops i) vars f hf hd]
    exact hf
  · apply reads_mono _ (pullback_reads (ops i) vars f hf)
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (Finset.mem_sdiff.mp hv).1
    · exact hr hv

theorem hazard_free_pullbacks_commute (a b : RepairHazard.Action V α)
    (h : RepairHazard.canSwap a b = true) (f : RepairHazard.State V α → R) :
    pullback a.run (pullback b.run f) = pullback b.run (pullback a.run f) := by
  funext s
  exact congrArg f (RepairHazard.canSwap_commute a b h s).symm

end Footprints
end RepairObservable

#check @RepairObservable.pullback
#check @RepairObservable.pullback_apply
#check @RepairObservable.pullback_comp
#check @RepairObservable.Stable
#check @RepairObservable.Fixed
#check @RepairObservable.fixedAlgebra
#check @RepairObservable.mem_fixedAlgebra
#check @RepairObservable.fixed_adjoin_iff
#check @RepairObservable.stable_adjoin_iff
#check @RepairObservable.stableHull
#check @RepairObservable.subset_stableHull
#check @RepairObservable.stable_stableHull
#check @RepairObservable.stableHull_le
#check @RepairObservable.stableHull_mono
#check @RepairObservable.stableHull_idempotent
#check @RepairObservable.ObsEq
#check @RepairObservable.observableSetoid
#check @RepairObservable.obsEq_adjoin_iff
#check @RepairObservable.obsEq_after
#check @RepairObservable.quotientStep
#check @RepairObservable.quotientStep_mk
#check @RepairObservable.quotientObservable
#check @RepairObservable.quotientObservable_mk
#check @RepairObservable.observable_test_congr
#check @RepairObservable.runWord
#check @RepairObservable.stable_runWord
#check @RepairObservable.obsEq_runWord
#check @RepairObservable.orbitGenerators
#check @RepairObservable.subset_orbitGenerators
#check @RepairObservable.orbit_adjoin_stable
#check @RepairObservable.stableHull_eq_adjoin_orbit
#check @RepairObservable.obsEq_stableHull_iff_future
#check @RepairObservable.projectionAlgebra
#check @RepairObservable.mem_projectionAlgebra
#check @RepairObservable.obsEq_of_projection_eq
#check @RepairObservable.obsEq_projectionAlgebra_iff
#check @RepairObservable.projection_stable_of_factor
#check @RepairObservable.Reads
#check @RepairObservable.localAlgebra
#check @RepairObservable.reads_mono
#check @RepairObservable.pullback_fixed_of_disjoint
#check @RepairObservable.disjoint_fixes_localAlgebra
#check @RepairObservable.readEnvelope
#check @RepairObservable.pullback_reads
#check @RepairObservable.reads_subset_stable_localAlgebra
#check @RepairObservable.hazard_free_pullbacks_commute
