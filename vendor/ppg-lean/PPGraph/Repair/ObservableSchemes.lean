/-
  Affine schemes of deterministic repair observables.

  A = (S -> R) and a stable observable subalgebra B give genuine mathlib
  schemes Spec A and Spec B, including their structure sheaves. The inclusion
  B -> A induces a projection Spec A -> Spec B. Restricted repair pullbacks
  induce endomorphisms making this projection commute with repair.

  Concrete states supply R-valued points. We do not identify all spectrum
  points with states, assume finite generation, or introduce a metric.
  Basic opens describe nonvanishing; inequality predicates require a separate
  Boolean indicator. Stochastic expectation is not an algebra homomorphism.
-/
module

public import PPGraph.Repair.ObservableAlgebra
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Properties

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace RepairObservableScheme

universe u
variable {R S T : Type u} [CommRing R]

def Restricts (q : S → S) (B : Subalgebra R (S → R)) : Prop :=
  ∀ f, f ∈ B → RepairObservable.pullback q f ∈ B

def restrictedPullback (q : S → S) (B : Subalgebra R (S → R))
    (h : Restricts q B) : B →ₐ[R] B :=
  ((RepairObservable.pullback q).comp B.val).codRestrict B (fun f => h f f.property)

@[simp] theorem restrictedPullback_apply (q : S → S) (B : Subalgebra R (S → R))
    (h : Restricts q B) (f : B) (s : S) :
    (restrictedPullback q B h f : S → R) s = (f : S → R) (q s) := rfl

theorem fixed_restricts (q : S → S) (B : Subalgebra R (S → R))
    (h : RepairObservable.Fixed q B) : Restricts q B := by
  intro f hf
  rw [h f hf]
  exact hf

abbrev stateScheme (R S : Type u) [CommRing R] : Scheme := Spec (.of (S → R))

abbrev observableScheme (B : Subalgebra R (S → R)) : Scheme := Spec (.of B)

abbrev baseScheme (R : Type u) [CommRing R] : Scheme := Spec (.of R)

def stateRepair (q : S → S) : stateScheme R S ⟶ stateScheme R S :=
  Spec.map (CommRingCat.ofHom (RepairObservable.pullback q).toRingHom)

def observableRepair (q : S → S) (B : Subalgebra R (S → R)) (h : Restricts q B) :
    observableScheme B ⟶ observableScheme B :=
  Spec.map (CommRingCat.ofHom (restrictedPullback q B h).toRingHom)

def observe (B : Subalgebra R (S → R)) : stateScheme R S ⟶ observableScheme B :=
  Spec.map (CommRingCat.ofHom B.val.toRingHom)

def stateBase : stateScheme R S ⟶ baseScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (S → R)))

def observableBase (B : Subalgebra R (S → R)) : observableScheme B ⟶ baseScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap R B))

theorem stateScheme_affine : IsAffine (stateScheme R S) := inferInstance

theorem observableScheme_affine (B : Subalgebra R (S → R)) :
    IsAffine (observableScheme B) := inferInstance

theorem repair_observe_commutes (q : S → S) (B : Subalgebra R (S → R))
    (h : Restricts q B) :
    stateRepair q ≫ observe B = observe B ≫ observableRepair q B h := by
  unfold stateRepair observe observableRepair
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

theorem observe_over_base (B : Subalgebra R (S → R)) :
    observe B ≫ observableBase B = stateBase := by
  unfold observe observableBase stateBase
  rw [← Spec.map_comp]
  congr 1

theorem stateRepair_over_base (q : S → S) :
    stateRepair (R := R) q ≫ stateBase = stateBase := by
  unfold stateRepair stateBase
  rw [← Spec.map_comp]
  congr 1

theorem observableRepair_over_base (q : S → S) (B : Subalgebra R (S → R))
    (h : Restricts q B) : observableRepair q B h ≫ observableBase B = observableBase B := by
  unfold observableRepair observableBase
  rw [← Spec.map_comp]
  congr 1

theorem stateRepair_id : stateRepair (R := R) (id : S → S) = 𝟙 (stateScheme R S) := by
  unfold stateRepair stateScheme
  apply Spec.map_eq_id.mpr
  rfl

theorem stateRepair_comp (q r : S → S) :
    stateRepair (R := R) (r ∘ q) = stateRepair q ≫ stateRepair r := by
  unfold stateRepair
  rw [← Spec.map_comp]
  congr 1

theorem restricts_comp (q r : S → S) (B : Subalgebra R (S → R))
    (hq : Restricts q B) (hr : Restricts r B) : Restricts (r ∘ q) B := by
  intro f hf
  exact hq _ (hr f hf)

theorem observableRepair_comp (q r : S → S) (B : Subalgebra R (S → R))
    (hq : Restricts q B) (hr : Restricts r B) :
    observableRepair (r ∘ q) B (restricts_comp q r B hq hr) =
      observableRepair q B hq ≫ observableRepair r B hr := by
  unfold observableRepair
  rw [← Spec.map_comp]
  congr 1

theorem observableRepair_eq_id_iff (q : S → S) (B : Subalgebra R (S → R))
    (h : Restricts q B) :
    observableRepair q B h = 𝟙 (observableScheme B) ↔ RepairObservable.Fixed q B := by
  rw [observableRepair, Spec.map_eq_id]
  constructor
  · intro he f hf
    have hh := congrArg (fun k : CommRingCat.of B ⟶ CommRingCat.of B => k.hom ⟨f,hf⟩) he
    exact congrArg Subtype.val hh
  · intro hf
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro f
    exact Subtype.ext (hf f f.property)

def evaluate (B : Subalgebra R (S → R)) (s : S) : B →ₐ[R] R :=
  (Pi.evalAlgHom R (fun _ : S => R) s).comp B.val

def statePoint (s : S) : baseScheme R ⟶ stateScheme R S :=
  Spec.map (CommRingCat.ofHom (Pi.evalAlgHom R (fun _ : S => R) s).toRingHom)

def observablePoint (B : Subalgebra R (S → R)) (s : S) :
    baseScheme R ⟶ observableScheme B := Spec.map (CommRingCat.ofHom (evaluate B s).toRingHom)

theorem statePoint_observe (B : Subalgebra R (S → R)) (s : S) :
    statePoint s ≫ observe B = observablePoint B s := by
  unfold statePoint observe observablePoint evaluate
  rw [← Spec.map_comp]
  rfl

theorem statePoint_after (q : S → S) (s : S) :
    statePoint (R := R) s ≫ stateRepair q = statePoint (q s) := by
  unfold statePoint stateRepair
  rw [← Spec.map_comp]
  rfl

theorem observablePoint_after (q : S → S) (B : Subalgebra R (S → R))
    (h : Restricts q B) (s : S) :
    observablePoint B s ≫ observableRepair q B h = observablePoint B (q s) := by
  unfold observablePoint observableRepair evaluate
  rw [← Spec.map_comp]
  rfl

theorem observablePoint_eq_iff (B : Subalgebra R (S → R)) (s t : S) :
    observablePoint B s = observablePoint B t ↔ RepairObservable.ObsEq B s t := by
  rw [observablePoint, observablePoint, Spec.map_inj]
  constructor
  · intro h f hf
    exact congrArg (fun k : CommRingCat.of B ⟶ CommRingCat.of R => k.hom ⟨f,hf⟩) h
  · intro h
    ext f
    exact h f f.property

theorem protected_projection (q : S → S) (B : Subalgebra R (S → R))
    (h : RepairObservable.Fixed q B) : stateRepair q ≫ observe B = observe B := by
  rw [repair_observe_commutes q B (fixed_restricts q B h),
      (observableRepair_eq_id_iff q B (fixed_restricts q B h)).mpr h, Category.comp_id]

theorem stateRepair_commute (q r : S → S) (h : ∀ s, q (r s) = r (q s)) :
    stateRepair (R := R) q ≫ stateRepair r = stateRepair r ≫ stateRepair q := by
  rw [← stateRepair_comp, ← stateRepair_comp]
  congr 1
  funext s
  exact (h s).symm

theorem observableRepair_commute (q r : S → S) (B : Subalgebra R (S → R))
    (hq : Restricts q B) (hr : Restricts r B) (h : ∀ s, q (r s) = r (q s)) :
    observableRepair q B hq ≫ observableRepair r B hr =
      observableRepair r B hr ≫ observableRepair q B hq := by
  unfold observableRepair
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  apply Subtype.ext
  funext s
  exact congrArg (fun x => (f : S → R) x) (h s).symm

/-- Existence of an actual scheme factor forces algebraic closure. -/
theorem restricts_of_scheme_factor (q : S → S) (B : Subalgebra R (S → R))
    (m : observableScheme B ⟶ observableScheme B)
    (h : stateRepair q ≫ observe B = observe B ≫ m) : Restricts q B := by
  rw [← Spec.map_preimage m] at h
  unfold stateRepair observe at h
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have hh := Spec.map_injective h
  intro f hf
  have he := congrArg (fun k : CommRingCat.of B ⟶ CommRingCat.of (S → R) =>
    k.hom ⟨f,hf⟩) hh
  change RepairObservable.pullback q f =
    ((Spec.preimage m).hom ⟨f,hf⟩ : S → R) at he
  rw [he]
  exact ((Spec.preimage m).hom ⟨f,hf⟩).property

theorem restricts_iff_scheme_factor (q : S → S) (B : Subalgebra R (S → R)) :
    Restricts q B ↔ ∃ m : observableScheme B ⟶ observableScheme B,
      stateRepair q ≫ observe B = observe B ≫ m := by
  constructor
  · intro h
    exact ⟨observableRepair q B h, repair_observe_commutes q B h⟩
  · rintro ⟨m,h⟩
    exact restricts_of_scheme_factor q B m h

/-- Any scheme factor is the one induced by the restricted pullback. -/
theorem scheme_factor_unique (q : S → S) (B : Subalgebra R (S → R))
    (hB : Restricts q B) (m : observableScheme B ⟶ observableScheme B)
    (h : stateRepair q ≫ observe B = observe B ≫ m) :
    m = observableRepair q B hB := by
  rw [← Spec.map_preimage m] at h ⊢
  unfold stateRepair observe at h
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have hh := Spec.map_injective h
  unfold observableRepair
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  apply Subtype.ext
  exact (congrArg (fun k : CommRingCat.of B ⟶ CommRingCat.of (S → R) => k.hom f) hh).symm

theorem restricts_iff_unique_scheme_factor (q : S → S) (B : Subalgebra R (S → R)) :
    Restricts q B ↔ ∃! m : observableScheme B ⟶ observableScheme B,
      stateRepair q ≫ observe B = observe B ≫ m := by
  constructor
  · intro h
    exact ⟨observableRepair q B h, repair_observe_commutes q B h,
      fun m hm => scheme_factor_unique q B h m hm⟩
  · rintro ⟨m,hm,_⟩
    exact restricts_of_scheme_factor q B m hm

theorem pullback_injective_of_surjective (q : S → T) (h : Function.Surjective q) :
    Function.Injective (RepairObservable.pullback (R := R) q) := by
  intro f g he
  funext t
  obtain ⟨s,rfl⟩ := h t
  exact congrFun he s

def summaryAlgebraEquiv (q : S → T) (h : Function.Surjective q) :
    (T → R) ≃ₐ[R] RepairObservable.projectionAlgebra (R := R) q :=
  AlgEquiv.ofInjective (RepairObservable.pullback (R := R) q)
    (pullback_injective_of_surjective (R := R) q h)

/-- A supplied surjective summary gives a genuine isomorphism of affine schemes. -/
def summarySchemeIso (q : S → T) (h : Function.Surjective q) :
    observableScheme (RepairObservable.projectionAlgebra (R := R) q) ≅ stateScheme R T :=
  Scheme.Spec.mapIso ((summaryAlgebraEquiv (R := R) q h).toRingEquiv.toCommRingCatIso).op

theorem observableRing_reduced (B : Subalgebra R (S → R)) [IsReduced R] :
    IsReduced B := isReduced_of_injective B.val Subtype.val_injective

theorem observableScheme_reduced (B : Subalgebra R (S → R)) [_root_.IsReduced R] :
    AlgebraicGeometry.IsReduced (observableScheme B) := by
  let : _root_.IsReduced B := observableRing_reduced B
  exact inferInstance

section FieldPoints
variable {K : Type u} [Field K] (B : Subalgebra K (S → K))

def evaluationPrime (s : S) : PrimeSpectrum B :=
  ⟨RingHom.ker (evaluate B s).toRingHom, RingHom.ker_isPrime (evaluate B s).toRingHom⟩

theorem evaluationPrime_maximal (s : S) : (evaluationPrime B s).asIdeal.IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective (evaluate B s).toRingHom
  intro k
  exact ⟨algebraMap K B k, (evaluate B s).commutes k⟩

theorem evaluationPrime_basicOpen (f : B) (s : S) :
    evaluationPrime B s ∈ PrimeSpectrum.basicOpen f ↔ (f : S → K) s ≠ 0 := by
  rw [PrimeSpectrum.mem_basicOpen]
  rfl

theorem evaluationPrime_after (q : S → S) (h : Restricts q B) (s : S) :
    observableRepair q B h (evaluationPrime B s) = evaluationPrime B (q s) := by
  apply PrimeSpectrum.ext
  ext f
  change (f : S → K) (q s) = 0 ↔ (f : S → K) (q s) = 0
  rfl

theorem repair_basicOpen_preimage (q : S → S) (h : Restricts q B) (f : B) :
    observableRepair q B h ⁻¹ᵁ PrimeSpectrum.basicOpen f =
      PrimeSpectrum.basicOpen (restrictedPullback q B h f) :=
  SpecMap_preimage_basicOpen _ _

theorem repaired_point_basicOpen (q : S → S) (h : Restricts q B) (f : B) (s : S) :
    observableRepair q B h (evaluationPrime B s) ∈ PrimeSpectrum.basicOpen f ↔
      (f : S → K) (q s) ≠ 0 := by
  rw [evaluationPrime_after]
  exact evaluationPrime_basicOpen B f (q s)

end FieldPoints

section Hazards
variable {V α : Type} [DecidableEq V]

theorem hazard_free_scheme_commute (a b : RepairHazard.Action V α)
    (h : RepairHazard.canSwap a b = true) :
    stateRepair (R := ℚ) a.run ≫ stateRepair b.run = stateRepair b.run ≫ stateRepair a.run :=
  stateRepair_commute _ _ (RepairHazard.canSwap_commute a b h)

theorem hazard_free_observable_scheme_commute (a b : RepairHazard.Action V α)
    (B : Subalgebra ℚ (RepairHazard.State V α → ℚ))
    (ha : Restricts a.run B) (hb : Restricts b.run B)
    (h : RepairHazard.canSwap a b = true) :
    observableRepair a.run B ha ≫ observableRepair b.run B hb =
      observableRepair b.run B hb ≫ observableRepair a.run B ha :=
  observableRepair_commute _ _ _ _ _ (RepairHazard.canSwap_commute a b h)

end Hazards

end RepairObservableScheme

#check @RepairObservableScheme.Restricts
#check @RepairObservableScheme.restrictedPullback
#check @RepairObservableScheme.restrictedPullback_apply
#check @RepairObservableScheme.fixed_restricts
#check @RepairObservableScheme.stateScheme
#check @RepairObservableScheme.observableScheme
#check @RepairObservableScheme.baseScheme
#check @RepairObservableScheme.stateRepair
#check @RepairObservableScheme.observableRepair
#check @RepairObservableScheme.observe
#check @RepairObservableScheme.stateBase
#check @RepairObservableScheme.observableBase
#check @RepairObservableScheme.stateScheme_affine
#check @RepairObservableScheme.observableScheme_affine
#check @RepairObservableScheme.repair_observe_commutes
#check @RepairObservableScheme.observe_over_base
#check @RepairObservableScheme.stateRepair_over_base
#check @RepairObservableScheme.observableRepair_over_base
#check @RepairObservableScheme.stateRepair_id
#check @RepairObservableScheme.stateRepair_comp
#check @RepairObservableScheme.restricts_comp
#check @RepairObservableScheme.observableRepair_comp
#check @RepairObservableScheme.observableRepair_eq_id_iff
#check @RepairObservableScheme.evaluate
#check @RepairObservableScheme.statePoint
#check @RepairObservableScheme.observablePoint
#check @RepairObservableScheme.statePoint_observe
#check @RepairObservableScheme.statePoint_after
#check @RepairObservableScheme.observablePoint_after
#check @RepairObservableScheme.observablePoint_eq_iff
#check @RepairObservableScheme.protected_projection
#check @RepairObservableScheme.stateRepair_commute
#check @RepairObservableScheme.observableRepair_commute
#check @RepairObservableScheme.restricts_of_scheme_factor
#check @RepairObservableScheme.restricts_iff_scheme_factor
#check @RepairObservableScheme.scheme_factor_unique
#check @RepairObservableScheme.restricts_iff_unique_scheme_factor
#check @RepairObservableScheme.pullback_injective_of_surjective
#check @RepairObservableScheme.summaryAlgebraEquiv
#check @RepairObservableScheme.summarySchemeIso
#check @RepairObservableScheme.observableRing_reduced
#check @RepairObservableScheme.observableScheme_reduced
#check @RepairObservableScheme.evaluationPrime
#check @RepairObservableScheme.evaluationPrime_maximal
#check @RepairObservableScheme.evaluationPrime_basicOpen
#check @RepairObservableScheme.evaluationPrime_after
#check @RepairObservableScheme.repair_basicOpen_preimage
#check @RepairObservableScheme.repaired_point_basicOpen
#check @RepairObservableScheme.hazard_free_scheme_commute
#check @RepairObservableScheme.hazard_free_observable_scheme_commute
