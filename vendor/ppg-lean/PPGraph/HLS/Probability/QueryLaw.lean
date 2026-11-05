/-
  Injective queries of the independent resampling table have their
  coordinate product law. Private/shared query blocks can therefore be
  read as four independent random variables in Proposition 3.3.
-/
module

public import PPGraph.HLS.Encoding.TableCheck
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory

namespace HLS

variable {V : Type} [DecidableEq V] {S : VarSpaces V}

theorem map_tableQuery {κ : Type} [Fintype κ] (v : κ → V) (n : κ → ℕ)
    (hinj : Function.Injective (fun k => (n k, v k))) :
    (logMeasure S).map (fun ω k => atIdx ω (v k) (n k)) =
      Measure.pi (fun k => S.measure (v k)) := by
  have : ∀ a, IsProbabilityMeasure (μCoin S a) := fun a => S.isProb a.2
  calc
    _ = Measure.infinitePi (fun k => μCoin S (n k, v k)) :=
      Measure.map_infinitePi_infinitePi_of_inj (P := μCoin S)
        (f := fun k => (n k, v k)) hinj
    _ = _ := Measure.infinitePi_eq_pi _

theorem tableQuery_equidistributed {κ : Type} [Fintype κ] (v : κ → V) (n m : κ → ℕ)
    (hn : Function.Injective (fun k => (n k, v k)))
    (hm : Function.Injective (fun k => (m k, v k))) :
    (logMeasure S).map (fun ω k => atIdx ω (v k) (n k)) =
      (logMeasure S).map (fun ω k => atIdx ω (v k) (m k)) := by
  rw [map_tableQuery v n hn, map_tableQuery v m hm]

abbrev FourIndex (X Y Z : Type) := (X ⊕ Z) ⊕ (Y ⊕ Y)

def fourVariable {X Y Z : Type} (vX : X → V) (vY : Y → V) (vZ : Z → V) :
    FourIndex X Y Z → V
  | .inl (.inl x) => vX x
  | .inl (.inr z) => vZ z
  | .inr (.inl y) => vY y
  | .inr (.inr y) => vY y

def fourSlot {X Y Z : Type} (nX : X → ℕ) (nY₁ nY₂ : Y → ℕ) (nZ : Z → ℕ) :
    FourIndex X Y Z → ℕ
  | .inl (.inl x) => nX x
  | .inl (.inr z) => nZ z
  | .inr (.inl y) => nY₁ y
  | .inr (.inr y) => nY₂ y

def splitFour {X Y Z : Type} (vX : X → V) (vY : Y → V) (vZ : Z → V)
    (f : ∀ k : FourIndex X Y Z, S.space (fourVariable vX vY vZ k)) :
    ((∀ x, S.space (vX x)) × (∀ z, S.space (vZ z))) ×
      ((∀ y, S.space (vY y)) × (∀ y, S.space (vY y))) :=
  ((fun x => f (.inl (.inl x)), fun z => f (.inl (.inr z))),
    (fun y => f (.inr (.inl y)), fun y => f (.inr (.inr y))))

theorem measurePreserving_splitFour {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (vX : X → V) (vY : Y → V) (vZ : Z → V) :
    MeasurePreserving (splitFour (S := S) vX vY vZ)
      (Measure.pi (fun k => S.measure (fourVariable vX vY vZ k)))
      (((Measure.pi (fun x => S.measure (vX x))).prod
        (Measure.pi (fun z => S.measure (vZ z)))).prod
        ((Measure.pi (fun y => S.measure (vY y))).prod
          (Measure.pi (fun y => S.measure (vY y))))) := by
  have : ∀ a, IsProbabilityMeasure (S.measure a) := S.isProb
  let μ := fun k : FourIndex X Y Z => S.measure (fourVariable vX vY vZ k)
  have houter := measurePreserving_sumPiEquivProdPi μ
  have hleft := measurePreserving_sumPiEquivProdPi (fun k : X ⊕ Z => μ (.inl k))
  have hright := measurePreserving_sumPiEquivProdPi (fun k : Y ⊕ Y => μ (.inr k))
  exact (hleft.prod hright).comp houter

def readFour {X Y Z : Type} (vX : X → V) (vY : Y → V) (vZ : Z → V)
    (nX : X → ℕ) (nY₁ nY₂ : Y → ℕ) (nZ : Z → ℕ) (ω : LogSpace S) :
    ((∀ x, S.space (vX x)) × (∀ z, S.space (vZ z))) ×
      ((∀ y, S.space (vY y)) × (∀ y, S.space (vY y))) :=
  splitFour vX vY vZ (fun k => atIdx ω (fourVariable vX vY vZ k) (fourSlot nX nY₁ nY₂ nZ k))

theorem measurable_readFour {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (vX : X → V) (vY : Y → V) (vZ : Z → V)
    (nX : X → ℕ) (nY₁ nY₂ : Y → ℕ) (nZ : Z → ℕ) :
    Measurable (readFour (S := S) vX vY vZ nX nY₁ nY₂ nZ) := by
  exact (measurePreserving_splitFour (S := S) vX vY vZ).measurable.comp
    (Measurable.of_eval (fun k => measurable_pi_apply _))

theorem map_readFour {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (vX : X → V) (vY : Y → V) (vZ : Z → V)
    (nX : X → ℕ) (nY₁ nY₂ : Y → ℕ) (nZ : Z → ℕ)
    (hinj : Function.Injective (fun k : FourIndex X Y Z =>
      (fourSlot nX nY₁ nY₂ nZ k, fourVariable vX vY vZ k))) :
    (logMeasure S).map (readFour vX vY vZ nX nY₁ nY₂ nZ) =
      (((Measure.pi (fun x => S.measure (vX x))).prod
        (Measure.pi (fun z => S.measure (vZ z)))).prod
        ((Measure.pi (fun y => S.measure (vY y))).prod
          (Measure.pi (fun y => S.measure (vY y))))) := by
  have hm : Measurable (fun ω : LogSpace S => fun k : FourIndex X Y Z =>
      atIdx ω (fourVariable vX vY vZ k) (fourSlot nX nY₁ nY₂ nZ k)) := by
    apply Measurable.of_eval
    intro k
    exact measurable_pi_apply _
  have hsplit := measurePreserving_splitFour (S := S) vX vY vZ
  rw [show readFour (S := S) vX vY vZ nX nY₁ nY₂ nZ =
    splitFour vX vY vZ ∘ (fun ω k => atIdx ω (fourVariable vX vY vZ k)
      (fourSlot nX nY₁ nY₂ nZ k)) from rfl,
    ← Measure.map_map hsplit.measurable hm, map_tableQuery _ _ hinj]
  exact hsplit.map_eq

end HLS

#check @HLS.map_tableQuery
#check @HLS.tableQuery_equidistributed
#check @HLS.measurePreserving_splitFour
#check @HLS.measurable_readFour
#check @HLS.map_readFour
