/- A queried auxiliary coin is independent of four queried data blocks. -/
module

public import PPGraph.HLS.Probability.AugmentedSpace

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory

namespace HLS

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type} [DecidableEq ι]

def coinAndFourRead {X Y Z : Type} (K : Finset ι) (r : ℕ)
    (vX : X → V) (vY : Y → V) (vZ : Z → V)
    (nX : X → ℕ) (nY₁ nY₂ : Y → ℕ) (nZ : Z → ℕ)
    (η : LogSpace (augmentedSpaces S)) :=
  (auxiliaryCoins η (K, r), readFour vX vY vZ nX nY₁ nY₂ nZ (originalTable η))

theorem map_coinAndFourRead {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (K : Finset ι) (r : ℕ) (vX : X → V) (vY : Y → V) (vZ : Z → V)
    (nX : X → ℕ) (nY₁ nY₂ : Y → ℕ) (nZ : Z → ℕ)
    (hinj : Function.Injective (fun k : FourIndex X Y Z =>
      (fourSlot nX nY₁ nY₂ nZ k, fourVariable vX vY vZ k))) :
    (logMeasure (augmentedSpaces S)).map (coinAndFourRead K r vX vY vZ nX nY₁ nY₂ nZ) =
      fairOrientation.prod
        (((Measure.pi (fun x => S.measure (vX x))).prod
          (Measure.pi (fun z => S.measure (vZ z)))).prod
          ((Measure.pi (fun y => S.measure (vY y))).prod
            (Measure.pi (fun y => S.measure (vY y))))) := by
  let A := augmentedSpaces (ι := ι) S
  let v : Unit ⊕ FourIndex X Y Z → V ⊕ Finset ι :=
    Sum.elim (fun _ => Sum.inr K) (fun k => Sum.inl (fourVariable vX vY vZ k))
  let n : Unit ⊕ FourIndex X Y Z → ℕ := Sum.elim (fun _ => r) (fourSlot nX nY₁ nY₂ nZ)
  let μ := fun k => A.measure (v k)
  have : ∀ k, IsProbabilityMeasure (μ k) := fun k => A.isProb (v k)
  have hqinj : Function.Injective (fun k => (n k, v k)) := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => rfl
      | inr b =>
        have hs : Sum.inr K = Sum.inl (β := Finset ι) (fourVariable vX vY vZ b) := congrArg Prod.snd h
        cases hs
    | inr a =>
      cases b with
      | inl b =>
        have hs : Sum.inl (fourVariable vX vY vZ a) = Sum.inr (α := V) K := congrArg Prod.snd h
        cases hs
      | inr b =>
        apply congrArg Sum.inr
        apply hinj
        have hfst : fourSlot nX nY₁ nY₂ nZ a = fourSlot nX nY₁ nY₂ nZ b :=
          congrArg (fun z : ℕ × (V ⊕ Finset ι) => z.1) h
        have hsnd : Sum.inl (fourVariable vX vY vZ a) =
            Sum.inl (β := Finset ι) (fourVariable vX vY vZ b) :=
          congrArg (fun z : ℕ × (V ⊕ Finset ι) => z.2) h
        exact Prod.ext hfst (Sum.inl.inj hsnd)
  have hquery : MeasurePreserving (fun η : LogSpace A => fun k => atIdx η (v k) (n k))
      (logMeasure A) (Measure.pi μ) :=
    ⟨Measurable.of_eval (fun _ => measurable_pi_apply _), map_tableQuery v n hqinj⟩
  have hsplit := measurePreserving_sumPiEquivProdPi μ
  have hcoin := measurePreserving_funUnique fairOrientation Unit
  have hfour := measurePreserving_splitFour (S := S) vX vY vZ
  have : ∀ a, IsProbabilityMeasure (S.measure a) := S.isProb
  have hread := ((hcoin.prod hfour).comp hsplit).comp hquery
  exact hread.map_eq

end HLS

#check @HLS.map_coinAndFourRead
