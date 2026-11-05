/-
  The auxiliary orientation coins extend the analysis sample space.
  Projecting to the original resampling table preserves its exact law
  and hence preserves the expectation of the existing MT algorithm.
-/
module

public import PPGraph.HLS.Bounds.CoinSaving
public import PPGraph.HLS.Probability.QueryLaw
public import PPGraph.MoserTardos.Probability.RandomInitExpectation

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory

namespace HLS

variable {V : Type} [DecidableEq V] {ι : Type} [DecidableEq ι]

noncomputable def augmentedSpaces (S : VarSpaces V) : VarSpaces (V ⊕ Finset ι) where
  space a := Sum.elim S.space (fun _ => OrientationCoin) a
  measSpace a := by cases a with
    | inl v => exact S.measSpace v
    | inr _ =>
      change MeasurableSpace OrientationCoin
      infer_instance
  measure a := by cases a with
    | inl v => exact S.measure v
    | inr _ => exact fairOrientation
  isProb a := by cases a with
    | inl v => exact S.isProb v
    | inr _ =>
      change IsProbabilityMeasure fairOrientation
      infer_instance

def originalTable {S : VarSpaces V} (η : LogSpace (augmentedSpaces (ι := ι) S)) : LogSpace S :=
  fun p => η (p.1, .inl p.2)

def auxiliaryCoins {S : VarSpaces V} (η : LogSpace (augmentedSpaces (ι := ι) S)) :
    Finset ι × ℕ → OrientationCoin := fun p => η (p.2, .inr p.1)

theorem measurable_originalTable (S : VarSpaces V) :
    Measurable (originalTable (S := S) (ι := ι)) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

theorem measurable_auxiliaryCoins (S : VarSpaces V) :
    Measurable (auxiliaryCoins (S := S) (ι := ι)) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

theorem map_originalTable (S : VarSpaces V) :
    (logMeasure (augmentedSpaces (ι := ι) S)).map originalTable = logMeasure S := by
  have : ∀ p, IsProbabilityMeasure (μCoin (augmentedSpaces (ι := ι) S) p) :=
    fun p => (augmentedSpaces S).isProb p.2
  have hinj : Function.Injective (fun p : ℕ × V => (p.1, Sum.inl (α := V) (β := Finset ι) p.2)) := by
    intro p q h
    have hfst : p.1 = q.1 := congrArg (fun z : ℕ × (V ⊕ Finset ι) => z.1) h
    have hsnd : Sum.inl p.2 = Sum.inl (β := Finset ι) q.2 :=
      congrArg (fun z : ℕ × (V ⊕ Finset ι) => z.2) h
    exact Prod.ext hfst (Sum.inl.inj hsnd)
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := μCoin (augmentedSpaces (ι := ι) S)) hinj

theorem map_auxiliaryCoins (S : VarSpaces V) :
    (logMeasure (augmentedSpaces (ι := ι) S)).map auxiliaryCoins =
      Measure.infinitePi (fun _ : Finset ι × ℕ => fairOrientation) := by
  have : ∀ p, IsProbabilityMeasure (μCoin (augmentedSpaces (ι := ι) S) p) :=
    fun p => (augmentedSpaces S).isProb p.2
  have hinj : Function.Injective (fun p : Finset ι × ℕ =>
      (p.2, Sum.inr (α := V) (β := Finset ι) p.1)) := by
    intro p q h
    have hfst : p.2 = q.2 := congrArg (fun z : ℕ × (V ⊕ Finset ι) => z.1) h
    have hsnd : Sum.inr p.1 = Sum.inr (α := V) q.1 :=
      congrArg (fun z : ℕ × (V ⊕ Finset ι) => z.2) h
    exact Prod.ext (Sum.inr.inj hsnd) hfst
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := μCoin (augmentedSpaces (ι := ι) S)) hinj

theorem augmented_expectedWork_eq {S : VarSpaces V} [Fintype ι] [Nonempty ι]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) :
    (∫⁻ η : LogSpace (augmentedSpaces (ι := ι) S),
      randomInitTLog P (originalTable η) ∂logMeasure (augmentedSpaces S)) = randomInitETLog P := by
  unfold randomInitETLog
  rw [← map_originalTable (ι := ι) S]
  exact (lintegral_map (measurable_randomInitTLog P hbad) (measurable_originalTable S)).symm

end HLS

#check @HLS.measurable_originalTable
#check @HLS.measurable_auxiliaryCoins
#check @HLS.map_originalTable
#check @HLS.map_auxiliaryCoins
#check @HLS.augmented_expectedWork_eq
