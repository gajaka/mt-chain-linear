import NeighborBase

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

noncomputable section

namespace NeighborSeparation

open MTChainFormal
open scoped BigOperators

/-- Average the three strong raw labels; weak is the original raw label one. -/
def profile (H : EdgeTable) (a b : Fin 3) (q : Fin 2) : Real :=
  if q = 1 then H a b 1 else (H a b 0 + H a b 2 + H a b 3) / 3

def liftLabel (q : Fin 2) (u : Fin 3) : Fin 4 :=
  if q = 1 then 1 else ![0, 2, 3] u

def profilePass (a b : Fin 3) (q : Fin 2) : Prop :=
  if q = 1 then a = b else b <= a

structure LocalRow where
  a : Fin 3
  b : Fin 3
  c : Fin 3
  d : Fin 3
  l : Fin 2
  r : Fin 2
  t : Fin 2

def rows : Fin 14 -> LocalRow := ![
  {a := 0, b := 0, c := 1, d := 0, l := 0, r := 0, t := 0},
  {a := 0, b := 0, c := 1, d := 0, l := 0, r := 0, t := 1},
  {a := 0, b := 0, c := 1, d := 0, l := 0, r := 1, t := 0},
  {a := 0, b := 0, c := 1, d := 0, l := 1, r := 1, t := 1},
  {a := 0, b := 0, c := 2, d := 0, l := 1, r := 0, t := 1},
  {a := 0, b := 0, c := 2, d := 1, l := 0, r := 0, t := 0},
  {a := 0, b := 0, c := 2, d := 1, l := 1, r := 1, t := 0},
  {a := 1, b := 0, c := 2, d := 2, l := 0, r := 0, t := 0},
  {a := 1, b := 0, c := 2, d := 2, l := 0, r := 0, t := 1},
  {a := 1, b := 1, c := 2, d := 0, l := 0, r := 0, t := 0},
  {a := 1, b := 1, c := 2, d := 0, l := 0, r := 1, t := 1},
  {a := 1, b := 1, c := 2, d := 0, l := 1, r := 0, t := 1},
  {a := 1, b := 1, c := 2, d := 1, l := 0, r := 0, t := 1},
  {a := 1, b := 1, c := 2, d := 1, l := 1, r := 1, t := 1}]

def weight : Fin 14 -> Real := ![13/96, 5/48, 7/96, 1/48, 1/24, 1/32, 3/32, 1/8, 1/24, 11/48, 1/32, 1/32, 1/96, 1/32]

def L (H : EdgeTable) : Real :=
  ((66) * profile H 0 0 0 +
    (30) * profile H 0 0 1 +
    (-33) * profile H 0 1 0 +
    (-15) * profile H 0 1 1 +
    (-33) * profile H 0 2 0 +
    (-15) * profile H 0 2 1 +
    (6) * profile H 1 0 0 +
    (-6) * profile H 1 0 1 +
    (36) * profile H 1 1 0 +
    (12) * profile H 1 1 1 +
    (-42) * profile H 1 2 0 +
    (-6) * profile H 1 2 1) / 288

def M (H : EdgeTable) : Real :=
  ((-24) * profile H 0 0 0 +
    (-8) * profile H 0 0 1 +
    (45) * profile H 0 1 0 +
    (19) * profile H 0 1 1 +
    (45) * profile H 0 2 0 +
    (19) * profile H 0 2 1 +
    (-24) * profile H 1 0 0 +
    (-8) * profile H 1 0 1 +
    (-24) * profile H 1 1 0 +
    (-8) * profile H 1 1 1 +
    (54) * profile H 1 2 0 +
    (10) * profile H 1 2 1 +
    (-24) * profile H 2 0 0 +
    (-8) * profile H 2 0 1 +
    (-24) * profile H 2 1 0 +
    (-8) * profile H 2 1 1 +
    (-24) * profile H 2 2 0 +
    (-8) * profile H 2 2 1) / 288

def R (H : EdgeTable) : Real :=
  ((-42) * profile H 0 0 0 +
    (-22) * profile H 0 0 1 +
    (-12) * profile H 0 1 0 +
    (-4) * profile H 0 1 1 +
    (-12) * profile H 0 2 0 +
    (-4) * profile H 0 2 1 +
    (18) * profile H 1 0 0 +
    (14) * profile H 1 0 1 +
    (-12) * profile H 1 1 0 +
    (-4) * profile H 1 1 1 +
    (-12) * profile H 1 2 0 +
    (-4) * profile H 1 2 1 +
    (24) * profile H 2 0 0 +
    (8) * profile H 2 0 1 +
    (24) * profile H 2 1 0 +
    (8) * profile H 2 1 1 +
    (24) * profile H 2 2 0 +
    (8) * profile H 2 2 1) / 288

def flux (h : EdgeCosts) (j : Nat) : Real := L (h (j+1)) - R (h (j+2))

def rawLocalDrift (A B C : EdgeTable) (a b c d : Fin 3) (l r t : Fin 4) : Real :=
  (A a b l - (A a 0 l + A a 1 l + A a 2 l)/3) +
  (B b c r - meanEdge B) +
  (C c d t - (C 0 d t + C 1 d t + C 2 d t)/3)

def profileDrift (A B C : EdgeTable) (y : LocalRow) : Real :=
  (profile A y.a y.b y.l -
    (profile A y.a 0 y.l + profile A y.a 1 y.l + profile A y.a 2 y.l)/3) +
  (profile B y.b y.c y.r - meanEdge B) +
  (profile C y.c y.d y.t -
    (profile C 0 y.d y.t + profile C 1 y.d y.t + profile C 2 y.d y.t)/3)

theorem weight_nonneg (k : Fin 14) : 0 <= weight k := by
  fin_cases k <;> norm_num [weight]

theorem weight_sum : (∑ k : Fin 14, weight k) = 1 := by
  norm_num [weight, Fin.sum_univ_succ]

theorem rows_left_pass (k : Fin 14) :
    profilePass (rows k).a (rows k).b (rows k).l := by
  fin_cases k <;> norm_num [rows, profilePass]

theorem rows_selected_fail (k : Fin 14) :
    ¬ (profilePass (rows k).b (rows k).c (rows k).r) := by
  fin_cases k <;> norm_num [rows, profilePass]

theorem lift_pass (a b : Fin 3) (q : Fin 2) (u : Fin 3) :
    MTChainProof.bridgePass a b (liftLabel q u) <-> profilePass a b q := by
  fin_cases q <;> fin_cases u <;> simp [liftLabel, profilePass, MTChainProof.bridgePass]

theorem profile_drift_average (A B C : EdgeTable) (y : LocalRow) :
    (∑ u : Fin 3, ∑ v : Fin 3, ∑ w : Fin 3,
      rawLocalDrift A B C y.a y.b y.c y.d
        (liftLabel y.l u) (liftLabel y.r v) (liftLabel y.t w)) / 27 =
      profileDrift A B C y := by
  rcases y with ⟨a,b,c,d,l,r,t⟩
  fin_cases l <;> fin_cases r <;> fin_cases t <;>
    norm_num [profileDrift, rawLocalDrift, profile, liftLabel, Fin.sum_univ_succ] <;> ring

theorem profile_drift_lower (A B C : EdgeTable) (y : LocalRow) (delta : Real)
    (hh : forall u v w : Fin 3,
      delta <= rawLocalDrift A B C y.a y.b y.c y.d
        (liftLabel y.l u) (liftLabel y.r v) (liftLabel y.t w)) :
    delta <= profileDrift A B C y := by
  have hs := Finset.sum_le_sum (s := Finset.univ) fun u _ =>
    Finset.sum_le_sum (s := Finset.univ) fun v _ =>
      Finset.sum_le_sum (s := Finset.univ) fun w _ => hh u v w
  have heq := profile_drift_average A B C y
  norm_num at hs
  linarith

theorem dual_average (A B C : EdgeTable) :
    (∑ k : Fin 14, weight k * profileDrift A B C (rows k)) =
      L A + M B + R C := by
  norm_num [weight, rows, profileDrift, L, M, R, meanEdge, profile,
    Fin.sum_univ_succ]
  ring

theorem dual_identity (H : EdgeTable) : L H + M H + R H = 0 := by
  unfold L M R
  ring

theorem dual_lower (A B C : EdgeTable) (delta : Real)
    (hh : forall k : Fin 14, delta <= profileDrift A B C (rows k)) :
    delta <= L A + M B + R C := by
  have hs := Finset.sum_le_sum (s := Finset.univ) fun k _ =>
    mul_le_mul_of_nonneg_left (hh k) (weight_nonneg k)
  rw [dual_average] at hs
  rw [← Finset.sum_mul, weight_sum, one_mul] at hs
  exact hs

theorem L_abs_le_mean (H : EdgeTable) (hH : forall a b r, 0 <= H a b r) :
    |L H| <= (15/4 : Real) * meanEdge H := by
  have h000 := hH 0 0 0
  have h001 := hH 0 0 1
  have h002 := hH 0 0 2
  have h003 := hH 0 0 3
  have h010 := hH 0 1 0
  have h011 := hH 0 1 1
  have h012 := hH 0 1 2
  have h013 := hH 0 1 3
  have h020 := hH 0 2 0
  have h021 := hH 0 2 1
  have h022 := hH 0 2 2
  have h023 := hH 0 2 3
  have h100 := hH 1 0 0
  have h101 := hH 1 0 1
  have h102 := hH 1 0 2
  have h103 := hH 1 0 3
  have h110 := hH 1 1 0
  have h111 := hH 1 1 1
  have h112 := hH 1 1 2
  have h113 := hH 1 1 3
  have h120 := hH 1 2 0
  have h121 := hH 1 2 1
  have h122 := hH 1 2 2
  have h123 := hH 1 2 3
  have h200 := hH 2 0 0
  have h201 := hH 2 0 1
  have h202 := hH 2 0 2
  have h203 := hH 2 0 3
  have h210 := hH 2 1 0
  have h211 := hH 2 1 1
  have h212 := hH 2 1 2
  have h213 := hH 2 1 3
  have h220 := hH 2 2 0
  have h221 := hH 2 2 1
  have h222 := hH 2 2 2
  have h223 := hH 2 2 3
  apply abs_le.mpr
  constructor <;>
    norm_num [L, meanEdge, profile, Fin.sum_univ_succ] <;> linarith

theorem R_abs_le_mean (H : EdgeTable) (hH : forall a b r, 0 <= H a b r) :
    |R H| <= (11/4 : Real) * meanEdge H := by
  have h000 := hH 0 0 0
  have h001 := hH 0 0 1
  have h002 := hH 0 0 2
  have h003 := hH 0 0 3
  have h010 := hH 0 1 0
  have h011 := hH 0 1 1
  have h012 := hH 0 1 2
  have h013 := hH 0 1 3
  have h020 := hH 0 2 0
  have h021 := hH 0 2 1
  have h022 := hH 0 2 2
  have h023 := hH 0 2 3
  have h100 := hH 1 0 0
  have h101 := hH 1 0 1
  have h102 := hH 1 0 2
  have h103 := hH 1 0 3
  have h110 := hH 1 1 0
  have h111 := hH 1 1 1
  have h112 := hH 1 1 2
  have h113 := hH 1 1 3
  have h120 := hH 1 2 0
  have h121 := hH 1 2 1
  have h122 := hH 1 2 2
  have h123 := hH 1 2 3
  have h200 := hH 2 0 0
  have h201 := hH 2 0 1
  have h202 := hH 2 0 2
  have h203 := hH 2 0 3
  have h210 := hH 2 1 0
  have h211 := hH 2 1 1
  have h212 := hH 2 1 2
  have h213 := hH 2 1 3
  have h220 := hH 2 2 0
  have h221 := hH 2 2 1
  have h222 := hH 2 2 2
  have h223 := hH 2 2 3
  apply abs_le.mpr
  constructor <;>
    norm_num [R, meanEdge, profile, Fin.sum_univ_succ] <;> linarith

end NeighborSeparation

#print axioms NeighborSeparation.dual_average
#print axioms NeighborSeparation.dual_lower
#print axioms NeighborSeparation.L_abs_le_mean
#print axioms NeighborSeparation.R_abs_le_mean
