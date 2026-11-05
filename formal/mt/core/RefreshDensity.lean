module

public import Filtering
public import ChainKernel

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace MTChainFormal
namespace RefreshDensity

open scoped BigOperators
open Filtering

section Generic

variable {ι : Type*} {κ : ι → Type*}
variable [Fintype ι] [DecidableEq ι]
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

theorem update_density_expectation (w : ∀ i, κ i → ℝ) (i : ι)
    (p : κ i → ℝ) (f : (∀ j, κ j) → ℝ) (hw : ∀ j, ∑ x, w j x = 1) :
    (∑ state, ProductFiltering.density w state * ∑ fresh, p fresh *
      f (Function.update state i fresh)) =
      ∑ target, ProductFiltering.density (Function.update w i p) target * f target := by
  classical
  calc
    _ = ∑ target, (∑ state, ProductFiltering.density w state *
        ∑ fresh, p fresh * (if Function.update state i fresh = target then 1 else 0)) *
          f target := by
      symm
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro state _
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro fresh _
      simp [mul_assoc]
    _ = _ := by simp_rw [ProductFiltering.update_density w i p _ hw]

omit [Fintype ι] [∀ i, DecidableEq (κ i)] in
theorem update_weight_sum (w : ∀ i, κ i → ℝ) (i : ι) (p : κ i → ℝ)
    (hw : ∀ j, ∑ x, w j x = 1) (hp : ∑ x, p x = 1) :
    ∀ j, ∑ x, (Function.update w i p) j x = 1 := by
  classical
  intro j
  by_cases h : j = i
  · subst j
    simpa using hp
  · simpa [Function.update_of_ne h] using hw j

end Generic

def incomingSite {n : ℕ} (i : Fin n) (hi : 0 < i.val) : Fin (n - 1) :=
  ⟨i.val - 1, by omega⟩

def outgoingSite {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) : Fin (n - 1) :=
  ⟨i.val, by omega⟩

noncomputable def incomingUpdate {n : ℕ} (i : Fin n)
    (x : ∀ c : Coord n, Alphabet c) (u : Fin 3) : ∀ c : Coord n, Alphabet c :=
  if h : 0 < i.val then Function.update x (.inl (incomingSite i h)) u else x

noncomputable def outgoingUpdate {n : ℕ} (i : Fin n)
    (x : ∀ c : Coord n, Alphabet c) (v : Fin 3) : ∀ c : Coord n, Alphabet c :=
  if h : i.val + 1 < n then Function.update x (.inl (outgoingSite i h)) v else x

noncomputable def tacticUpdate {n : ℕ} (i : Fin n)
    (x : ∀ c : Coord n, Alphabet c) (t : Fin 4) : ∀ c : Coord n, Alphabet c :=
  Function.update x (.inr i) t

noncomputable def incomingWeight {n : ℕ} (i : Fin n)
    (w : ∀ c : Coord n, Alphabet c → ℝ) : ∀ c : Coord n, Alphabet c → ℝ :=
  if h : 0 < i.val then Function.update w (.inl (incomingSite i h)) (fun _ => 1 / 3) else w

noncomputable def outgoingWeight {n : ℕ} (i : Fin n)
    (w : ∀ c : Coord n, Alphabet c → ℝ) : ∀ c : Coord n, Alphabet c → ℝ :=
  if h : i.val + 1 < n then Function.update w (.inl (outgoingSite i h)) (fun _ => 1 / 3) else w

noncomputable def tacticWeight {n : ℕ} (i : Fin n)
    (w : ∀ c : Coord n, Alphabet c → ℝ) : ∀ c : Coord n, Alphabet c → ℝ :=
  Function.update w (.inr i) (fun _ => 1 / 4)

theorem incomingUpdate_left {n : ℕ} (i : Fin n)
    (x : ∀ c : Coord n, Alphabet c) (u : Fin 3) (j : Fin (n - 1)) :
    incomingUpdate i x u (.inl j) = if j.val + 1 = i.val then u else x (.inl j) := by
  classical
  unfold incomingUpdate
  split
  next hi =>
    by_cases h : j = incomingSite i hi
    · subst j
      rw [ite_eq_left (by dsimp [incomingSite]; omega)]
      exact Function.update_self _ _ _
    · have heq : j.val + 1 ≠ i.val := by
        intro heq
        exact h (Fin.ext (by dsimp [incomingSite]; omega))
      rw [ite_eq_right heq]
      exact Function.update_of_ne (by simpa using h) _ _
  next hi =>
    rw [ite_eq_right (by omega : j.val + 1 ≠ i.val)]

theorem outgoingUpdate_left {n : ℕ} (i : Fin n)
    (x : ∀ c : Coord n, Alphabet c) (u : Fin 3) (j : Fin (n - 1)) :
    outgoingUpdate i x u (.inl j) = if j.val + 1 = i.val + 1 then u else x (.inl j) := by
  classical
  unfold outgoingUpdate
  split
  next hi =>
    by_cases h : j = outgoingSite i hi
    · subst j
      rw [ite_eq_left (by dsimp [outgoingSite])]
      exact Function.update_self _ _ _
    · have heq : j.val + 1 ≠ i.val + 1 := by
        intro heq
        exact h (Fin.ext (by dsimp [outgoingSite]; omega))
      rw [ite_eq_right heq]
      exact Function.update_of_ne (by simpa using h) _ _
  next hi =>
    rw [ite_eq_right (by omega : j.val + 1 ≠ i.val + 1)]

theorem incomingUpdate_right {n : ℕ} (i : Fin n)
    (x : ∀ c : Coord n, Alphabet c) (u : Fin 3) (j : Fin n) :
    incomingUpdate i x u (.inr j) = x (.inr j) := by
  classical
  unfold incomingUpdate
  split
  · exact Function.update_of_ne (by intro h; cases h) _ _
  · rfl

theorem outgoingUpdate_right {n : ℕ} (i : Fin n)
    (x : ∀ c : Coord n, Alphabet c) (u : Fin 3) (j : Fin n) :
    outgoingUpdate i x u (.inr j) = x (.inr j) := by
  classical
  unfold outgoingUpdate
  split
  · exact Function.update_of_ne (by intro h; cases h) _ _
  · rfl

theorem tacticUpdate_left {n : ℕ} (i : Fin n)
    (x : ∀ c : Coord n, Alphabet c) (u : Fin 4) (j : Fin (n - 1)) :
    tacticUpdate i x u (.inl j) = x (.inl j) := by
  classical
  exact Function.update_of_ne (by intro h; cases h) _ _

theorem tacticUpdate_right {n : ℕ} (i : Fin n)
    (x : ∀ c : Coord n, Alphabet c) (u : Fin 4) (j : Fin n) :
    tacticUpdate i x u (.inr j) = if j = i then u else x (.inr j) := by
  classical
  by_cases h : j = i
  · subst j
    rw [ite_eq_left rfl]
    exact Function.update_self _ _ _
  · rw [ite_eq_right h]
    exact Function.update_of_ne (by simpa using h) _ _

theorem toCoords_replace {n : ℕ} (s : ChainState n) (i : Fin n) (u : Draw) :
    toCoords (replace s i u) =
      tacticUpdate i (outgoingUpdate i (incomingUpdate i (toCoords s) u.1) u.2.1) u.2.2 := by
  funext c
  cases c with
  | inl j =>
      rw [tacticUpdate_left, outgoingUpdate_left, incomingUpdate_left]
      change (if j.val + 1 = i.val then u.1
        else if j.val + 1 = i.val + 1 then u.2.1 else s.values j) = _
      by_cases h0 : j.val + 1 = i.val
      · have h1 : j.val + 1 ≠ i.val + 1 := by omega
        rw [ite_eq_left h0, ite_eq_right h1, ite_eq_left h0]
      · simp [h0, toCoords]
  | inr j =>
      rw [tacticUpdate_right, outgoingUpdate_right, incomingUpdate_right]
      rfl

theorem incomingWeight_left {n : ℕ} (i : Fin n)
    (w : ∀ c : Coord n, Alphabet c → ℝ) (j : Fin (n - 1)) (x : Fin 3) :
    incomingWeight i w (.inl j) x = if j.val + 1 = i.val then 1 / 3 else w (.inl j) x := by
  classical
  unfold incomingWeight
  split
  next hi =>
    by_cases h : j = incomingSite i hi
    · subst j
      rw [Function.update_self, ite_eq_left (by dsimp [incomingSite]; omega)]
    · have heq : j.val + 1 ≠ i.val := by
        intro heq
        exact h (Fin.ext (by dsimp [incomingSite]; omega))
      rw [Function.update_of_ne (by simpa using h), ite_eq_right heq]
  next hi => rw [ite_eq_right (by omega : j.val + 1 ≠ i.val)]

theorem outgoingWeight_left {n : ℕ} (i : Fin n)
    (w : ∀ c : Coord n, Alphabet c → ℝ) (j : Fin (n - 1)) (x : Fin 3) :
    outgoingWeight i w (.inl j) x = if j.val + 1 = i.val + 1 then 1 / 3 else w (.inl j) x := by
  classical
  unfold outgoingWeight
  split
  next hi =>
    by_cases h : j = outgoingSite i hi
    · subst j
      rw [Function.update_self, ite_eq_left (by dsimp [outgoingSite])]
    · have heq : j.val + 1 ≠ i.val + 1 := by
        intro heq
        exact h (Fin.ext (by dsimp [outgoingSite]; omega))
      rw [Function.update_of_ne (by simpa using h), ite_eq_right heq]
  next hi => rw [ite_eq_right (by omega : j.val + 1 ≠ i.val + 1)]

theorem incomingWeight_right {n : ℕ} (i : Fin n)
    (w : ∀ c : Coord n, Alphabet c → ℝ) (j : Fin n) (x : Fin 4) :
    incomingWeight i w (.inr j) x = w (.inr j) x := by
  classical
  unfold incomingWeight
  split
  · exact congrFun (Function.update_of_ne (by intro h; cases h) _ _) x
  · rfl

theorem outgoingWeight_right {n : ℕ} (i : Fin n)
    (w : ∀ c : Coord n, Alphabet c → ℝ) (j : Fin n) (x : Fin 4) :
    outgoingWeight i w (.inr j) x = w (.inr j) x := by
  classical
  unfold outgoingWeight
  split
  · exact congrFun (Function.update_of_ne (by intro h; cases h) _ _) x
  · rfl

theorem tacticWeight_left {n : ℕ} (i : Fin n)
    (w : ∀ c : Coord n, Alphabet c → ℝ) (j : Fin (n - 1)) (x : Fin 3) :
    tacticWeight i w (.inl j) x = w (.inl j) x := by
  classical
  exact congrFun (Function.update_of_ne (by intro h; cases h) _ _) x

theorem tacticWeight_right {n : ℕ} (i : Fin n)
    (w : ∀ c : Coord n, Alphabet c → ℝ) (j : Fin n) (x : Fin 4) :
    tacticWeight i w (.inr j) x = if j = i then 1 / 4 else w (.inr j) x := by
  classical
  by_cases h : j = i
  · subst j
    rw [ite_eq_left rfl]
    unfold tacticWeight
    rw [Function.update_self]
  · rw [ite_eq_right h]
    exact congrFun (Function.update_of_ne (by simpa using h) _ _) x

theorem refreshedWeight_eq_post {n : ℕ} (q : PrefixDatum n) :
    tacticWeight q.1 (outgoingWeight q.1 (incomingWeight q.1 (sourceWeight q))) = postWeight q := by
  classical
  funext c x
  cases c with
  | inl j =>
      rw [tacticWeight_left, outgoingWeight_left, incomingWeight_left]
      by_cases h0 : j.val + 1 = q.1.val <;>
        by_cases h1 : j.val = q.1.val <;>
          simp [postWeight, refreshCoords, freshWeight, h0, h1]
  | inr j =>
      rw [tacticWeight_right, outgoingWeight_right, incomingWeight_right]
      by_cases h : j = q.1 <;> simp [postWeight, refreshCoords, freshWeight, h]

theorem incomingWeight_sum {n : ℕ} (i : Fin n)
    (w : ∀ c : Coord n, Alphabet c → ℝ) (hw : ∀ c, ∑ x, w c x = 1) :
    ∀ c, ∑ x, incomingWeight i w c x = 1 := by
  classical
  unfold incomingWeight
  split
  · apply update_weight_sum w _ _ hw
    change (∑ _x : Fin 3, (1 / 3 : ℝ)) = 1
    norm_num
  · exact hw

theorem outgoingWeight_sum {n : ℕ} (i : Fin n)
    (w : ∀ c : Coord n, Alphabet c → ℝ) (hw : ∀ c, ∑ x, w c x = 1) :
    ∀ c, ∑ x, outgoingWeight i w c x = 1 := by
  classical
  unfold outgoingWeight
  split
  · apply update_weight_sum w _ _ hw
    change (∑ _x : Fin 3, (1 / 3 : ℝ)) = 1
    norm_num
  · exact hw

theorem incoming_density_expectation {n : ℕ} (i : Fin n)
    (w : ∀ c : Coord n, Alphabet c → ℝ) (hw : ∀ c, ∑ x, w c x = 1)
    (f : (∀ c : Coord n, Alphabet c) → ℝ) :
    (∑ state, ProductFiltering.density w state *
      ∑ u : Fin 3, (1 / 3 : ℝ) * f (incomingUpdate i state u)) =
        ∑ state, ProductFiltering.density (incomingWeight i w) state * f state := by
  classical
  by_cases h : 0 < i.val
  · simpa only [incomingUpdate, incomingWeight, dite_eq_left h, alphabetFintype, Alphabet] using
      update_density_expectation w (.inl (incomingSite i h)) (fun _ => 1 / 3) f hw
  · simp [incomingUpdate, incomingWeight, h]

theorem outgoing_density_expectation {n : ℕ} (i : Fin n)
    (w : ∀ c : Coord n, Alphabet c → ℝ) (hw : ∀ c, ∑ x, w c x = 1)
    (f : (∀ c : Coord n, Alphabet c) → ℝ) :
    (∑ state, ProductFiltering.density w state *
      ∑ u : Fin 3, (1 / 3 : ℝ) * f (outgoingUpdate i state u)) =
        ∑ state, ProductFiltering.density (outgoingWeight i w) state * f state := by
  classical
  by_cases h : i.val + 1 < n
  · simpa only [outgoingUpdate, outgoingWeight, dite_eq_left h, alphabetFintype, Alphabet] using
      update_density_expectation w (.inl (outgoingSite i h)) (fun _ => 1 / 3) f hw
  · simp [outgoingUpdate, outgoingWeight, h]

theorem tactic_density_expectation {n : ℕ} (i : Fin n)
    (w : ∀ c : Coord n, Alphabet c → ℝ) (hw : ∀ c, ∑ x, w c x = 1)
    (f : (∀ c : Coord n, Alphabet c) → ℝ) :
    (∑ state, ProductFiltering.density w state *
      ∑ u : Fin 4, (1 / 4 : ℝ) * f (tacticUpdate i state u)) =
        ∑ state, ProductFiltering.density (tacticWeight i w) state * f state := by
  exact update_density_expectation w (.inr i) (fun _ => 1 / 4) f hw

theorem drawAverage_nested (f : Draw → ℝ) :
    drawAverage f = ∑ a : Fin 3, (1 / 3 : ℝ) *
      ∑ b : Fin 3, (1 / 3 : ℝ) * ∑ t : Fin 4, (1 / 4 : ℝ) * f (a, b, t) := by
  unfold drawAverage
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem rawCompletion_density_source {n : ℕ} (q : PrefixDatum n) (s : ChainState n) :
    rawCompletion q s = ProductFiltering.density (sourceWeight q) (toCoords s) := rfl

end RefreshDensity

namespace Filtering

open RefreshDensity
open scoped BigOperators

set_option maxHeartbeats 2000000 in
/-- The actual 36-draw replacement sends the completion product law to
    the independently refreshed coordinate product law. No filtering identity
    or validity assumption is used in this fixed-index update calculation. -/
theorem raw_replace_expectation {n : ℕ} (q : PrefixDatum n) (f : ChainState n → ℝ) :
    (∑ s, rawCompletion q s * drawAverage (fun u => f (replace s q.1 u))) =
      ∑ t, ProductFiltering.density (postWeight q) (toCoords t) * f t := by
  classical
  let w0 := sourceWeight q
  let w1 := incomingWeight q.1 w0
  let w2 := outgoingWeight q.1 w1
  let w3 := tacticWeight q.1 w2
  let fC := fun x : ∀ c : Coord n, Alphabet c => f (fromCoords x)
  have hw0 : ∀ c, ∑ x, w0 c x = 1 := sourceWeight_sum q
  have hw1 : ∀ c, ∑ x, w1 c x = 1 := incomingWeight_sum q.1 w0 hw0
  have hw2 : ∀ c, ∑ x, w2 c x = 1 := outgoingWeight_sum q.1 w1 hw1
  have hreplace (s : ChainState n) (u : Draw) : replace s q.1 u =
      fromCoords (tacticUpdate q.1
        (outgoingUpdate q.1 (incomingUpdate q.1 (toCoords s) u.1) u.2.1) u.2.2) := by
    have h := congrArg fromCoords (toCoords_replace s q.1 u)
    simpa only [fromCoords_toCoords] using h
  have hraw :
      (∑ s, rawCompletion q s * drawAverage (fun u => f (replace s q.1 u))) =
        ∑ x, ProductFiltering.density w0 x *
          ∑ a : Fin 3, (1 / 3 : ℝ) * ∑ b : Fin 3, (1 / 3 : ℝ) *
            ∑ t : Fin 4, (1 / 4 : ℝ) *
              fC (tacticUpdate q.1 (outgoingUpdate q.1 (incomingUpdate q.1 x a) b) t) := by
    calc
      _ = ∑ s : ChainState n, ProductFiltering.density w0 (toCoords s) *
          ∑ a : Fin 3, (1 / 3 : ℝ) * ∑ b : Fin 3, (1 / 3 : ℝ) *
            ∑ t : Fin 4, (1 / 4 : ℝ) *
              fC (tacticUpdate q.1
                (outgoingUpdate q.1 (incomingUpdate q.1 (toCoords s) a) b) t) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [rawCompletion_density_source, drawAverage_nested]
          simp_rw [hreplace]
          rfl
      _ = _ := (coordinateEquiv n).sum_comp
        (fun x => ProductFiltering.density w0 x *
          ∑ a : Fin 3, (1 / 3 : ℝ) * ∑ b : Fin 3, (1 / 3 : ℝ) *
            ∑ t : Fin 4, (1 / 4 : ℝ) *
              fC (tacticUpdate q.1 (outgoingUpdate q.1 (incomingUpdate q.1 x a) b) t))
  have hcoords :
      (∑ x, ProductFiltering.density w0 x *
        ∑ a : Fin 3, (1 / 3 : ℝ) * ∑ b : Fin 3, (1 / 3 : ℝ) *
          ∑ t : Fin 4, (1 / 4 : ℝ) *
            fC (tacticUpdate q.1 (outgoingUpdate q.1 (incomingUpdate q.1 x a) b) t)) =
        ∑ x, ProductFiltering.density w3 x * fC x := by
    calc
      _ = ∑ x, ProductFiltering.density w1 x *
          ∑ b : Fin 3, (1 / 3 : ℝ) * ∑ t : Fin 4, (1 / 4 : ℝ) *
            fC (tacticUpdate q.1 (outgoingUpdate q.1 x b) t) :=
          incoming_density_expectation (n := n) q.1 w0 hw0
            (fun x => ∑ b : Fin 3, (1 / 3 : ℝ) * ∑ t : Fin 4, (1 / 4 : ℝ) *
              fC (tacticUpdate q.1 (outgoingUpdate q.1 x b) t))
      _ = ∑ x, ProductFiltering.density w2 x *
          ∑ t : Fin 4, (1 / 4 : ℝ) * fC (tacticUpdate q.1 x t) :=
          outgoing_density_expectation (n := n) q.1 w1 hw1
            (fun x => ∑ t : Fin 4, (1 / 4 : ℝ) * fC (tacticUpdate q.1 x t))
      _ = _ := tactic_density_expectation q.1 w2 hw2 fC
  rw [hraw, hcoords]
  have hw3 : w3 = postWeight q := refreshedWeight_eq_post q
  rw [hw3]
  have heq := (coordinateEquiv n).sum_comp
    (fun x => ProductFiltering.density (postWeight q) x * f (fromCoords x))
  simpa only [fC, coordinateEquiv, Equiv.coe_fn_mk, fromCoords_toCoords] using heq.symm

theorem raw_replace_density {n : ℕ} (q : PrefixDatum n) (target : ChainState n) :
    (∑ s, rawCompletion q s * drawAverage
      (fun u => if replace s q.1 u = target then (1 : ℝ) else 0)) =
        ProductFiltering.density (postWeight q) (toCoords target) := by
  simpa [mul_ite] using raw_replace_expectation q
    (fun s => if s = target then (1 : ℝ) else 0)

end Filtering
end MTChainFormal
