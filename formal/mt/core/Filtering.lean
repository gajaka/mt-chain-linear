module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Chain

@[expose] public section

/-!
Finite product filtering by an exactly observed cylinder.

The completion law is constructed coordinate by coordinate. The factorization
below derives the observation/completion identity from independent coordinates;
it does not assume an intertwining identity between two transition kernels.
-/

namespace MTChainFormal
namespace ProductFiltering

open scoped BigOperators

variable {ι : Type*} {κ : ι → Type*}
variable [Fintype ι] [DecidableEq ι]
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

def density (w : ∀ i, κ i → ℝ) (s : ∀ i, κ i) : ℝ :=
  ∏ i, w i (s i)

def Agrees (read : Finset ι) (pinned state : ∀ i, κ i) : Prop :=
  ∀ i ∈ read, state i = pinned i

instance agreesDecidable (read : Finset ι) (pinned state : ∀ i, κ i) :
    Decidable (Agrees read pinned state) := by
  unfold Agrees
  infer_instance

def prefixMass (w : ∀ i, κ i → ℝ) (read : Finset ι)
    (pinned : ∀ i, κ i) : ℝ :=
  ∏ i, if i ∈ read then w i (pinned i) else 1

def completion (w : ∀ i, κ i → ℝ) (read : Finset ι)
    (pinned state : ∀ i, κ i) : ℝ :=
  ∏ i, if i ∈ read then (if state i = pinned i then 1 else 0) else w i (state i)

omit [∀ i, DecidableEq (κ i)] in
theorem density_sum (w : ∀ i, κ i → ℝ)
    (hnorm : ∀ i, ∑ x, w i x = 1) :
    ∑ state, density w state = 1 := by
  classical
  simp only [density]
  rw [← Fintype.prod_sum w]
  simp only [hnorm, Finset.prod_const_one]

theorem completion_sum (w : ∀ i, κ i → ℝ) (read : Finset ι)
    (pinned : ∀ i, κ i) (hnorm : ∀ i, ∑ x, w i x = 1) :
    ∑ state, completion w read pinned state = 1 := by
  classical
  simp only [completion]
  rw [← Fintype.prod_sum (fun i (x : κ i) =>
    if i ∈ read then (if x = pinned i then (1 : ℝ) else 0) else w i x)]
  apply Finset.prod_eq_one
  intro i _
  by_cases hi : i ∈ read
  · simp [hi]
  · simpa [hi] using hnorm i

omit [∀ i, Fintype (κ i)] in
theorem completion_nonneg (w : ∀ i, κ i → ℝ) (read : Finset ι)
    (pinned state : ∀ i, κ i) (hw : ∀ i x, 0 ≤ w i x) :
    0 ≤ completion w read pinned state := by
  classical
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> simp_all

omit [∀ i, Fintype (κ i)] in
theorem completion_zero_of_not_agrees (w : ∀ i, κ i → ℝ) (read : Finset ι)
    (pinned state : ∀ i, κ i) (h : ¬ Agrees read pinned state) :
    completion w read pinned state = 0 := by
  classical
  simp only [Agrees, not_forall] at h
  obtain ⟨i, hread, hne⟩ := h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hread, hne]

omit [∀ i, Fintype (κ i)] in
theorem factor_on_agrees (w : ∀ i, κ i → ℝ) (read : Finset ι)
    (pinned state : ∀ i, κ i) (h : Agrees read pinned state) :
    density w state = prefixMass w read pinned * completion w read pinned state := by
  classical
  rw [density, prefixMass, completion, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ read
  · simp [hi, h i hi]
  · simp [hi]

omit [∀ i, Fintype (κ i)] in
theorem cylinder_factor (w : ∀ i, κ i → ℝ) (read : Finset ι)
    (pinned state : ∀ i, κ i) :
    (if Agrees read pinned state then density w state else 0) =
      prefixMass w read pinned * completion w read pinned state := by
  classical
  by_cases h : Agrees read pinned state
  · simpa [h] using factor_on_agrees w read pinned state h
  · simp [h, completion_zero_of_not_agrees w read pinned state h]

omit [∀ i, Fintype (κ i)] in
theorem completion_congr_unread (w v : ∀ i, κ i → ℝ) (read : Finset ι)
    (pinned state : ∀ i, κ i)
    (h : ∀ i, i ∉ read → ∀ x, w i x = v i x) :
    completion w read pinned state = completion v read pinned state := by
  classical
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ read
  · simp [hi]
  · simp [hi, h i hi]

theorem cylinder_mass (w : ∀ i, κ i → ℝ) (read : Finset ι)
    (pinned : ∀ i, κ i) (hnorm : ∀ i, ∑ x, w i x = 1) :
    (∑ state, if Agrees read pinned state then density w state else 0) =
      prefixMass w read pinned := by
  classical
  simp_rw [cylinder_factor]
  rw [← Finset.mul_sum, completion_sum w read pinned hnorm, mul_one]

omit [∀ i, Fintype (κ i)] in
theorem observation_factor {Q : Type*} [DecidableEq Q] (observe : (∀ i, κ i) → Q)
    (q : Q) (w : ∀ i, κ i → ℝ) (read : Finset ι) (pinned state : ∀ i, κ i)
    (hfiber : ∀ s, observe s = q ↔ Agrees read pinned s) :
    (if observe state = q then density w state else 0) =
      prefixMass w read pinned * completion w read pinned state := by
  classical
  simpa only [hfiber state] using cylinder_factor w read pinned state

omit [∀ i, Fintype (κ i)] [DecidableEq ι] in
theorem equality_indicator_product (f g : ∀ i, κ i) :
    (if f = g then (1 : ℝ) else 0) =
      ∏ i, if f i = g i then (1 : ℝ) else 0 := by
  classical
  by_cases h : f = g
  · simp [h]
  · have hn : ∃ i, f i ≠ g i := by
      by_contra hx
      push Not at hx
      exact h (funext hx)
    obtain ⟨i, hi⟩ := hn
    rw [ite_eq_right h]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

def refreshPair (refresh : Finset ι) (draw : ∀ i, κ i × κ i) (i : ι) : κ i :=
  if i ∈ refresh then (draw i).2 else (draw i).1

theorem refresh_pair_density (v w : ∀ i, κ i → ℝ) (refresh : Finset ι)
    (target : ∀ i, κ i)
    (hv : ∀ i, ∑ x, v i x = 1) (hw : ∀ i, ∑ x, w i x = 1) :
    (∑ draw : ∀ i, κ i × κ i,
      (∏ i, v i (draw i).1 * w i (draw i).2) *
        (if refreshPair refresh draw = target then 1 else 0)) =
      density (fun i x => if i ∈ refresh then w i x else v i x) target := by
  classical
  have hpoint (draw : ∀ i, κ i × κ i) :
      (∏ i, v i (draw i).1 * w i (draw i).2) *
          (if refreshPair refresh draw = target then (1 : ℝ) else 0) =
        ∏ i, (v i (draw i).1 * w i (draw i).2) *
          (if (if i ∈ refresh then (draw i).2 else (draw i).1) = target i then 1 else 0) := by
    rw [equality_indicator_product, ← Finset.prod_mul_distrib]
    rfl
  simp_rw [hpoint]
  rw [← Fintype.prod_sum (fun i (x : κ i × κ i) =>
    (v i x.1 * w i x.2) *
      (if (if i ∈ refresh then x.2 else x.1) = target i then (1 : ℝ) else 0))]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]
  by_cases hi : i ∈ refresh
  · simp [hi, ← Finset.sum_mul, hv i]
  · simp [hi, ← Finset.mul_sum, hw i]

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
theorem update_eq_iff (state target : ∀ i, κ i) (i : ι) (fresh : κ i) :
    Function.update state i fresh = target ↔
      fresh = target i ∧ Agrees (Finset.univ.erase i) target state := by
  classical
  constructor
  · intro heq
    constructor
    · simpa using congrFun heq i
    · intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simpa [Function.update_of_ne hji] using congrFun heq j
  · rintro ⟨hfresh, hrest⟩
    funext j
    by_cases hji : j = i
    · subst j
      simpa using hfresh
    · have hj : j ∈ Finset.univ.erase i := by simp [hji]
      simpa [Function.update_of_ne hji] using hrest j hj

theorem update_density (w : ∀ i, κ i → ℝ) (i : ι) (freshLaw : κ i → ℝ)
    (target : ∀ i, κ i) (hw : ∀ j, ∑ x, w j x = 1) :
    (∑ state, density w state *
      ∑ fresh, freshLaw fresh *
        (if Function.update state i fresh = target then (1 : ℝ) else 0)) =
      density (Function.update w i freshLaw) target := by
  classical
  have hinner (state : ∀ i, κ i) :
      (∑ fresh, freshLaw fresh *
        (if Function.update state i fresh = target then (1 : ℝ) else 0)) =
        if Agrees (Finset.univ.erase i) target state then freshLaw (target i) else 0 := by
    simp_rw [update_eq_iff]
    by_cases h : Agrees (Finset.univ.erase i) target state
    · simp [h]
    · simp [h]
  simp_rw [hinner]
  calc
    _ = freshLaw (target i) *
        ∑ state, if Agrees (Finset.univ.erase i) target state then density w state else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro state _
      split_ifs <;> ring
    _ = freshLaw (target i) * prefixMass w (Finset.univ.erase i) target := by
      rw [cylinder_mass w (Finset.univ.erase i) target hw]
    _ = density (Function.update w i freshLaw) target := by
      rw [density, ← Finset.mul_prod_erase Finset.univ
        (fun j => (Function.update w i freshLaw) j (target j)) (Finset.mem_univ i)]
      simp only [Function.update_self]
      congr 1
      rw [prefixMass, Finset.prod_ite_mem_eq]
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [Function.update_of_ne hji]

end ProductFiltering

namespace Filtering

abbrev Coord (n : ℕ) := Fin (n - 1) ⊕ Fin n

def Alphabet {n : ℕ} : Coord n → Type
  | .inl _ => Fin 3
  | .inr _ => Fin 4

instance alphabetFintype {n : ℕ} (c : Coord n) : Fintype (Alphabet c) := by
  cases c with
  | inl j => change Fintype (Fin 3); infer_instance
  | inr j => change Fintype (Fin 4); infer_instance

instance alphabetDecidableEq {n : ℕ} (c : Coord n) : DecidableEq (Alphabet c) := by
  cases c with
  | inl j => change DecidableEq (Fin 3); infer_instance
  | inr j => change DecidableEq (Fin 4); infer_instance

def toCoords {n : ℕ} (s : ChainState n) : ∀ c : Coord n, Alphabet c
  | .inl j => s.values j
  | .inr j => s.tactic j

def fromCoords {n : ℕ} (x : ∀ c : Coord n, Alphabet c) : ChainState n where
  values j := x (.inl j)
  tactic j := x (.inr j)

def coordinateEquiv (n : ℕ) : ChainState n ≃ (∀ c : Coord n, Alphabet c) where
  toFun := toCoords
  invFun := fromCoords
  left_inv s := by cases s; rfl
  right_inv x := by funext c; cases c <;> rfl

@[simp] theorem fromCoords_toCoords {n : ℕ} (s : ChainState n) :
    fromCoords (toCoords s) = s := (coordinateEquiv n).left_inv s

@[simp] theorem toCoords_fromCoords {n : ℕ} (x : ∀ c : Coord n, Alphabet c) :
    toCoords (fromCoords x) = x := (coordinateEquiv n).right_inv x

noncomputable def readCoords {n : ℕ} (cut : ℕ) : Finset (Coord n) := by
  classical
  exact Finset.univ.filter (fun c => match c with
    | .inl j => j.val + 1 ≤ cut
    | .inr j => j.val < cut)

@[simp] theorem mem_readCoords_left {n : ℕ} (cut : ℕ) (j : Fin (n - 1)) :
    Sum.inl j ∈ readCoords cut ↔ j.val + 1 ≤ cut := by simp [readCoords]

@[simp] theorem mem_readCoords_right {n : ℕ} (cut : ℕ) (j : Fin n) :
    Sum.inr j ∈ readCoords cut ↔ j.val < cut := by simp [readCoords]

def truncateState {n : ℕ} (s : ChainState n) (cut : ℕ) : ChainState n where
  values j := if j.val + 1 ≤ cut then s.values j else 0
  tactic j := if j.val < cut then s.tactic j else 0

theorem chainState_ext {n : ℕ} {s t : ChainState n}
    (hv : s.values = t.values) (ht : s.tactic = t.tactic) : s = t := by
  cases s
  cases t
  cases hv
  cases ht
  rfl

theorem truncateState_idempotent {n : ℕ} (s : ChainState n) (cut : ℕ) :
    truncateState (truncateState s cut) cut = truncateState s cut := by
  apply chainState_ext
  · funext j
    by_cases hj : j.val + 1 ≤ cut <;> simp only [truncateState, hj, ite_true, ite_false]
  · funext j
    by_cases hj : j.val < cut <;> simp only [truncateState, hj, ite_true, ite_false]

theorem agrees_truncate {n : ℕ} (s : ChainState n) (cut : ℕ) :
    ProductFiltering.Agrees (readCoords cut) (toCoords s) (toCoords (truncateState s cut)) := by
  intro c hc
  cases c with
  | inl j =>
    simp only [mem_readCoords_left] at hc
    change (if j.val + 1 ≤ cut then s.values j else 0) = s.values j
    exact ite_eq_left hc
  | inr j =>
    simp only [mem_readCoords_right] at hc
    change (if j.val < cut then s.tactic j else 0) = s.tactic j
    exact ite_eq_left hc

theorem truncateState_eq_of_agrees {n : ℕ} (s t : ChainState n) (cut : ℕ)
    (h : ProductFiltering.Agrees (readCoords cut) (toCoords s) (toCoords t)) :
    truncateState t cut = truncateState s cut := by
  apply chainState_ext
  · funext j
    by_cases hj : j.val + 1 ≤ cut
    · have heq := h (.inl j) (by simpa using hj)
      change t.values j = s.values j at heq
      simpa only [truncateState, hj, ite_true] using heq
    · simp only [truncateState, hj, ite_false]
  · funext j
    by_cases hj : j.val < cut
    · have heq := h (.inr j) (by simpa using hj)
      change t.tactic j = s.tactic j at heq
      simpa only [truncateState, hj, ite_true] using heq
    · simp only [truncateState, hj, ite_false]

theorem value_eq_of_agrees {n : ℕ} (s t : ChainState n) (cut : ℕ)
    (h : ProductFiltering.Agrees (readCoords cut) (toCoords s) (toCoords t))
    (j : ℕ) (hj : j ≤ cut) : value t j = value s j := by
  by_cases h0 : j = 0
  · simp [h0]
  by_cases hint : j - 1 < n - 1
  · let k : Fin (n - 1) := ⟨j - 1, hint⟩
    have hread : Sum.inl k ∈ readCoords cut := by simp; dsimp [k]; omega
    have heq := h (.inl k) hread
    change t.values k = s.values k at heq
    simpa [value, h0, hint, k] using heq
  · simp [value, h0, hint]

theorem passes_eq_of_agrees {n : ℕ} (s t : ChainState n) (cut : ℕ)
    (h : ProductFiltering.Agrees (readCoords cut) (toCoords s) (toCoords t))
    (j : Fin n) (hj : j.val < cut) : passes t j = passes s j := by
  have hleft := value_eq_of_agrees s t cut h j.val (by omega)
  have hright := value_eq_of_agrees s t cut h (j.val + 1) (by omega)
  have hprofile := h (.inr j) (by simpa using hj)
  change t.tactic j = s.tactic j at hprofile
  simpa only [passes, hleft, hright, toCoords] using
    congrArg (fun r => MTChainProof.bridgePass (value s j.val) (value s (j.val + 1)) r) hprofile

theorem firstFailure_eq_of_agrees {n : ℕ} (s t : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) (cut : ℕ) (hcut : i.val + 1 ≤ cut)
    (h : ProductFiltering.Agrees (readCoords cut) (toCoords s) (toCoords t)) :
    firstFailure t = some i := by
  apply firstFailure_of_failed_prefix t i
  · rw [passes_eq_of_agrees s t cut h i (by omega)]
    exact selected_failed s i hi
  · intro j hj
    rw [passes_eq_of_agrees s t cut h j (by omega)]
    exact selected_prefix s i hi j hj

theorem firstFailure_truncate {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) :
    firstFailure (truncateState s (i.val + 1)) = some i :=
  firstFailure_eq_of_agrees s (truncateState s (i.val + 1)) i hi _ le_rfl
    (agrees_truncate s _)

abbrev PrefixDatum (n : ℕ) := Fin n × ChainState n

noncomputable def observeRaw {n : ℕ} (s : ChainState n) : Option (PrefixDatum n) :=
  match firstFailure s with
  | none => none
  | some i => some (i, truncateState s (i.val + 1))

def ValidDatum {n : ℕ} (q : PrefixDatum n) : Prop :=
  firstFailure q.2 = some q.1 ∧ truncateState q.2 (q.1.val + 1) = q.2

theorem observeRaw_fiber {n : ℕ} (q : PrefixDatum n) (hq : ValidDatum q)
    (s : ChainState n) :
    observeRaw s = some q ↔
      ProductFiltering.Agrees (readCoords (q.1.val + 1)) (toCoords q.2) (toCoords s) := by
  constructor
  · intro hobs
    cases hs : firstFailure s with
    | none => simp [observeRaw, hs] at hobs
    | some i =>
      have heq : (i, truncateState s (i.val + 1)) = q := by
        exact Option.some.inj (by simpa [observeRaw, hs] using hobs)
      have hindex : i = q.1 := congrArg Prod.fst heq
      have hstate : truncateState s (q.1.val + 1) = q.2 := by
        simpa [hindex] using congrArg Prod.snd heq
      intro c hc
      have hretain := agrees_truncate s (q.1.val + 1) c hc
      rw [hstate] at hretain
      exact hretain.symm
  · intro hagree
    have hfirst := firstFailure_eq_of_agrees q.2 s q.1 hq.1
      (q.1.val + 1) le_rfl hagree
    have hstate := truncateState_eq_of_agrees q.2 s (q.1.val + 1) hagree
    rw [hq.2] at hstate
    simp [observeRaw, hfirst, hstate]

theorem observeRaw_valid {n : ℕ} (s : ChainState n) (q : PrefixDatum n)
    (hobs : observeRaw s = some q) : ValidDatum q := by
  cases hs : firstFailure s with
  | none => simp [observeRaw, hs] at hobs
  | some i =>
    have heq : (i, truncateState s (i.val + 1)) = q :=
      Option.some.inj (by simpa [observeRaw, hs] using hobs)
    subst q
    exact ⟨firstFailure_truncate s i hs, truncateState_idempotent s _⟩

noncomputable def freshWeight {n : ℕ} : ∀ c : Coord n, Alphabet c → ℝ
  | .inl _ => fun _ => 1 / 3
  | .inr _ => fun _ => 1 / 4

theorem freshWeight_sum {n : ℕ} (c : Coord n) : ∑ x, freshWeight c x = 1 := by
  cases c with
  | inl j => change (∑ _ : Fin 3, (1 / 3 : ℝ)) = 1; norm_num
  | inr j => change (∑ _ : Fin 4, (1 / 4 : ℝ)) = 1; norm_num

theorem freshWeight_nonneg {n : ℕ} (c : Coord n) (x : Alphabet c) :
    0 ≤ freshWeight c x := by
  cases c <;> norm_num [freshWeight]

theorem freshWeight_uniform {n : ℕ} (c : Coord n) (x : Alphabet c) :
    freshWeight c x = 1 / (Fintype.card (Alphabet c) : ℝ) := by
  cases c with
  | inl j => change (1 / 3 : ℝ) = 1 / (Fintype.card (Fin 3) : ℝ); norm_num
  | inr j => change (1 / 4 : ℝ) = 1 / (Fintype.card (Fin 4) : ℝ); norm_num

noncomputable def rawInitialDensity {n : ℕ} (s : ChainState n) : ℝ :=
  ProductFiltering.density freshWeight (toCoords s)

theorem rawInitialDensity_uniform {n : ℕ} (s : ChainState n) :
    rawInitialDensity s = 1 / (Fintype.card (ChainState n) : ℝ) := by
  unfold rawInitialDensity ProductFiltering.density
  simp_rw [freshWeight_uniform, one_div]
  rw [Finset.prod_inv_distrib]
  congr 1
  rw [Fintype.card_congr (coordinateEquiv n), Fintype.card_pi, Nat.cast_prod]

noncomputable def rawCompletion {n : ℕ} (q : PrefixDatum n) (s : ChainState n) : ℝ :=
  ProductFiltering.completion freshWeight (readCoords (q.1.val + 1))
    (toCoords q.2) (toCoords s)

theorem rawCompletion_sum {n : ℕ} (q : PrefixDatum n) :
    ∑ s, rawCompletion q s = 1 := by
  classical
  calc
    _ = ∑ x, ProductFiltering.completion freshWeight (readCoords (q.1.val + 1))
        (toCoords q.2) x := (coordinateEquiv n).sum_comp _
    _ = 1 := ProductFiltering.completion_sum _ _ _ freshWeight_sum

theorem rawCompletion_nonneg {n : ℕ} (q : PrefixDatum n) (s : ChainState n) :
    0 ≤ rawCompletion q s :=
  ProductFiltering.completion_nonneg _ _ _ _ freshWeight_nonneg

theorem rawCompletion_support {n : ℕ} (q : PrefixDatum n) (hq : ValidDatum q)
    (s : ChainState n) (hs : rawCompletion q s ≠ 0) : observeRaw s = some q := by
  apply (observeRaw_fiber q hq s).mpr
  by_contra h
  exact hs (ProductFiltering.completion_zero_of_not_agrees _ _ _ _ h)

noncomputable def initialPrefixMass {n : ℕ} (q : PrefixDatum n) : ℝ :=
  ProductFiltering.prefixMass freshWeight (readCoords (q.1.val + 1)) (toCoords q.2)

theorem initial_cylinder_factor {n : ℕ} (q : PrefixDatum n) (hq : ValidDatum q)
    (s : ChainState n) :
    (if observeRaw s = some q then rawInitialDensity s else 0) =
      initialPrefixMass q * rawCompletion q s := by
  classical
  have hfiber (x : ∀ c : Coord n, Alphabet c) :
      observeRaw (fromCoords x) = some q ↔
        ProductFiltering.Agrees (readCoords (q.1.val + 1)) (toCoords q.2) x := by
    simpa using observeRaw_fiber q hq (fromCoords x)
  simpa [rawInitialDensity, initialPrefixMass, rawCompletion] using
    ProductFiltering.observation_factor (fun x => observeRaw (fromCoords x)) (some q)
      freshWeight (readCoords (q.1.val + 1)) (toCoords q.2) (toCoords s) hfiber

theorem initial_observation_mass {n : ℕ} (q : PrefixDatum n) (hq : ValidDatum q) :
    (∑ s, if observeRaw s = some q then rawInitialDensity s else 0) =
      initialPrefixMass q := by
  classical
  simp_rw [initial_cylinder_factor q hq]
  rw [← Finset.mul_sum, rawCompletion_sum, mul_one]

noncomputable def refreshCoords {n : ℕ} (i : Fin n) : Finset (Coord n) := by
  classical
  exact Finset.univ.filter (fun c => match c with
    | .inl j => j.val + 1 = i.val ∨ j.val + 1 = i.val + 1
    | .inr j => j = i)

noncomputable def sourceWeight {n : ℕ} (q : PrefixDatum n)
    (c : Coord n) (x : Alphabet c) : ℝ :=
  if c ∈ readCoords (q.1.val + 1) then (if x = toCoords q.2 c then 1 else 0)
  else freshWeight c x

noncomputable def postWeight {n : ℕ} (q : PrefixDatum n)
    (c : Coord n) (x : Alphabet c) : ℝ :=
  if c ∈ refreshCoords q.1 then freshWeight c x else sourceWeight q c x

theorem postWeight_unread {n : ℕ} (q : PrefixDatum n) (j : Fin n)
    (hcut : q.1.val ≤ j.val + 1) (c : Coord n)
    (hc : c ∉ readCoords (j.val + 1)) (x : Alphabet c) :
    postWeight q c x = freshWeight c x := by
  classical
  unfold postWeight sourceWeight
  by_cases hrefresh : c ∈ refreshCoords q.1
  · simp [hrefresh]
  · have hnotread : c ∉ readCoords (q.1.val + 1) := by
      cases c with
      | inl k =>
        simp only [mem_readCoords_left, not_le] at hc ⊢
        simp only [refreshCoords, Finset.mem_filter, Finset.mem_univ, true_and,
          not_or] at hrefresh
        omega
      | inr k =>
        simp only [mem_readCoords_right, not_lt] at hc ⊢
        simp only [refreshCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hrefresh
        have hne : k.val ≠ q.1.val := by
          intro heq
          exact hrefresh (Fin.ext heq)
        omega
    simp [hrefresh, hnotread]

theorem sourceWeight_sum {n : ℕ} (q : PrefixDatum n) (c : Coord n) :
    ∑ x, sourceWeight q c x = 1 := by
  classical
  by_cases hc : c ∈ readCoords (q.1.val + 1)
  · simp [sourceWeight, hc]
  · simpa [sourceWeight, hc] using freshWeight_sum c

theorem postWeight_sum {n : ℕ} (q : PrefixDatum n) (c : Coord n) :
    ∑ x, postWeight q c x = 1 := by
  classical
  by_cases hc : c ∈ refreshCoords q.1
  · simpa [postWeight, hc] using freshWeight_sum c
  · simpa [postWeight, hc] using sourceWeight_sum q c

theorem sourceWeight_nonneg {n : ℕ} (q : PrefixDatum n) (c : Coord n) (x : Alphabet c) :
    0 ≤ sourceWeight q c x := by
  classical
  unfold sourceWeight
  split_ifs
  · norm_num
  · norm_num
  · exact freshWeight_nonneg c x

theorem postWeight_nonneg {n : ℕ} (q : PrefixDatum n) (c : Coord n) (x : Alphabet c) :
    0 ≤ postWeight q c x := by
  classical
  unfold postWeight
  split_ifs
  · exact freshWeight_nonneg c x
  · exact sourceWeight_nonneg q c x

theorem postDensity_prefix {n : ℕ} (q : PrefixDatum n) (s : ChainState n)
    (hs : ProductFiltering.density (postWeight q) (toCoords s) ≠ 0) :
    ProductFiltering.Agrees (readCoords (q.1.val - 1)) (toCoords q.2) (toCoords s) := by
  classical
  intro c hc
  have hread : c ∈ readCoords (q.1.val + 1) := by
    cases c with
    | inl k => simp only [mem_readCoords_left] at hc ⊢; omega
    | inr k => simp only [mem_readCoords_right] at hc ⊢; omega
  have hnotrefresh : c ∉ refreshCoords q.1 := by
    cases c with
    | inl k =>
      simp only [mem_readCoords_left] at hc
      simp only [refreshCoords, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
      omega
    | inr k =>
      simp only [mem_readCoords_right] at hc
      simp only [refreshCoords, Finset.mem_filter, Finset.mem_univ, true_and]
      intro heq
      have : k.val = q.1.val := congrArg Fin.val heq
      omega
  have hfactor : postWeight q c (toCoords s c) ≠ 0 := by
    intro hz
    apply hs
    exact Finset.prod_eq_zero (Finset.mem_univ c) hz
  by_contra hne
  simp [postWeight, sourceWeight, hread, hnotrefresh, hne] at hfactor

theorem postDensity_cut_lower_bound {n : ℕ} (q : PrefixDatum n) (hq : ValidDatum q)
    (s : ChainState n) (j : Fin n)
    (hs : ProductFiltering.density (postWeight q) (toCoords s) ≠ 0)
    (hj : firstFailure s = some j) : q.1.val ≤ j.val + 1 := by
  by_contra hlt
  have hagree := postDensity_prefix q s hs
  have hpass : passes s j = true := by
    rw [passes_eq_of_agrees q.2 s (q.1.val - 1) hagree j (by omega)]
    exact selected_prefix q.2 q.1 hq.1 j (by omega)
  have hfail := selected_failed s j hj
  simp [hpass] at hfail

noncomputable def postPrefixMass {n : ℕ} (q p : PrefixDatum n) : ℝ :=
  ProductFiltering.prefixMass (postWeight q) (readCoords (p.1.val + 1)) (toCoords p.2)

theorem post_same_weight_factor {n : ℕ} (q p : PrefixDatum n) (hp : ValidDatum p)
    (s : ChainState n) :
    (if observeRaw s = some p then ProductFiltering.density (postWeight q) (toCoords s) else 0) =
      postPrefixMass q p * ProductFiltering.completion (postWeight q)
        (readCoords (p.1.val + 1)) (toCoords p.2) (toCoords s) := by
  classical
  have hfiber (x : ∀ c : Coord n, Alphabet c) :
      observeRaw (fromCoords x) = some p ↔
        ProductFiltering.Agrees (readCoords (p.1.val + 1)) (toCoords p.2) x := by
    simpa using observeRaw_fiber p hp (fromCoords x)
  simpa [postPrefixMass] using ProductFiltering.observation_factor
    (fun x => observeRaw (fromCoords x)) (some p) (postWeight q)
    (readCoords (p.1.val + 1)) (toCoords p.2) (toCoords s) hfiber

theorem post_observation_mass {n : ℕ} (q p : PrefixDatum n) (hp : ValidDatum p) :
    (∑ s, if observeRaw s = some p then
      ProductFiltering.density (postWeight q) (toCoords s) else 0) = postPrefixMass q p := by
  classical
  simp_rw [post_same_weight_factor q p hp]
  rw [← Finset.mul_sum]
  have hnorm :
      (∑ s, ProductFiltering.completion (postWeight q) (readCoords (p.1.val + 1))
        (toCoords p.2) (toCoords s)) = 1 := by
    calc
      _ = ∑ x, ProductFiltering.completion (postWeight q) (readCoords (p.1.val + 1))
          (toCoords p.2) x := (coordinateEquiv n).sum_comp _
      _ = 1 := ProductFiltering.completion_sum _ _ _ (postWeight_sum q)
  rw [hnorm, mul_one]

theorem postPrefixMass_cut_lower_bound {n : ℕ} (q p : PrefixDatum n)
    (hq : ValidDatum q) (hp : ValidDatum p) (hm : postPrefixMass q p ≠ 0) :
    q.1.val ≤ p.1.val + 1 := by
  classical
  rw [← post_observation_mass q p hp] at hm
  obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  by_cases hobs : observeRaw s = some p
  · have hsne : ProductFiltering.density (postWeight q) (toCoords s) ≠ 0 := by
      simpa [hobs] using hs
    have hagree := (observeRaw_fiber p hp s).mp hobs
    have hfirst := firstFailure_eq_of_agrees p.2 s p.1 hp.1 _ le_rfl hagree
    exact postDensity_cut_lower_bound q hq s p.1 hsne hfirst
  · simp [hobs] at hs

theorem post_observation_factor {n : ℕ} (q p : PrefixDatum n)
    (hq : ValidDatum q) (hp : ValidDatum p) (s : ChainState n) :
    (if observeRaw s = some p then ProductFiltering.density (postWeight q) (toCoords s) else 0) =
      postPrefixMass q p * rawCompletion p s := by
  classical
  rw [post_same_weight_factor q p hp]
  by_cases hm : postPrefixMass q p = 0
  · simp [hm]
  · congr 1
    have hcut := postPrefixMass_cut_lower_bound q p hq hp hm
    exact ProductFiltering.completion_congr_unread (postWeight q) freshWeight
      (readCoords (p.1.val + 1)) (toCoords p.2) (toCoords s)
      (fun c hc x => postWeight_unread q p.1 hcut c hc x)

end Filtering
end MTChainFormal
