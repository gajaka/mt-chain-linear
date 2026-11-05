module

public import Filtering
public import ActualScan

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal.TailLaw

open scoped BigOperators
open Filtering ProductFiltering TailScan ActualScan

/-- Full states agreeing with the retained cylinder. -/
abbrev Cylinder {n : ℕ} (q : PrefixDatum n) :=
  {s : ChainState n // Agrees (readCoords (q.1.val + 1)) (toCoords q.2) (toCoords s)}

noncomputable def splice {n : ℕ} (q : PrefixDatum n) (m : ℕ)
    (h : q.1.val + 1 + m + 1 = n) (w : Word m) (last : Fin 4) : ChainState n where
  values j := if hj : j.val + 1 ≤ q.1.val + 1 then q.2.values j
    else (w ⟨j.val - (q.1.val + 1), by omega⟩).1
  tactic j := if hj : j.val < q.1.val + 1 then q.2.tactic j
    else if he : j.val < n - 1 then (w ⟨j.val - (q.1.val + 1), by omega⟩).2 else last

theorem splice_agrees {n : ℕ} (q : PrefixDatum n) (m : ℕ)
    (h : q.1.val + 1 + m + 1 = n) (w : Word m) (last : Fin 4) :
    Agrees (readCoords (q.1.val + 1)) (toCoords q.2) (toCoords (splice q m h w last)) := by
  intro c hc
  cases c with
  | inl j =>
      have hj := (mem_readCoords_left _ _).mp hc
      simp only [toCoords, splice, dite_eq_left hj]
      rfl
  | inr j =>
      have hj := (mem_readCoords_right _ _).mp hc
      simp only [toCoords, splice, dite_eq_left hj]
      rfl

theorem lettersFrom_splice {n : ℕ} (q : PrefixDatum n) (m : ℕ)
    (h : q.1.val + 1 + m + 1 = n) (w : Word m) (last : Fin 4) :
    lettersFrom (splice q m h w last) (q.1.val + 1) m h = w := by
  funext j
  have hjv : q.1.val + 1 + j.val < n - 1 := by omega
  have hjn : q.1.val + 1 + j.val + 1 < n := by omega
  have hindex : q.1.val + 1 + j.val - (q.1.val + 1) = j.val := by omega
  have hv := value_internal (splice q m h w last)
    (⟨q.1.val + 1 + j.val, hjv⟩ : Fin (n - 1))
  change (value (splice q m h w last) (q.1.val + 1 + j.val + 1),
    (splice q m h w last).tactic ⟨q.1.val + 1 + j.val, by omega⟩) = w j
  rw [hv]
  simp only [splice, show ¬ (q.1.val + 1 + j.val + 1 ≤ q.1.val + 1) by omega,
    show ¬ (q.1.val + 1 + j.val < q.1.val + 1) by omega, hjv,
    dite_false, dite_true, hindex]

theorem lastTactic_splice {n : ℕ} (q : PrefixDatum n) (m : ℕ)
    (h : q.1.val + 1 + m + 1 = n) (w : Word m) (last : Fin 4) :
    lastTactic (splice q m h w last) (by omega) = last := by
  simp only [lastTactic, splice, dite_eq_right (show ¬ (n - 1 < q.1.val + 1) by omega),
    dite_eq_right (lt_irrefl (n - 1))]

theorem splice_extract {n : ℕ} (q : PrefixDatum n) (m : ℕ)
    (h : q.1.val + 1 + m + 1 = n) (s : Cylinder q) :
    splice q m h (lettersFrom s.val (q.1.val + 1) m h)
      (lastTactic s.val (by omega)) = s.val := by
  apply chainState_ext
  · funext j
    by_cases hj : j.val + 1 ≤ q.1.val + 1
    · have heq := s.property (.inl j) (by simpa using hj)
      change s.val.values j = q.2.values j at heq
      simpa only [splice, dite_eq_left hj, toCoords] using heq.symm
    · have hind : q.1.val + 1 + (j.val - (q.1.val + 1)) = j.val := by omega
      have hindex : (⟨q.1.val + 1 + (j.val - (q.1.val + 1)), by omega⟩ :
          Fin (n - 1)) = j := Fin.ext hind
      simp only [splice, hj, dite_false, lettersFrom]
      have hv := value_internal s.val j
      simpa only [hind] using hv
  · funext j
    by_cases hj : j.val < q.1.val + 1
    · have heq := s.property (.inr j) (by simpa using hj)
      change s.val.tactic j = q.2.tactic j at heq
      simpa only [splice, dite_eq_left hj, toCoords] using heq.symm
    · by_cases he : j.val < n - 1
      · have hind : q.1.val + 1 + (j.val - (q.1.val + 1)) = j.val := by omega
        have hindex : (⟨q.1.val + 1 + (j.val - (q.1.val + 1)), by omega⟩ : Fin n) = j :=
          Fin.ext hind
        simp only [splice, hj, he, dite_false, dite_true, lettersFrom, hindex]
      · have hind : n - 1 = j.val := by omega
        have hindex : (⟨n - 1, by omega⟩ : Fin n) = j := Fin.ext hind
        simp only [splice, dite_eq_right hj, dite_eq_right he, lastTactic, hindex]

noncomputable def suffixEquiv {n : ℕ} (q : PrefixDatum n) (m : ℕ)
    (h : q.1.val + 1 + m + 1 = n) : Cylinder q ≃ Word m × Fin 4 where
  toFun s := (lettersFrom s.val (q.1.val + 1) m h, lastTactic s.val (by omega))
  invFun x := ⟨splice q m h x.1 x.2, splice_agrees q m h x.1 x.2⟩
  left_inv s := Subtype.ext (splice_extract q m h s)
  right_inv x := Prod.ext (lettersFrom_splice q m h x.1 x.2) (lastTactic_splice q m h x.1 x.2)

theorem sum_cylinder {n : ℕ} (q : PrefixDatum n) (f : ChainState n → ℝ) :
    (∑ s : Cylinder q, f s.val) = ∑ s, if Agrees
      (readCoords (q.1.val + 1)) (toCoords q.2) (toCoords s) then f s else 0 := by
  classical
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun s => Agrees (readCoords (q.1.val + 1)) (toCoords q.2) (toCoords s)))
    (by simp)]
  exact Finset.sum_filter _ _

theorem rawCompletion_eq_on {n : ℕ} (q : PrefixDatum n) (s t : Cylinder q) :
    rawCompletion q s.val = rawCompletion q t.val := by
  classical
  unfold rawCompletion completion
  apply Finset.prod_congr rfl
  intro c _
  by_cases hc : c ∈ readCoords (q.1.val + 1)
  · simp [hc, s.property c hc, t.property c hc]
  · cases c <;> simp [hc, freshWeight]

theorem rawCompletion_on_cylinder {n : ℕ} (q : PrefixDatum n) (s : Cylinder q) :
    rawCompletion q s.val = 1 / (Fintype.card (Cylinder q) : ℝ) := by
  classical
  have hsum : (Fintype.card (Cylinder q) : ℝ) * rawCompletion q s.val = 1 := by
    calc
      _ = ∑ t : Cylinder q, rawCompletion q t.val := by
        simp_rw [rawCompletion_eq_on q _ s]
        simp
      _ = ∑ t, rawCompletion q t := by
        rw [sum_cylinder]
        apply Finset.sum_congr rfl
        intro t _
        by_cases ht : Agrees (readCoords (q.1.val + 1)) (toCoords q.2) (toCoords t)
        · simp [ht]
        · simp [ht, rawCompletion,
            completion_zero_of_not_agrees freshWeight _ _ _ ht]
      _ = 1 := rawCompletion_sum q
  have hcard : (Fintype.card (Cylinder q) : ℝ) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hsum
    norm_num at hsum
  apply (eq_div_iff hcard).mpr
  nlinarith [hsum]

theorem completion_expectation {n : ℕ} (q : PrefixDatum n) (f : ChainState n → ℝ) :
    (∑ s, rawCompletion q s * f s) =
      (∑ s : Cylinder q, f s.val) / (Fintype.card (Cylinder q) : ℝ) := by
  classical
  rw [sum_cylinder, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : Agrees (readCoords (q.1.val + 1)) (toCoords q.2) (toCoords s)
  · rw [ite_eq_left hs, (rawCompletion_on_cylinder q ⟨s, hs⟩)]
    ring
  · simp only [ite_eq_right hs, zero_div]
    rw [rawCompletion, completion_zero_of_not_agrees _ _ _ _ hs, zero_mul]

theorem completion_tail_average {n : ℕ} (q : PrefixDatum n) (m : ℕ)
    (h : q.1.val + 1 + m + 1 = n) (f : Word m → Fin 4 → ℝ) :
    (∑ s, rawCompletion q s *
      f (lettersFrom s (q.1.val + 1) m h) (lastTactic s (by omega))) = average m f := by
  classical
  rw [completion_expectation]
  have hsum : (∑ s : Cylinder q,
      f (lettersFrom s.val (q.1.val + 1) m h) (lastTactic s.val (by omega))) =
      ∑ w : Word m, ∑ last : Fin 4, f w last := by
    calc
      _ = ∑ x : Word m × Fin 4, f x.1 x.2 := (suffixEquiv q m h).sum_comp _
      _ = _ := Fintype.sum_prod_type _
  rw [hsum, Fintype.card_congr (suffixEquiv q m h)]
  simp [average, Fintype.card_prod]

theorem lettersFrom_replace {n : ℕ} (s : ChainState n) (i : Fin n) (u : Draw)
    (m : ℕ) (h : i.val + 1 + m + 1 = n) :
    lettersFrom (replace s i u) (i.val + 1) m h =
      lettersFrom s (i.val + 1) m h := by
  funext j
  apply Prod.ext
  · have hi : 2 ≤ n := by omega
    change value (replace s i u) (i.val + 1 + j.val + 1) = _
    rw [replace_value hi s i u _ (by omega)]
    simp only [show ¬(i.val + 1 + j.val + 1 = 0) by omega,
      show ¬(i.val + 1 + j.val + 1 = n) by omega,
      show ¬(i.val + 1 + j.val + 1 = i.val) by omega,
      show ¬(i.val + 1 + j.val + 1 = i.val + 1) by omega,
      ite_false]
    rfl
  · exact replace_tactic_other s i ⟨i.val + 1 + j.val, by omega⟩ u
      (by
        intro he
        have hv := congrArg Fin.val he
        change i.val + 1 + j.val = i.val at hv
        omega)

theorem lastTactic_replace {n : ℕ} (s : ChainState n) (i : Fin n) (u : Draw)
    (m : ℕ) (h : i.val + 1 + m + 1 = n) :
    lastTactic (replace s i u) (by omega) = lastTactic s (by omega) := by
  unfold lastTactic
  exact replace_tactic_other s i ⟨n - 1, by omega⟩ u
    (by
      intro he
      have hv := congrArg Fin.val he
      change n - 1 = i.val at hv
      omega)

end MTChainFormal.TailLaw
