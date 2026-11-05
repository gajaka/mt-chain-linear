import NeighborBase

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace NeighborSeparation

open MTChainFormal
open scoped BigOperators

def pathScore (h : EdgeCosts) (len : ℕ) (x : ℕ → Fin 3) (r : ℕ → Fin 4) : ℝ :=
  ∑ i ∈ Finset.range len, h i (x i) (x (i + 1)) (r i)

theorem pathScore_succ (h : EdgeCosts) (len : ℕ) (x : ℕ → Fin 3) (r : ℕ → Fin 4) :
    pathScore h (len + 1) x r = pathScore h len x r + h len (x len) (x (len + 1)) (r len) := by
  exact Finset.sum_range_succ _ _

/-- Minimum first-edge cost, then finite prefix minima. Every endpoint is
reachable; no infinite or unsupported boundary values are introduced. -/
noncomputable def prefixMin (h : EdgeCosts) : ℕ → Fin 3 → ℝ
  | 0, y => PotentialSeparation.low (fun r : Fin 4 => h 0 2 y r)
  | m + 1, y => PotentialSeparation.low (fun z : Fin 3 × Fin 4 =>
      prefixMin h m z.1 + h (m + 1) z.1 y z.2)

noncomputable def gauge (h : EdgeCosts) (m : ℕ) : EdgeCosts
  | 0, a, b, r => if a = 2 then h 0 2 b r - prefixMin h 0 b else 0
  | i + 1, a, b, r => if i + 1 ≤ m then
      h (i + 1) a b r + prefixMin h i a - prefixMin h (i + 1) b else 0

theorem gauge_nonnegative (h : EdgeCosts) (m : ℕ) : Nonnegative (gauge h m) := by
  intro i a b r
  cases i with
  | zero =>
    dsimp [gauge]
    split_ifs
    · exact sub_nonneg.mpr (PotentialSeparation.low_le (fun r : Fin 4 => h 0 2 b r) r)
    · exact le_rfl
  | succ i =>
    dsimp [gauge]
    split_ifs
    · have hmin := PotentialSeparation.low_le
        (fun z : Fin 3 × Fin 4 => prefixMin h i z.1 + h (i + 1) z.1 b z.2) (a,r)
      change 0 ≤ h (i + 1) a b r + prefixMin h i a -
        PotentialSeparation.low (fun z : Fin 3 × Fin 4 =>
          prefixMin h i z.1 + h (i + 1) z.1 b z.2)
      linarith
    · exact le_rfl

theorem pathScore_gauge (h : EdgeCosts) (m : ℕ) (x : ℕ → Fin 3)
    (r : ℕ → Fin 4) (hx : x 0 = 2) :
    ∀ k : ℕ, k ≤ m → pathScore (gauge h m) (k + 1) x r =
      pathScore h (k + 1) x r - prefixMin h k (x (k + 1)) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [pathScore, gauge, hx]
  | succ k ih =>
    intro hk
    have hi := ih (by omega)
    rw [pathScore_succ (gauge h m) (k + 1), hi,
      pathScore_succ h (k + 1)]
    simp only [gauge, hk, ↓reduceIte]
    ring

theorem prefixMin_attained (h : EdgeCosts) :
    ∀ (m : ℕ) (y : Fin 3), ∃ x : ℕ → Fin 3, ∃ r : ℕ → Fin 4,
      x 0 = 2 ∧ x (m + 1) = y ∧ pathScore h (m + 1) x r = prefixMin h m y := by
  intro m
  induction m with
  | zero =>
    intro y
    let a : Fin 4 := PotentialSeparation.lowArg (fun r : Fin 4 => h 0 2 y r)
    refine ⟨(fun j => if j = 0 then 2 else y), (fun _ => a), ?_, ?_, ?_⟩
    · simp
    · simp
    · simpa [pathScore, prefixMin, a] using
        PotentialSeparation.lowArg_value (fun r : Fin 4 => h 0 2 y r)
  | succ m ih =>
    intro y
    let z : Fin 3 × Fin 4 := PotentialSeparation.lowArg
      (fun z : Fin 3 × Fin 4 => prefixMin h m z.1 + h (m + 1) z.1 y z.2)
    obtain ⟨x,r,hx0,hxm,hsum⟩ := ih z.1
    let xx := Function.update x (m + 2) y
    let rr := Function.update r (m + 1) z.2
    refine ⟨xx,rr,?_,?_,?_⟩
    · simpa [xx] using hx0
    · simp [xx, Nat.add_assoc]
    · have hprefix : pathScore h (m + 1) xx rr = pathScore h (m + 1) x r := by
        apply Finset.sum_congr rfl
        intro i hi
        have hilt := Finset.mem_range.mp hi
        have hix : i ≠ m + 2 := by omega
        have hix1 : i + 1 ≠ m + 2 := by omega
        have hir : i ≠ m + 1 := by omega
        simp [xx,rr,hix,hir]
      have hlast : h (m + 1) (xx (m + 1)) (xx (m + 2)) (rr (m + 1)) =
          h (m + 1) z.1 y z.2 := by
        simp [xx,rr,hxm]
      have hz := PotentialSeparation.lowArg_value
        (fun z : Fin 3 × Fin 4 => prefixMin h m z.1 + h (m + 1) z.1 y z.2)
      change prefixMin h m z.1 + h (m + 1) z.1 y z.2 = prefixMin h (m + 1) y at hz
      change pathScore h (m + 2) xx rr = _
      rw [pathScore, Finset.sum_range_succ, ← pathScore, hprefix, hsum, hlast]
      exact hz

/-- Extend the finite tactic vector only to state a natural-index path sum. -/
def tacticAt {n : ℕ} (s : ChainState n) (i : ℕ) : Fin 4 :=
  if hi : i < n then s.tactic ⟨i,hi⟩ else 0

theorem rawScore_pathScore {n : ℕ} (c : ℝ) (h : EdgeCosts) (s : ChainState n) :
    rawScore c h s = c + pathScore h n (value s) (tacticAt s) := by
  unfold rawScore pathScore
  congr 1
  have hfin : (∑ i : Fin n, h i.val (value s i.val) (value s (i.val + 1)) (s.tactic i)) =
      ∑ i : Fin n, h i.val (value s i.val) (value s (i.val + 1)) (tacticAt s i.val) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [tacticAt, i.isLt]
  rw [hfin]
  exact Fin.sum_univ_eq_sum_range (fun i => h i (value s i) (value s (i + 1)) (tacticAt s i)) n

theorem remote_tacticAt_last {n : ℕ} (_hn : 0 < n) (s : ChainState n)
    (hs : Remote s) : tacticAt s (n - 1) = 1 := by
  obtain ⟨_,i,hi,hr⟩ := hs
  have hit : n - 1 < n := by omega
  have heq : (⟨n - 1, hit⟩ : Fin n) = i := Fin.ext hi.symm
  simpa [tacticAt, hit, heq] using hr

theorem remote_score_split (m : ℕ) (c : ℝ) (h : EdgeCosts)
    (s : ChainState (m + 2)) (hs : Remote s) :
    rawScore c h s = c + pathScore h (m + 1) (value s) (tacticAt s) +
      h (m + 1) 1 0 1 := by
  rw [rawScore_pathScore, pathScore, Finset.sum_range_succ, ← pathScore]
  have hx : value s (m + 1) = 1 := by simpa using hs.1
  have hr : tacticAt s (m + 1) = 1 := by
    simpa using remote_tacticAt_last (by omega : 0 < m + 2) s hs
  rw [hx, hr, value_right (by omega : 0 < m + 2)]
  ring

theorem gauge_score_identity (m : ℕ) (c : ℝ) (h : EdgeCosts)
    (s : ChainState (m + 2)) (hs : Remote s) :
    rawScore c h s =
      rawScore (c + h (m + 1) 1 0 1 + prefixMin h m 1) (gauge h m) s := by
  rw [remote_score_split m c h s hs, rawScore_pathScore]
  have htail : gauge h m (m + 1) (value s (m + 1)) (value s (m + 2))
      (tacticAt s (m + 1)) = 0 := by
    cases m <;> simp [gauge]
  rw [pathScore_succ (gauge h m) (m + 1), htail, add_zero]
  rw [pathScore_gauge h m (value s) (tacticAt s) (value_zero s) m le_rfl]
  have hx : value s (m + 1) = 1 := by simpa using hs.1
  rw [hx]
  ring

/-- Realize an attained finite path as an actual original-chain raw state.
Only the fixed final weak label is imposed beyond the path. -/
def realizePath (m : ℕ) (x : ℕ → Fin 3) (r : ℕ → Fin 4) : ChainState (m + 2) where
  values j := x (j.val + 1)
  tactic i := if i.val = m + 1 then 1 else r i.val

theorem realizePath_value (m : ℕ) (x : ℕ → Fin 3) (r : ℕ → Fin 4)
    (hx0 : x 0 = 2) (j : ℕ) (hj : j ≤ m + 1) :
    value (realizePath m x r) j = x j := by
  by_cases hj0 : j = 0
  · simp [hj0,hx0]
  · have hjlt : j - 1 < m + 1 := by omega
    have hjadd : j - 1 + 1 = j := by omega
    simp [value,hj0,hjlt,realizePath,hjadd]

theorem realizePath_tactic (m : ℕ) (x : ℕ → Fin 3) (r : ℕ → Fin 4)
    (j : ℕ) (hj : j < m + 1) : tacticAt (realizePath m x r) j = r j := by
  have hne : j ≠ m + 1 := by omega
  have hlt : j < m + 2 := by omega
  simp [tacticAt,hlt,realizePath,hne]

theorem realizePath_remote (m : ℕ) (x : ℕ → Fin 3) (r : ℕ → Fin 4)
    (hx0 : x 0 = 2) (hxlast : x (m + 1) = 1) : Remote (realizePath m x r) := by
  constructor
  · change value (realizePath m x r) (m + 1) = 1
    rw [realizePath_value m x r hx0 (m + 1) le_rfl, hxlast]
  · refine ⟨Fin.last (m + 1), ?_, ?_⟩
    · simp
    · simp [realizePath]

theorem realizePath_score (m : ℕ) (c : ℝ) (h : EdgeCosts)
    (x : ℕ → Fin 3) (r : ℕ → Fin 4)
    (hx0 : x 0 = 2) (hxlast : x (m + 1) = 1) :
    rawScore c h (realizePath m x r) =
      c + pathScore h (m + 1) x r + h (m + 1) 1 0 1 := by
  rw [remote_score_split m c h _ (realizePath_remote m x r hx0 hxlast)]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  have hil := Finset.mem_range.mp hi
  rw [realizePath_value m x r hx0 i (by omega),
    realizePath_value m x r hx0 (i + 1) (by omega), realizePath_tactic m x r i hil]

theorem gauge_constant_nonnegative (m : ℕ) (c : ℝ) (h : EdgeCosts)
    (h_nonneg_remote : ∀ s : ChainState (m + 2), Remote s → 0 ≤ rawScore c h s) :
    0 ≤ c + h (m + 1) 1 0 1 + prefixMin h m 1 := by
  obtain ⟨x,r,hx0,hxlast,hcost⟩ := prefixMin_attained h m 1
  have hs := h_nonneg_remote (realizePath m x r) (realizePath_remote m x r hx0 hxlast)
  rw [realizePath_score m c h x r hx0 hxlast, hcost] at hs
  linarith

/-- Genuine finite min-plus attainment supplies a nonnegative offset and
globally nonnegative bridge tables on the original remote-failure cylinder. -/
theorem gauge_exists {n : ℕ} (hn : 2 ≤ n) (c : ℝ) (h : EdgeCosts)
    (h_nonneg_remote : ∀ s : ChainState n, Remote s → 0 ≤ rawScore c h s) :
    ∃ (b : ℝ) (k : EdgeCosts), 0 ≤ b ∧ Nonnegative k ∧
      ∀ s : ChainState n, Remote s → rawScore c h s = rawScore b k s := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  have heq : n = m + 2 := by omega
  clear hm
  subst n
  refine ⟨c + h (m + 1) 1 0 1 + prefixMin h m 1, gauge h m,
    gauge_constant_nonnegative m c h h_nonneg_remote, gauge_nonnegative h m, ?_⟩
  intro s hs
  exact gauge_score_identity m c h s hs

#print axioms gauge_exists

end NeighborSeparation
