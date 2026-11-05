module

public import UniformScan
public import RegularDrift

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal.Tightness.ExceptionalBound

open scoped BigOperators
open Filtering ProductFiltering ObservedFeatures ActualScan PotentialAlgebra

/-- At an exceptional observation there is at most one trailing zero, and
    its indicator charge exactly compensates the retained-distance shift. -/
theorem exceptional_localPotential_index {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i)
    (he : i.val = 0 ∨ value s (i.val - 1) = 2) :
    localPotential s =
      35 * (((i.val + 1 : ℕ) : ℝ) - (barrierHeight s : ℝ)) := by
  have hr : zeroRun s = 0 ∨ zeroRun s = 1 := by
    by_cases hin : value s i.val = 0
    · right
      have hip : 0 < i.val := by
        by_contra hh
        have hiz : i.val = 0 := by omega
        simp [hiz] at hin
      apply zeroRun_eq_one_of_previous_nonzero s i hi hip hin
      rcases he with hfirst | hprev
      · omega
      · simp [hprev]
    · left
      have hnpos : ¬ 0 < zeroRun s := by
        intro hp
        exact hin ((zeroRun_pos_iff s i hi).mp hp)
      omega
  have hnat := retainedDistance_identity s i hi
  rw [failureIndex_of_selected s i hi] at hnat
  have hreal : (retainedDistance s : ℝ) + (zeroRun s : ℝ) +
      (barrierHeight s : ℝ) = ((i.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rcases hr with hr | hr
  · simp only [localPotential, localValue, zeroIndicator, hr]
    norm_num
    rw [hr] at hreal
    norm_num at hreal
    linarith
  · simp only [localPotential, localValue, zeroIndicator, hr]
    norm_num
    rw [hr] at hreal
    norm_num at hreal
    linarith

/-- Failure before a declared prefix cutoff occurs no later than that cutoff. -/
theorem failure_before_cutoff {n : ℕ} (s : ChainState n) (k : ℕ)
    (hnot : ¬ PrefixHolds s k) :
    ∃ j : Fin n, firstFailure s = some j ∧ j.val < k := by
  cases hs : firstFailure s with
  | none =>
      exfalso
      apply hnot
      intro j _
      exact (no_failure_iff s).mp hs j
  | some j =>
      refine ⟨j, rfl, ?_⟩
      by_contra hj
      apply hnot
      intro c hc
      exact selected_prefix s j hs c (by omega)

/-- An early failure costs only the affine index charge, without looking
    at any suffix coordinates. -/
theorem after_early_failure_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (hi : firstFailure s = some i) (u : Draw)
    (b : ℕ) (hb : b ≤ barrierHeight s) (d : ℝ)
    (hline : d + (b : ℝ) = ((i.val + 1 : ℕ) : ℝ))
    (hnot : ¬ PrefixHolds (replace s i u) (i.val + 1)) :
    localPotential (replace s i u) ≤ 35 * d + 33 := by
  obtain ⟨j, hj, hjlt⟩ := failure_before_cutoff (replace s i u) (i.val + 1) hnot
  have hbnew := le_trans hb (barrierHeight_mono_replace hn s i u hi)
  have hcost := UniformScan.localPotential_le_index (replace s i u) j hj b hbnew
    (((j.val + 1 : ℕ) : ℝ) - (b : ℝ)) (by ring)
  have hjcast : ((j.val + 1 : ℕ) : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show j.val + 1 ≤ i.val + 1 by omega)
  linarith

/-- Every redraw is dominated by one common fresh-tail payoff. Early
    failure is overestimated by its positive entry charge. -/
theorem actual_redraw_payoff_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (hi : firstFailure s = some i) (u : Draw)
    (m : ℕ) (hm : i.val + 1 + m + 1 = n)
    (b : ℕ) (hb : b ≤ barrierHeight s) (d : ℝ) (hd : 0 ≤ d)
    (hline : d + (b : ℝ) = ((i.val + 1 : ℕ) : ℝ)) :
    localPotential (replace s i u) ≤ UniformScan.payoff m u.2.1 (d + 1)
      (lettersFrom s (i.val + 1) m hm) (lastTactic s (by omega)) := by
  by_cases hp : PrefixHolds (replace s i u) (i.val + 1)
  · have hbnew := le_trans hb (barrierHeight_mono_replace hn s i u hi)
    have hscan := UniformScan.actual_scan_le (by omega : 0 < n) (replace s i u) b hbnew
      m (i.val + 1) hm hp (d + 1) (by linarith)
      (by push_cast at hline ⊢; linarith)
    have hout := replace_outgoing hn s i u (by omega : i.val + 1 < n)
    simpa only [hout, TailLaw.lettersFrom_replace,
      TailLaw.lastTactic_replace s i u m hm] using hscan
  · have hcost := after_early_failure_bound hn s i hi u b hb d hline hp
    have hentry := UniformScan.entry_le_payoff m u.2.1 (d + 1)
      (lettersFrom s (i.val + 1) m hm) (lastTactic s (by omega))
    linarith

/-- With the selected final bridge there is no fresh outgoing endpoint:
    all active outcomes have index at most the original index. -/
theorem actual_last_redraw_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (hi : firstFailure s = some i) (u : Draw)
    (hlast : i.val + 1 = n) (b : ℕ) (hb : b ≤ barrierHeight s)
    (d : ℝ) (hd : 0 ≤ d)
    (hline : d + (b : ℝ) = ((i.val + 1 : ℕ) : ℝ)) :
    localPotential (replace s i u) ≤ 35 * d + 33 := by
  cases hj : firstFailure (replace s i u) with
  | none =>
      rw [localPotential_of_good _ hj]
      linarith
  | some j =>
      have hbnew := le_trans hb (barrierHeight_mono_replace hn s i u hi)
      have hcost := UniformScan.localPotential_le_index (replace s i u) j hj b hbnew
        (((j.val + 1 : ℕ) : ℝ) - (b : ℝ)) (by ring)
      have hjcast : ((j.val + 1 : ℕ) : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show j.val + 1 ≤ i.val + 1 by omega)
      linarith

/-- Averaging only the genuinely fresh completion gives a constant, rather
    than length-dependent, cost for every exceptional observation. -/
theorem completed_exceptional_local_growth {n : ℕ} (hn : 2 ≤ n)
    (q : PrefixDatum n) (hq : ValidDatum q)
    (he : q.1.val = 0 ∨ value q.2 (q.1.val - 1) = 2) :
    completionMean q (fun s => drawAverage
      (fun u => localPotential (replace s q.1 u))) ≤ localPotential q.2 + 243 := by
  let b : ℕ := barrierHeight q.2
  let d : ℝ := ((q.1.val + 1 : ℕ) : ℝ) - (b : ℝ)
  have hline : d + (b : ℝ) = ((q.1.val + 1 : ℕ) : ℝ) := by dsimp [d]; ring
  have hd : 0 ≤ d := by
    have hbar := barrierHeight_le_selected q.2 q.1 hq.1
    have hcast : (b : ℝ) ≤ ((q.1.val + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show b ≤ q.1.val + 1 by dsimp [b]; omega)
    dsimp [d]
    linarith
  have hlocal : localPotential q.2 = 35 * d := by
    simpa only [d, b] using exceptional_localPotential_index q.2 q.1 hq.1 he
  by_cases hlast : q.1.val + 1 = n
  · have hpoint (s : ChainState n)
        (hs : Agrees (readCoords (q.1.val + 1)) (toCoords q.2) (toCoords s)) :
        drawAverage (fun u => localPotential (replace s q.1 u)) ≤ 35 * d + 33 := by
      have hi := firstFailure_eq_of_agrees q.2 s q.1 hq.1 _ le_rfl hs
      have hb : b ≤ barrierHeight s := by
        rw [barrierHeight_congr q.2 s q.1 hq.1 hs]
      calc
        _ ≤ drawAverage (fun _ => 35 * d + 33) :=
          drawAverage_mono fun u => actual_last_redraw_bound hn s q.1 hi u hlast b hb d hd hline
        _ = _ := drawAverage_const _
    calc
      _ ≤ completionMean q (fun _ => 35 * d + 33) :=
        completionMean_mono q hq _ _ hpoint
      _ = 35 * d + 33 := completionMean_const _ _
      _ ≤ localPotential q.2 + 243 := by rw [hlocal]; linarith
  · let m : ℕ := n - (q.1.val + 1) - 1
    have hm : q.1.val + 1 + m + 1 = n := by dsimp [m]; omega
    rw [completionMean_drawAverage]
    calc
      _ ≤ drawAverage (fun _ => 35 * (d + 1) + 208) := by
        apply drawAverage_mono
        intro u
        calc
          _ ≤ completionMean q (fun s => UniformScan.payoff m u.2.1 (d + 1)
              (lettersFrom s (q.1.val + 1) m hm) (lastTactic s (by omega))) := by
            apply completionMean_mono q hq
            intro s hs
            have hi := firstFailure_eq_of_agrees q.2 s q.1 hq.1 _ le_rfl hs
            have hb : b ≤ barrierHeight s := by
              rw [barrierHeight_congr q.2 s q.1 hq.1 hs]
            exact actual_redraw_payoff_bound hn s q.1 hi u m hm b hb d hd hline
          _ ≤ 35 * (d + 1) + 208 :=
            UniformScan.completion_payoff_le q m hm u.2.1 (d + 1) (by linarith)
      _ = 35 * (d + 1) + 208 := drawAverage_const _
      _ = localPotential q.2 + 243 := by rw [hlocal]; ring

end MTChainFormal.Tightness.ExceptionalBound
