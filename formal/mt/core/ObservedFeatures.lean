module

public import Filtering
public import Features

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal.ObservedFeatures

open scoped BigOperators
open Filtering ProductFiltering

theorem agrees_symmetric {n : ℕ} (s t : ChainState n) (cut : ℕ)
    (h : Agrees (readCoords cut) (toCoords s) (toCoords t)) :
    Agrees (readCoords cut) (toCoords t) (toCoords s) := by
  intro c hc
  exact (h c hc).symm

theorem isBarrier_congr {n : ℕ} (s t : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i)
    (h : Agrees (readCoords (i.val + 1)) (toCoords s) (toCoords t))
    (j : Fin n) : IsBarrier t j ↔ IsBarrier s j := by
  have ht := firstFailure_eq_of_agrees s t i hi _ le_rfl h
  constructor
  · intro hb
    have hj := barrier_before_selected t j i hb ht
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      rw [← passes_eq_of_agrees s t _ h k (by omega)]
      exact hb.1 k hk
    · rw [← value_eq_of_agrees s t _ h j.val (by omega)]
      exact hb.2.1
    · have heq := h (.inr j) (by simp; omega)
      change t.tactic j = s.tactic j at heq
      rw [← heq]
      exact hb.2.2
  · intro hb
    have hj := barrier_before_selected s j i hb hi
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      rw [passes_eq_of_agrees s t _ h k (by omega)]
      exact hb.1 k hk
    · rw [value_eq_of_agrees s t _ h j.val (by omega)]
      exact hb.2.1
    · have heq := h (.inr j) (by simp; omega)
      change t.tactic j = s.tactic j at heq
      rw [heq]
      exact hb.2.2

theorem barrierHeight_congr {n : ℕ} (s t : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i)
    (h : Agrees (readCoords (i.val + 1)) (toCoords s) (toCoords t)) :
    barrierHeight t = barrierHeight s := by
  classical
  have ht := firstFailure_eq_of_agrees s t i hi _ le_rfl h
  have hbar : barrierCandidates t = barrierCandidates s := by
    ext j
    simp only [mem_barrierCandidates, isBarrier_congr s t i hi h]
  simp [barrierHeight, hi, ht, hbar]

theorem zeroRun_congr {n : ℕ} (s t : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i)
    (h : Agrees (readCoords (i.val + 1)) (toCoords s) (toCoords t)) :
    zeroRun t = zeroRun s := by
  classical
  have ht := firstFailure_eq_of_agrees s t i hi _ le_rfl h
  have hz : prefixZeroSites t = prefixZeroSites s := by
    ext j
    simp only [prefixZeroSites, failureIndex_of_selected s i hi,
      failureIndex_of_selected t i ht, Finset.mem_filter, Finset.mem_range]
    by_cases hj : j < i.val + 1
    · rw [value_eq_of_agrees s t _ h j (by omega)]
    · simp [hj]
  simp [zeroRun, hi, ht, hz]

theorem retainedDistance_congr {n : ℕ} (s t : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i)
    (h : Agrees (readCoords (i.val + 1)) (toCoords s) (toCoords t)) :
    retainedDistance t = retainedDistance s := by
  have ht := firstFailure_eq_of_agrees s t i hi _ le_rfl h
  simp [retainedDistance, hi, ht, failureIndex, barrierHeight_congr s t i hi h,
    zeroRun_congr s t i hi h]

theorem localPotential_congr {n : ℕ} (s t : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i)
    (h : Agrees (readCoords (i.val + 1)) (toCoords s) (toCoords t)) :
    localPotential t = localPotential s := by
  simp only [localPotential, retainedDistance_congr s t i hi h,
    zeroIndicator, zeroRun_congr s t i hi h]

theorem chainPotential_congr {n : ℕ} (s t : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i)
    (h : Agrees (readCoords (i.val + 1)) (toCoords s) (toCoords t)) :
    chainPotential t = chainPotential s := by
  simp only [chainPotential, barrierHeight_congr s t i hi h,
    localPotential_congr s t i hi h]

end MTChainFormal.ObservedFeatures
