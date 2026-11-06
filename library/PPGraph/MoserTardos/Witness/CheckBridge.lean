/-
  PPGraphMoserTardosCheckBridge.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), the address-to-shape bridge
  for tauCheck: the real, address-indexed `tauCheck P (tau_C P C t) omega`
  (PPGraphMoserTardosCheck.lean) agrees with the WTree-level
  `WTree.tauCheck P omega ((tau_C P C t).toWTree [])`
  (PPGraphMoserTardosCheckShape.lean). Combined with
  `WTree.tauCheck_congr_of_canonicalize_eq`, this lets the entropy-compression
  union bound compare TWO DIFFERENT tau_C-built trees (a real occurrence and a
  fixed shape-representative) purely via their canonical WTree shapes.

  Scoped to `tau_C P C t`-built trees specifically (not arbitrary GrowingTree),
  matching the existing scope of Theorem 5.7.2 (`logMeasure_tauCheck_eq_prod_p`,
  PPGraphMoserTardosProbability.lean) and of `PPGraphMoserTardosRealTree.lean`'s
  own label/WellFormed/Proper facts -- nothing in the union-bound assembly ever
  needs this for a generic GrowingTree.

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.MoserTardos.Witness.CheckShape
public import PPGraph.MoserTardos.Witness.RealTree
public import PPGraph.MoserTardos.Witness.Check

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Classical

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- Generalized (fuel + starting address v) form, mirroring
-- `GrowingTree.toWTreeFuel_footprintCountBeyondAt`'s induction exactly,
-- with the Finset.card target replaced by a Prop conjunction.
-- -------------------------------------------------------------------

theorem τC_toWTreeFuel_checkOK {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (ω : LogSpace S) :
    ∀ n v, v ∈ (τC P C t).dom → (∀ w ∈ (τC P C t).dom, w.length ≤ v.length + n) →
      (WTree.checkOK P ω ((τC P C t).toWTree []) v.length ((τC P C t).toWTreeFuel n v)
        ↔ ∀ w ∈ (τC P C t).dom, v <+: w →
            checkState P (τC P C t) ω w ∈ P.bad ((τC P C t).lab w)) := by
  intro n
  induction n with
  | zero =>
    intro v hv hb
    have hstateEq : WTree.checkStateAt P ω ((τC P C t).toWTree []) v.length
        = checkState P (τC P C t) ω v := by
      funext x
      show atIdx ω x (WTree.footprintCountBeyondAt P x v.length 0 ((τC P C t).toWTree []))
        = atIdx ω x (localCount P (τC P C t) v x)
      rw [GrowingTree.localCount_eq_footprintCountBeyondAt P (τC P C t) (τC_valid P C t) v x hv
        (τC_root_mem P C t)]
    show (WTree.checkStateAt P ω ((τC P C t).toWTree []) v.length ∈ P.bad ((τC P C t).lab v)
        ∧ WTree.checkOKList P ω ((τC P C t).toWTree []) (v.length + 1) [])
      ↔ ∀ w ∈ (τC P C t).dom, v <+: w → checkState P (τC P C t) ω w ∈ P.bad ((τC P C t).lab w)
    simp only [WTree.checkOKList, and_true, hstateEq]
    constructor
    · intro hcheck w hw hpre
      have hweq : w = v := (hpre.eq_of_length_le (by have := hb w hw; omega)).symm
      rwa [hweq]
    · intro hall
      exact hall v hv (List.prefix_refl v)
  | succ n ih =>
    intro v hv hb
    set children := (τC P C t).dom.filter (fun w => ∃ k, w = v ++ [k]) with hchildren_def
    show
      (WTree.checkStateAt P ω ((τC P C t).toWTree []) v.length ∈ P.bad ((τC P C t).lab v)
        ∧ WTree.checkOKList P ω ((τC P C t).toWTree []) (v.length + 1)
            (children.toList.map (fun w => (τC P C t).toWTreeFuel n w)))
      ↔ ∀ w ∈ (τC P C t).dom, v <+: w → checkState P (τC P C t) ω w ∈ P.bad ((τC P C t).lab w)
    have hstateEq : WTree.checkStateAt P ω ((τC P C t).toWTree []) v.length
        = checkState P (τC P C t) ω v := by
      funext x
      show atIdx ω x (WTree.footprintCountBeyondAt P x v.length 0 ((τC P C t).toWTree []))
        = atIdx ω x (localCount P (τC P C t) v x)
      rw [GrowingTree.localCount_eq_footprintCountBeyondAt P (τC P C t) (τC_valid P C t) v x hv
        (τC_root_mem P C t)]
    rw [hstateEq, WTree.checkOKList_iff_forall_mem]
    have hstepA : (∀ b ∈ children.toList.map (fun w => (τC P C t).toWTreeFuel n w),
          WTree.checkOK P ω ((τC P C t).toWTree []) (v.length + 1) b)
        ↔ ∀ w ∈ children.toList, ∀ w' ∈ (τC P C t).dom, w <+: w' →
            checkState P (τC P C t) ω w' ∈ P.bad ((τC P C t).lab w') := by
      apply list_forall_map_iff_pointwise
      intro w hw
      rw [Finset.mem_toList, hchildren_def, Finset.mem_filter] at hw
      obtain ⟨hwdom, k, hwk⟩ := hw
      have hwlen : w.length = v.length + 1 := by rw [hwk]; simp
      have hbw : ∀ w' ∈ (τC P C t).dom, w'.length ≤ w.length + n := by
        intro w' hw'
        have hb' := hb w' hw'
        omega
      rw [← hwlen]
      exact ih w hwdom hbw
    rw [hstepA]
    constructor
    · rintro ⟨hself, hchildren_all⟩ w hwdom hpre
      rcases eq_or_ne w v with heq | hne
      · subst heq; exact hself
      · obtain ⟨tl, htl⟩ := hpre
        have htl_ne : tl ≠ [] := by
          intro h; subst h; simp only [List.append_nil] at htl; exact hne htl.symm
        obtain ⟨k, tl', htlk⟩ := List.exists_cons_of_ne_nil htl_ne
        have hkey : (v ++ [k]) ++ tl' = w := by rw [← htl, htlk]; simp [List.append_assoc]
        have hchild_mem : v ++ [k] ∈ children.toList := by
          rw [Finset.mem_toList, hchildren_def, Finset.mem_filter]
          exact ⟨GrowingTree.Valid.prefix_mem (τC P C t)
              (τC_valid P C t) w hwdom (v ++ [k]) ⟨tl', hkey⟩, k, rfl⟩
        exact hchildren_all (v ++ [k]) hchild_mem w hwdom ⟨tl', hkey⟩
    · intro hall
      refine ⟨hall v hv (List.prefix_refl v), ?_⟩
      intro w hw w' hw'dom hpre
      rw [Finset.mem_toList, hchildren_def, Finset.mem_filter] at hw
      obtain ⟨_, k, hwk⟩ := hw
      have hvw : v <+: w := by rw [hwk]; exact ⟨[k], rfl⟩
      exact hall w' hw'dom (hvw.trans hpre)

-- -------------------------------------------------------------------
-- Specialize at the root: the address-level `tauCheck` (all of `T.dom`)
-- agrees with the WTree-level `tauCheck` on the reconstructed tree.
-- -------------------------------------------------------------------

/-- The address-to-shape bridge. The real, address-indexed `tauCheck` on
    a `tau_C`-built tree agrees with the WTree-level `tauCheck` on its
    reconstruction. Combined with `tauCheck_congr_of_canonicalize_eq`, two
    `tau_C`-built trees whose reconstructions canonicalize to the SAME shape
    give the SAME address-level `tauCheck` verdict. -/
theorem τC_tauCheck_iff_WTree_tauCheck {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (ω : LogSpace S) :
    τCheck P (τC P C t) ω ↔ WTree.tauCheck P ω ((τC P C t).toWTree []) := by
  have hroot : ([] : List ℕ) ∈ (τC P C t).dom := (τC_root_mem P C t)
  have hb : ∀ w ∈ (τC P C t).dom, w.length ≤ ([] : List ℕ).length + (τC P C t).dom.card := by
    intro w hw
    have := GrowingTree.Valid.length_lt_card (τC P C t) (τC_valid P C t) hw
    simp only [List.length_nil, zero_add]
    omega
  have hkey := τC_toWTreeFuel_checkOK P C t ω (τC P C t).dom.card [] hroot hb
  show τCheck P (τC P C t) ω
    ↔ WTree.checkOK P ω ((τC P C t).toWTree []) 0 ((τC P C t).toWTreeFuel (τC P C t).dom.card [])
  rw [show (0:ℕ) = ([] : List ℕ).length from rfl, hkey]
  constructor
  · intro hτ w hw _; exact hτ w hw
  · intro hall w hw; exact hall w hw List.nil_prefix

#check @τC_toWTreeFuel_checkOK
#check @τC_tauCheck_iff_WTree_tauCheck
