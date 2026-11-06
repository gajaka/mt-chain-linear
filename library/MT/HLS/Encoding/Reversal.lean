/-
  Reversible arcs of witness DAGs (He--Li--Sun, arXiv:2111.06527,
  Definition 2.4 and Fact 2.5). An alternate path is represented by a
  directed path after deleting the particular arc. Reversal preserves
  acyclicity exactly when this alternate path does not exist.
  https://arxiv.org/abs/2111.06527
-/
module

public import Mathlib.Logic.Relation
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace HLS

variable {V : Type*}

def Acyclic (r : V → V → Prop) : Prop := ∀ x, ¬ Relation.TransGen r x x

def eraseArc (r : V → V → Prop) (u v : V) : V → V → Prop :=
  fun x y => r x y ∧ ¬ (x = u ∧ y = v)

def addArc (r : V → V → Prop) (u v : V) : V → V → Prop :=
  fun x y => r x y ∨ (x = u ∧ y = v)

def reverseArc (r : V → V → Prop) (u v : V) : V → V → Prop :=
  addArc (eraseArc r u v) v u

theorem Acyclic.mono (r s : V → V → Prop) (h : ∀ x y, s x y → r x y)
    (hr : Acyclic r) : Acyclic s := by
  intro x hx
  exact hr x (Relation.TransGen.mono h x x hx)

theorem Acyclic.irrefl (r : V → V → Prop) (hr : Acyclic r) (x : V) : ¬ r x x :=
  fun hx => hr x (.single hx)

theorem Acyclic.asymm (r : V → V → Prop) (hr : Acyclic r) (u v : V)
    (huv : r u v) : ¬ r v u :=
  fun hvu => hr u ((Relation.TransGen.single huv).trans (.single hvu))

theorem Acyclic.eraseArc (r : V → V → Prop) (hr : Acyclic r) (u v : V) :
    Acyclic (eraseArc r u v) := Acyclic.mono r _ (fun _ _ h => h.1) hr

/-- An added arc can occur at most once in a path when there is no return
path. The decomposition is the key acyclicity argument. -/
theorem transGen_addArc_cases (r : V → V → Prop) (u v x y : V)
    (hreturn : ¬ Relation.ReflTransGen r v u)
    (hpath : Relation.TransGen (addArc r u v) x y) :
    Relation.TransGen r x y ∨
      (Relation.ReflTransGen r x u ∧ Relation.ReflTransGen r v y) := by
  induction hpath using Relation.TransGen.trans_induction_on with
  | @single a b h =>
    rcases h with h | ⟨rfl, rfl⟩
    · exact Or.inl (.single h)
    · exact Or.inr ⟨.refl, .refl⟩
  | @trans a b c _ _ ih₁ ih₂ =>
    rcases ih₁ with h₁ | ⟨h₁, h₁'⟩ <;> rcases ih₂ with h₂ | ⟨h₂, h₂'⟩
    · exact Or.inl (h₁.trans h₂)
    · exact Or.inr ⟨h₁.to_reflTransGen.trans h₂, h₂'⟩
    · exact Or.inr ⟨h₁, h₁'.trans h₂.to_reflTransGen⟩
    · exact False.elim (hreturn (h₁'.trans h₂))

theorem acyclic_addArc (r : V → V → Prop) (u v : V) (hr : Acyclic r)
    (hreturn : ¬ Relation.ReflTransGen r v u) : Acyclic (addArc r u v) := by
  intro x hx
  rcases transGen_addArc_cases r u v x x hreturn hx with h | ⟨h₁, h₂⟩
  · exact hr x h
  · exact hreturn (h₂.trans h₁)

theorem acyclic_addArc_iff (r : V → V → Prop) (u v : V) (hr : Acyclic r) :
    Acyclic (addArc r u v) ↔ ¬ Relation.ReflTransGen r v u := by
  constructor
  · intro h hreturn
    have hpath : Relation.ReflTransGen (addArc r u v) v u :=
      Relation.ReflTransGen.mono (fun _ _ h => Or.inl h) _ _ hreturn
    have hedge : addArc r u v u v := Or.inr ⟨rfl, rfl⟩
    exact h u ((Relation.TransGen.single hedge).trans_left hpath)
  · exact acyclic_addArc r u v hr

/-- Fact 2.5, with the length-at-least-two path expressed by deleting the arc. -/
theorem reversible_iff_no_alternate_path (r : V → V → Prop) (u v : V)
    (hr : Acyclic r) (hedge : r u v) :
    Acyclic (reverseArc r u v) ↔ ¬ Relation.TransGen (eraseArc r u v) u v := by
  have huv : u ≠ v := by
    intro h
    subst v
    exact hr.irrefl r u hedge
  rw [reverseArc, acyclic_addArc_iff _ v u (hr.eraseArc r u v),
    Relation.reflTransGen_iff_eq_or_transGen]
  simp [Ne.symm huv]

theorem reverseArc_oriented (r : V → V → Prop) (u v x y : V)
    (hedge : r u v) :
    (reverseArc r u v x y ∨ reverseArc r u v y x) ↔ (r x y ∨ r y x) := by
  unfold reverseArc addArc eraseArc
  constructor
  · intro h
    rcases h with h | h
    · rcases h with ⟨h, _⟩ | ⟨rfl, rfl⟩
      · exact Or.inl h
      · exact Or.inr hedge
    · rcases h with ⟨h, _⟩ | ⟨rfl, rfl⟩
      · exact Or.inr h
      · exact Or.inl hedge
  · intro h
    by_cases h₁ : x = u ∧ y = v
    · exact Or.inr (Or.inr ⟨h₁.2, h₁.1⟩)
    by_cases h₂ : y = u ∧ x = v
    · exact Or.inl (Or.inr ⟨h₂.2, h₂.1⟩)
    rcases h with h | h
    · exact Or.inl (Or.inl ⟨h, h₁⟩)
    · exact Or.inr (Or.inl ⟨h, h₂⟩)

end HLS

#check @HLS.Acyclic.mono
#check @HLS.Acyclic.irrefl
#check @HLS.Acyclic.asymm
#check @HLS.Acyclic.eraseArc
#check @HLS.transGen_addArc_cases
#check @HLS.acyclic_addArc
#check @HLS.acyclic_addArc_iff
#check @HLS.reversible_iff_no_alternate_path
#check @HLS.reverseArc_oriented
