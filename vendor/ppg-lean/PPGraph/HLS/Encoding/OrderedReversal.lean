/- Consecutive vertices in the construction order give reversible arcs. -/
module

public import PPGraph.HLS.DAG.OrderedDAG

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.OrderedDAG

variable {ι A : Type} [DecidableEq ι] [DecidableEq A]

theorem no_alternate_if_no_middle (G : SimpleGraph ι) (s : Finset A)
    (label : A → ι) (tag : A → ℕ) (before : A → A → Prop)
    (hinj : Set.InjOn (embed label tag) (↑s : Set A))
    (htrans : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, before a b → before b c → before a c)
    (a b : A) (ha : a ∈ s) (hb : b ∈ s)
    (hno : ∀ c ∈ s, ¬ (before a c ∧ before c b)) :
    ¬ Relation.TransGen (eraseArc (build G s label tag before).Edge
      (embed label tag a) (embed label tag b)) (embed label tag a) (embed label tag b) := by
  intro hp
  cases hp with
  | single he => exact he.2 ⟨rfl, rfl⟩
  | tail hp he =>
    have hp' := Relation.TransGen.mono (fun _ _ h => h.1) _ _ hp
    obtain ⟨x, hx, y, hy, hxa, hyc, hxy⟩ :=
      transGen_order G s label tag before hinj htrans _ _ hp'
    obtain ⟨z, hz, w, hw, hzc, hwb, hzw, _⟩ :=
      (edge_witness G s label tag before _ _).mp he.1
    have hxEq : x = a := hinj hx ha hxa
    have hyEq : y = z := hinj hy hz (hyc.trans hzc.symm)
    have hwEq : w = b := hinj hw hb hwb
    have hay : before a y := by simpa only [hxEq] using hxy
    have hyb : before y b := by simpa only [← hyEq, hwEq] using hzw
    exact hno y hy ⟨hay, hyb⟩

theorem reversible_if_no_middle (G : SimpleGraph ι) (s : Finset A)
    (label : A → ι) (tag : A → ℕ) (before : A → A → Prop)
    (hinj : Set.InjOn (embed label tag) (↑s : Set A))
    (htrans : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, before a b → before b c → before a c)
    (hValid : (build G s label tag before).Valid G) (a b : A) (ha : a ∈ s) (hb : b ∈ s)
    (hbefore : before a b) (hdep : label a = label b ∨ G.Adj (label a) (label b))
    (hno : ∀ c ∈ s, ¬ (before a c ∧ before c b)) :
    Acyclic (reverseArc (build G s label tag before).Edge (embed label tag a) (embed label tag b)) := by
  have he := (edge_embed G s label tag before hinj a b ha hb).mpr ⟨hbefore, hdep⟩
  apply (reversible_iff_no_alternate_path _ _ _ hValid.acyclic he).mpr
  exact no_alternate_if_no_middle G s label tag before hinj htrans a b ha hb hno

end HLS.OrderedDAG

#check @HLS.OrderedDAG.no_alternate_if_no_middle
#check @HLS.OrderedDAG.reversible_if_no_middle
