/-
  Backward decoding of the four split-graph choices in HLS Appendix C.
  A down-colored original node with a marked preceding reversible arc
  consumes its extra predecessor. Boundary flags of consumed extras and
  up-colored originals are irrelevant. The graph-to-token bridge is
  developed separately; no graph injectivity is assumed here.
-/
module

public import PPGraph.HLS.DAG.PairKeys
public import Mathlib.Tactic.DeriveFintype

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace HLS

inductive ExpansionChoice where
  | up | down | insertUp | insertDown
  deriving DecidableEq

instance : Fintype ExpansionChoice where
  elems := {.up, .down, .insertUp, .insertDown}
  complete := by intro x; cases x <;> simp

structure ExpansionToken (ι : Type) where
  label : ι
  down : Bool
  predecessorMarked : Bool
  deriving DecidableEq

structure ExpansionAtom (ι : Type) where
  label : ι
  choice : ExpansionChoice
  boundaryMarked : Bool
  deriving DecidableEq

def expansionBlock {ι : Type} (mate : ι → ι) (a : ExpansionAtom ι) : List (ExpansionToken ι) :=
  match a.choice with
  | .up => [⟨a.label, false, a.boundaryMarked⟩]
  | .down => [⟨a.label, true, false⟩]
  | .insertUp => [⟨a.label, true, true⟩, ⟨mate a.label, false, a.boundaryMarked⟩]
  | .insertDown => [⟨a.label, true, true⟩, ⟨mate a.label, true, a.boundaryMarked⟩]

def encodeExpansion {ι : Type} (mate : ι → ι) (L : List (ExpansionAtom ι)) : List (ExpansionToken ι) :=
  L.flatMap (expansionBlock mate)

def decodeExpansion {ι : Type} : List (ExpansionToken ι) → List (ι × ExpansionChoice)
  | [] => []
  | t :: ts =>
    if t.down then
      if t.predecessorMarked then
        match ts with
        | [] => [(t.label, .down)]
        | s :: rest => (t.label, if s.down then .insertDown else .insertUp) :: decodeExpansion rest
      else (t.label, .down) :: decodeExpansion ts
    else (t.label, .up) :: decodeExpansion ts

theorem decode_expansionBlock_append {ι : Type} (mate : ι → ι) (a : ExpansionAtom ι)
    (L : List (ExpansionToken ι)) :
    decodeExpansion (expansionBlock mate a ++ L) = (a.label, a.choice) :: decodeExpansion L := by
  cases a with
  | mk label choice mark =>
    cases choice <;> cases L <;> simp [expansionBlock, decodeExpansion]

theorem decode_encodeExpansion {ι : Type} (mate : ι → ι) (L : List (ExpansionAtom ι)) :
    decodeExpansion (encodeExpansion mate L) = L.map (fun a => (a.label, a.choice)) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [encodeExpansion, List.flatMap_cons, decode_expansionBlock_append]
    exact congrArg (List.cons (a.label, a.choice)) ih

theorem encoded_equality_recovers_choices {ι : Type} (mate : ι → ι)
    (L K : List (ExpansionAtom ι)) (h : encodeExpansion mate L = encodeExpansion mate K) :
    L.map (fun a => (a.label, a.choice)) = K.map (fun a => (a.label, a.choice)) := by
  simpa only [decode_encodeExpansion] using congrArg decodeExpansion h

theorem decoded_length_eq_original {ι : Type} (mate : ι → ι) (L : List (ExpansionAtom ι)) :
    (decodeExpansion (encodeExpansion mate L)).length = L.length := by
  rw [decode_encodeExpansion, List.length_map]

end HLS

#check @HLS.decode_expansionBlock_append
#check @HLS.decode_encodeExpansion
#check @HLS.encoded_equality_recovers_choices
#check @HLS.decoded_length_eq_original
