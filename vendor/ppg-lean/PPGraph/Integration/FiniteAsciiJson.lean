/-
  A bounded, kernel-reducible reader for the ASCII/integer JSON fragment used
  by the shared LUCES certificate and exact-ratio input files. Strings with
  escapes, fractional JSON numbers and non-ASCII text are rejected. The fuel
  bounds nested containers and their members; it does not call a native parser.
-/

module

public import Mathlib.Data.List.Basic

@[expose] public section

namespace FiniteAsciiJson

inductive Value where
  | str (value : List Nat)
  | int (value : Int)
  | arr (values : List Value)
  | obj (fields : List (List Nat × Value))

def chars (text : String) : List Nat := text.toList.map Char.toNat

def whitespace (c : Nat) : Bool := c == 32 || c == 9 || c == 10 || c == 13

def skip (input : List Nat) : List Nat := input.dropWhile whitespace

def digit (c : Nat) : Bool := 48 ≤ c && c ≤ 57

def digits (acc : Nat) : List Nat → Nat × List Nat
  | [] => (acc, [])
  | c :: cs => if digit c then digits (acc * 10 + c - 48) cs else (acc, c :: cs)

def stringBody : List Nat → Option (List Nat × List Nat)
  | [] => none
  | c :: cs =>
      if c = 34 then some ([], cs)
      else if 32 ≤ c ∧ c ≤ 126 ∧ c ≠ 92 then do
        let (value, rest) ← stringBody cs
        pure (c :: value, rest)
      else none

mutual

def value : Nat → List Nat → Option (Value × List Nat)
  | 0, _ => none
  | fuel + 1, input =>
      match skip input with
      | [] => none
      | 34 :: cs => do
          let (text, rest) ← stringBody cs
          pure (.str text, rest)
      | 91 :: cs => do
          let (values, rest) ← array fuel true cs
          pure (.arr values, rest)
      | 123 :: cs => do
          let (fields, rest) ← object fuel true cs
          pure (.obj fields, rest)
      | 45 :: c :: cs =>
          if digit c then
            let (n, rest) := digits 0 (c :: cs)
            some (.int (-(Int.ofNat n)), rest)
          else none
      | c :: cs =>
          if digit c then
            let (n, rest) := digits 0 (c :: cs)
            some (.int (Int.ofNat n), rest)
          else none

def array : Nat → Bool → List Nat → Option (List Value × List Nat)
  | 0, _, _ => none
  | fuel + 1, allowEmpty, input =>
      match skip input with
      | 93 :: cs => if allowEmpty then some ([], cs) else none
      | input => do
          let (first, rest) ← value fuel input
          match skip rest with
          | 93 :: cs => pure ([first], cs)
          | 44 :: cs =>
              let (tail, final) ← array fuel false cs
              pure (first :: tail, final)
          | _ => none

def object : Nat → Bool → List Nat → Option (List (List Nat × Value) × List Nat)
  | 0, _, _ => none
  | fuel + 1, allowEmpty, input =>
      match skip input with
      | 125 :: cs => if allowEmpty then some ([], cs) else none
      | 34 :: cs => do
          let (key, rest) ← stringBody cs
          match skip rest with
          | 58 :: cs =>
              let (entry, rest) ← value fuel cs
              match skip rest with
              | 125 :: cs => pure ([(key, entry)], cs)
              | 44 :: cs =>
                  let (tail, final) ← object fuel false cs
                  pure ((key, entry) :: tail, final)
              | _ => none
          | _ => none
      | _ => none

end

def parseBytes (input : List Nat) : Option Value := do
  let (result, rest) ← value 40 input
  if (skip rest).isEmpty then some result else none

def parse (source : String) : Option Value := parseBytes (chars source)

def get (key : String) : Value → Option Value
  | .obj fields => (fields.find? (fun p => p.1 == chars key)).map Prod.snd
  | _ => none

def getArray : Value → Option (List Value)
  | .arr values => some values
  | _ => none

def getString : Value → Option (List Nat)
  | .str text => some text
  | _ => none

def getInt : Value → Option Int
  | .int number => some number
  | _ => none

end FiniteAsciiJson
