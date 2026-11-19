/-
The pure model of structured-merge-diff v7.0.0 (SMD): **values** (`value` package). See
`Model/Merge.lean`'s header for the model as a whole.

`UVal` is an unstructured value as `value.NewValueInterface` wraps it: `nil` (`null`), a `bool`, an
`int64`, a `string`, a `[]interface{}` (`list`) or a `map[string]interface{}` (`map`, its entries
kept sorted by key, without duplicates: a Go map has no order). Not modelled: floats, the other
integer types, `map[interface{}]interface{}`, reflection-backed values (the representation
predicate excludes them). Strings are Perennial's `GoString` (bytes); `gsCompare` is
`strings.Compare` (bytewise).

Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Perennial.Std.ByteString

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace smd

/-! ## value -/

/-- `strings.Compare`: bytewise. -/
def gsCompare : GoString → GoString → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | x :: xs, y :: ys =>
    if x.toNat < y.toNat then -1 else if y.toNat < x.toNat then 1 else gsCompare xs ys

def gsLt (a b : GoString) : Bool := gsCompare a b == -1

/-- `value.IntCompare`. -/
def intCompare (a b : w64) : Int :=
  if a.toInt > b.toInt then 1 else if a.toInt == b.toInt then 0 else -1

/-- `value.BoolCompare`. -/
def boolCompare (a b : Bool) : Int :=
  if a == b then 0 else if !a then -1 else 1

inductive UVal where
  | null
  | bool (b : Bool)
  | int (i : w64)
  | str (s : GoString)
  | list (vs : List UVal)
  | map (kvs : List (GoString × UVal))
  deriving Repr, Inhabited

def lookupKV {α : Type} (k : GoString) : List (GoString × α) → Option α
  | [] => none
  | (k', v) :: rest => if k' = k then some v else lookupKV k rest

/-- Insert into a map kept sorted by key (a Go map assignment `m[k] = v`). -/
def insertKV {α : Type} (k : GoString) (v : α) : List (GoString × α) → List (GoString × α)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k' = k then (k, v) :: rest
    else if gsLt k k' then (k, v) :: (k', v') :: rest
    else (k', v') :: insertKV k v rest

def eraseKV {α : Type} (k : GoString) : List (GoString × α) → List (GoString × α)
  | [] => []
  | (k', v') :: rest => if k' = k then rest else (k', v') :: eraseKV k rest

namespace UVal
def isNull : UVal → Bool | .null => true | _ => false
def isInt : UVal → Bool | .int _ => true | _ => false
def isString : UVal → Bool | .str _ => true | _ => false
def isBool : UVal → Bool | .bool _ => true | _ => false
def isList : UVal → Bool | .list _ => true | _ => false
def isMap : UVal → Bool | .map _ => true | _ => false

mutual
def size : UVal → Nat
  | .list vs => sizeL vs + 1
  | .map kvs => sizeM kvs + 1
  | _ => 1
def sizeL : List UVal → Nat
  | [] => 0
  | v :: vs => size v + sizeL vs
def sizeM : List (GoString × UVal) → Nat
  | [] => 0
  | (_, v) :: kvs => size v + sizeM kvs
end

-- `value.EqualsUsing` on unstructured values (no floats).
mutual
def equals : UVal → UVal → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .str a, .str b => decide (a = b)
  | .list as, .list bs => as.length == bs.length && equalsL as bs
  | .map as, .map bs => as.length == bs.length && equalsM as bs
  | _, _ => false
/-- `ListEqualsUsing`'s loop (the lengths are equal). -/
def equalsL : List UVal → List UVal → Bool
  | a :: as, b :: bs => equals a b && equalsL as bs
  | _, _ => true
/-- `mapUnstructuredString.EqualsUsing`: every entry of the right map is in the left one,
equal. -/
def equalsM (lhs : List (GoString × UVal)) : List (GoString × UVal) → Bool
  | [] => true
  | (k, v) :: rest =>
    (match lookupKV k lhs with | some lv => equals lv v | none => false) && equalsM lhs rest
end

/-- The keys of two maps in lexical order, with each side's value (`lexicalKeyOrderedMapZip`). -/
def zipLexical (fuel : Nat) (as bs : List (GoString × UVal)) :
    List (GoString × Option UVal × Option UVal) :=
  match fuel, as, bs with
  | 0, _, _ => []
  | _ + 1, [], [] => []
  | _ + 1, (k, a) :: as, [] => (k, some a, none) :: as.map (fun (k, a) => (k, some a, none))
  | _ + 1, [], (k, b) :: bs => (k, none, some b) :: bs.map (fun (k, b) => (k, none, some b))
  | n + 1, (k, a) :: as', (k', b) :: bs' =>
    if k = k' then (k, some a, some b) :: zipLexical n as' bs'
    else if gsLt k k' then (k, some a, none) :: zipLexical n as' ((k', b) :: bs')
    else (k', none, some b) :: zipLexical n ((k, a) :: as') bs'

/-- `value.CompareUsing` on unstructured values, with fuel (`size lhs + size rhs` suffices). -/
def compareF : Nat → UVal → UVal → Int
  | 0, _, _ => 0
  | n + 1, lhs, rhs =>
    match lhs, rhs with
    | .int a, .int b => intCompare a b
    | .int _, _ => -1
    | _, .int _ => 1
    | .str a, .str b => gsCompare a b
    | .str _, _ => -1
    | _, .str _ => 1
    | .bool a, .bool b => boolCompare a b
    | .bool _, _ => -1
    | _, .bool _ => 1
    | .list as, .list bs =>
      -- `ListCompareUsing`: the first difference, else the shorter first
      let r := (as.zip bs).foldl (fun c (a, b) => if c != 0 then c else compareF n a b) 0
      if r != 0 then r else if as.length < bs.length then -1 else if bs.length < as.length then 1 else 0
    | .list _, _ => -1
    | _, .list _ => 1
    | .map as, .map bs =>
      -- `MapCompareUsing`
      if as.length == 0 && bs.length == 0 then 0 else
      let z := zipLexical (as.length + bs.length + 1) as bs
      let step : (Int × Nat × Bool) → (GoString × Option UVal × Option UVal) → (Int × Nat × Bool) :=
        fun (c, i, stop) (_, l, r) =>
          if stop then (c, i, stop) else
          let c :=
            if i == as.length then -1
            else if i == bs.length then 1
            else match l, r with
              | none, _ => 1
              | _, none => -1
              | some l, some r => compareF n l r
          (c, i + 1, c != 0)
      (z.foldl step (0, 0, false)).1
    | .map _, _ => -1
    | _, .map _ => 1
    | .null, .null => 0
end UVal

/-- `value.Compare`. -/
def UVal.compare (a b : UVal) : Int := UVal.compareF (a.size + b.size + 1) a b

/-- A `value.FieldList`: `(name, value)`. -/
abbrev FieldList := List (GoString × UVal)

/-- `FieldList.Compare`. -/
def flCompare : FieldList → FieldList → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | (n, v) :: as, (n', v') :: bs =>
    let c := gsCompare n n'
    if c != 0 then c else
    let c := UVal.compare v v'
    if c != 0 then c else flCompare as bs

/-- `FieldList.Equals`. -/
def flEquals (as bs : FieldList) : Bool :=
  as.length == bs.length &&
    (as.zip bs).all (fun ((n, v), (n', v')) => decide (n = n') && UVal.equals v v')

/-- `FieldList.Sort`: stable by name (an insertion sort). -/
def flInsert (f : GoString × UVal) : FieldList → FieldList
  | [] => [f]
  | g :: gs => if gsLt f.1 g.1 then f :: g :: gs else g :: flInsert f gs
def flSort (fl : FieldList) : FieldList := fl.foldl (fun acc f => flInsert f acc) []

end smd
end EtcdGrove
end Perennial
