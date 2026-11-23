/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsoncodec/ScanDef.lean (lab master 915f964;
notes/dsv-vr.md).
-/
/-
`jsoncodec.Scan` as a Lean function (`scanL`, `vsrnet.scanF`): a transcription of
harness/jsoncodec/jsoncodec.go's `Scan` and its helpers, on the suffix of the input at the
current index (each helper takes the bytes from its index `i` on and returns absolute
indices). Statuses: 0 Done, 1 More, 2 Bad.
-/
module

public import Perennial.Std.ByteString

@[expose] public section

namespace VsrJson

open Perennial

/-- JSON whitespace (`jsoncodec.IsSpace`). -/
def spB (c : w8) : Bool := [32#8, 9#8, 10#8, 13#8].contains c

/-- `isDigit`. -/
def isDig (c : w8) : Bool := decide (48#8 ≤ c) && decide (c ≤ 57#8)

/-- `isHex`. -/
def isHexB (c : w8) : Bool :=
  isDig c || (decide (97#8 ≤ c) && decide (c ≤ 102#8)) || (decide (65#8 ≤ c) && decide (c ≤ 70#8))

/-- The escapes after a backslash other than `u`. -/
def escB (e : w8) : Bool := [34#8, 92#8, 47#8, 98#8, 102#8, 110#8, 114#8, 116#8].contains e

/-- `scanString`'s loop from index `j` (the bytes from `j` on): status and index. -/
def strL : List w8 → Nat → Nat × Nat
  | [], j => (1, j)
  | c :: cs, j =>
    if c = 34#8 then (0, j + 1)
    else if c < 32#8 then (2, j)
    else if c = 92#8 then
      match cs with
      | [] => (1, j)
      | e :: cs' =>
        if e = 117#8 then
          match cs' with
          | [] => (1, j + 2)
          | h1 :: r1 => if !isHexB h1 then (2, j + 2) else
            match r1 with
            | [] => (1, j + 3)
            | h2 :: r2 => if !isHexB h2 then (2, j + 3) else
              match r2 with
              | [] => (1, j + 4)
              | h3 :: r3 => if !isHexB h3 then (2, j + 4) else
                match r3 with
                | [] => (1, j + 5)
                | h4 :: r4 => if !isHexB h4 then (2, j + 5) else strL r4 (j + 6)
        else if escB e then strL cs' (j + 2)
        else (2, j)
    else strL cs (j + 1)

/-- `scanDigits` from index `j`: the index after the digits and the bytes after them. -/
def digitsL : List w8 → Nat → Nat × List w8
  | [], j => (j, [])
  | c :: cs, j => if isDig c then digitsL cs (j + 1) else (j, c :: cs)

/-- A number's end at the end of the input. -/
def endS (eof : Bool) (j : Nat) : Nat × Nat := if eof then (0, j) else (1, j)

/-- A number's exponent part, at `j` (after its integer and fraction parts; the input goes on). -/
def expL (cs : List w8) (j : Nat) (eof : Bool) : Nat × Nat :=
  match cs with
  | [] => endS eof j
  | c :: r =>
    if c = 101#8 ∨ c = 69#8 then
      let p : Nat × List w8 := match r with
        | s :: r' => if s = 43#8 ∨ s = 45#8 then (j + 2, r') else (j + 1, r)
        | [] => (j + 1, [])
      match p.2 with
      | [] => (1, p.1)
      | d :: r3 =>
        if !isDig d then (2, p.1) else
          let q := digitsL (d :: r3) p.1
          match q.2 with
          | [] => endS eof q.1
          | _ :: _ => (0, q.1)
    else (0, j)

/-- A number's fraction and exponent parts, at `j` (after its integer part; the input goes on). -/
def fracL (cs : List w8) (j : Nat) (eof : Bool) : Nat × Nat :=
  match cs with
  | [] => endS eof j
  | c :: r =>
    if c = 46#8 then
      match r with
      | [] => (1, j + 1)
      | d :: r' =>
        if !isDig d then (2, j + 1) else
          let q := digitsL (d :: r') (j + 1)
          match q.2 with
          | [] => endS eof q.1
          | r4@(_ :: _) => expL r4 q.1 eof
    else expL cs j eof

/-- A number's integer part at `j` (a digit), then the rest. -/
def intL (cs : List w8) (j : Nat) (eof : Bool) : Nat × Nat :=
  let p : Nat × List w8 := match cs with
    | c :: r => if c = 48#8 then (j + 1, r) else digitsL cs j
    | [] => (j, [])
  match p.2 with
  | [] => endS eof p.1
  | r@(_ :: _) => fracL r p.1 eof

/-- `scanNumber` at `i` (a `-` or a digit). -/
def numL (cs : List w8) (i : Nat) (eof : Bool) : Nat × Nat :=
  match cs with
  | [] => (2, i)
  | c :: r =>
    if c = 45#8 then
      match r with
      | [] => (1, i + 1)
      | d :: r' => if !isDig d then (2, i + 1) else intL (d :: r') (i + 1) eof
    else intL cs i eof

/-- `scanLiteral` of `lit` at `j`. -/
def litL : List w8 → Nat → List w8 → Nat × Nat
  | _, j, [] => (0, j)
  | [], j, _ :: _ => (1, j)
  | c :: cs, j, l :: ls => if c = l then litL cs (j + 1) ls else (2, j)

/-- `scanScalar` at `i` (a byte that is not whitespace). -/
def scalarL (cs : List w8) (i : Nat) (eof : Bool) : Nat × Nat :=
  match cs with
  | [] => (2, i)
  | c :: r =>
    if c = 34#8 then strL r (i + 1)
    else if c = 45#8 ∨ isDig c then numL cs i eof
    else if c = 116#8 then litL cs i go!"true"
    else if c = 102#8 then litL cs i go!"false"
    else if c = 110#8 then litL cs i go!"null"
    else (2, i)

/-- `MaxDepth`. -/
abbrev maxDepth : Nat := 10000

/-- `Scan`'s loop, at index `i` (the bytes from `i` on), with the open containers `stk` (the
innermost first), the state `st` and `emptyOK` (whitespace is skipped a byte at a time). -/
def goL (cs : List w8) (i : Nat) (stk : List w8) (st : Nat) (eOK : Bool) (eof : Bool) :
    Nat × Nat :=
  match cs with
  | [] => (1, i)
  | c :: r =>
    if spB c then goL r (i + 1) stk st eOK eof
    else if st = 0 then
      if c = 91#8 ∨ c = 123#8 then
        if maxDepth ≤ stk.length then (2, i)
        else goL r (i + 1) (c :: stk) (if c = 123#8 then 2 else 0) true eof
      else if c = 93#8 ∧ eOK = true ∧ stk.head? = some 91#8 then
        if stk.tail = [] then (0, i + 1)
        else goL r (i + 1) stk.tail 1 false eof
      else
        let p := scalarL (c :: r) i (eof && stk.isEmpty)
        if p.1 ≠ 0 then p
        else if stk = [] then (0, p.2)
        else goL (r.drop (p.2 - i - 1)) p.2 stk 1 false eof
    else if st = 1 then
      match stk with
      | [] => (2, i)
      | top :: stk' =>
        if c = 44#8 then goL r (i + 1) stk (if top = 123#8 then 2 else 0) eOK eof
        else if (c = 93#8 ∧ top = 91#8) ∨ (c = 125#8 ∧ top = 123#8) then
          if stk' = [] then (0, i + 1)
          else goL r (i + 1) stk' 1 eOK eof
        else (2, i)
    else if st = 2 then
      if c = 125#8 ∧ eOK = true then
        if stk.tail = [] then (0, i + 1)
        else goL r (i + 1) stk.tail 1 false eof
      else if c ≠ 34#8 then (2, i)
      else
        let p := strL r (i + 1)
        if p.1 ≠ 0 then p
        else goL (r.drop (p.2 - i - 1)) p.2 stk 3 false eof
    else
      if c ≠ 58#8 then (2, i)
      else goL r (i + 1) stk 0 eOK eof
termination_by cs.length
decreasing_by all_goals (simp; try omega)

/-- `Scan(b, eof)`: status and end. -/
def scanL (b : List w8) (eof : Bool) : Nat × Nat := goL b 0 [] 0 false eof

end VsrJson
