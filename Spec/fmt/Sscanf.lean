/-
`fmt.Sscanf`: the trust boundary (Perennial translates `fmt` names-only and models `Sprintf`, not
the scanner), for the one call shape the recipes make, `Sscanf(s, "%d", &n)` with `n` an `int`
(`newSequentialKV`). Lean-first (no Rocq counterpart); see `decisions.md`, "Recipes", "Units 1b,
2 and 3".

**The parse** (`fmt.scanInt s`, pure): Go's `%d` into an `int` skips leading spaces, accepts one
sign (`+` or `-`), reads the longest run of decimal digits (it must be non-empty) and parses it
(`strconv.ParseInt(tok, 10, 64)`: the value must fit an `int64`); what follows the digits is
ignored (`"5abc"` scans as `5`). `scanInt` skips ASCII spaces only: Go skips every Unicode space
(a tab too) but fails on a newline, so on an input whose first non-space byte is another space
`scanInt` gives `none`, and the axiom then says nothing of the value (below).
-/
module

public import Perennial.Proof.fmt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- An ASCII decimal digit, `'0'` to `'9'`. -/
def fmt.isDigitByte (b : w8) : Bool := decide (48 ≤ uint.Z b ∧ uint.Z b ≤ 57)

/-- The value of a run of decimal digits, most significant first. -/
def fmt.digitsValue (ds : GoString) : Nat := ds.foldl (fun acc b => acc * 10 + (uint.nat b - 48)) 0

/-- **`Sscanf(s, "%d", &n)` for an `int` `n`**, as far as it is modelled: the value of the
longest run of decimal digits after the leading ASCII spaces (`W8 32`) and an optional sign
(`W8 45` is `-`, `W8 43` is `+`), if that run is non-empty and its value fits an `int64`;
`none` otherwise (where Go fails, or skips a space other than `' '`). -/
def fmt.scanInt (s : GoString) : Option Int :=
  let s1 := s.dropWhile (fun b => b == W8 32)
  let s2 := if s1.head? = some (W8 45) ∨ s1.head? = some (W8 43) then s1.tail else s1
  let ds := s2.takeWhile fmt.isDigitByte
  let z : Int := if s1.head? = some (W8 45) then -(fmt.digitsValue ds : Int) else fmt.digitsValue ds
  if ds ≠ [] ∧ -2 ^ 63 ≤ z ∧ z < 2 ^ 63 then some z else none

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **`fmt.Sscanf(s, "%d", &n)`** for an `int` variable `n` (the arguments' slice `[&n]` as
`any`s): returns a count and an error; with no error, `n` holds what Go's `%d` parsed, which is
`scanInt s` where that is defined; with an error, `n` is unchanged. -/
abbrev fmt.Sscanf.spec : Prop :=
  ∀ (s : GoString) (sl : GoSlice) (dq : DFrac) (p : Loc) (n0 : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
      sl ↦*{dq} [interface.mkOk (go.GoType.PointerType go.int) #p] ∗ p ↦ n0 }}
    (App (App (App (Val (@! _root_.Perennial.fmt.Sscanf)) (Val #s)) (Val #(go!"%d")))
      (Val #sl))
  {{ (cnt : w64) (err : GoInterface), RET (PairV #cnt #err);
      sl ↦*{dq} [interface.mkOk (go.GoType.PointerType go.int) #p] ∗ ∃ n : w64, p ↦ n ∗
      ((⌜err = GoInterface.nil⌝ ∗ ⌜∀ z, fmt.scanInt s = some z → sint.Z n = z⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ n = n0⌝) }}

end spec

end EtcdGrove
end Perennial
