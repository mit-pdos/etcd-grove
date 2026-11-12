/-
`fmt.Sscanf(str, "%d", &n)` (Go's standard library): **assumed** (trust boundary; Perennial has the
function's name only). Owned by batch 1f for the recipes' `newSequentialKV` (`key.go:88`), the one
caller on this branch; restated from the old tree's trust-boundary spec (specs-ref
`Spec/fmt/Sscanf.lean`, `notes/decisions.md`), in the weak form the caller needs.

**Why it is true of Go's `fmt`** (go1.27 `fmt/scan.go`): `Sscanf` scans `str` by the format; the
verb `%d` with an `*int` operand runs `scanOne('d', arg)`, which reads an optional sign and decimal
digits (`scanInt` with base 10: leading zeros allowed) and converts them with `strconv.ParseInt`
(64 bits for `int`), storing the result through the pointer. A string of decimal digits whose
value fits an `int64` is therefore scanned without error, and `n` gets that value (`Sscanf` does
not require the input to be consumed in full, and the digits are the whole input here). Anything
else either stores some integer (a prefix's value) and returns `nil`, or returns an error from
`scanError`'s recovery: an `errors.New` value of `fmt`, `io.EOF`/`io.ErrUnexpectedEOF` (an empty
input), or `ParseInt`'s `*strconv.NumError` (out of range): `Fmt.scanErr`. It never panics on a
well-typed operand (`errorHandler` recovers the scanner's own panics); it reads the operand slice
and writes only through the operand. The count returned is not modelled.

**Users**: `newSequentialKV` (`SpecPlan/Spec/go_etcd_io/etcd/client/v3/experimental/recipes/newSequentialKV.lean`).
-/
module

public import SpecPlan.Spec.fmt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Fmt

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- **`fmt.Sscanf(str, "%d", p)`** with `p` an `*int`: on a string of decimal digits whose value
fits an `int64`, `nil` with that value stored at `p`; otherwise `nil` with some value stored, or a
scanning error (`scanErr`). -/
def Sscanf_d.spec : Prop :=
  ∀ (str : GoString) (sl : GoSlice) (p : Loc) (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
      sl ↦* [interface.mkOk (go.GoType.PointerType go.int) #p] ∗ p ↦ x }}
    (App (App (App (Val (@! fmt.Sscanf)) (Val #str)) (Val #go!"%d")) (Val #sl))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      sl ↦* [interface.mkOk (go.GoType.PointerType go.int) #p] ∗ ∃ x' : w64, p ↦ x' ∗
      (⌜err = GoInterface.nil⌝ ∨ scanErr err) ∗
      ⌜∀ v, decValue str = some v → v < 2 ^ 63 → err = GoInterface.nil ∧ sint.Z x' = v⌝ }}

end spec

end Fmt
end EtcdGrove
end Perennial
