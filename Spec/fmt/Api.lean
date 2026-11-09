/-
# Go's `fmt` scanning: the trust boundary's vocabulary (batch 1f)

Perennial specifies `fmt.Sprintf`, `Printf`, `Errorf` (`Perennial/Spec/fmt/`), not the scanning
functions. The recipes' `newSequentialKV` parses a key's last field with `fmt.Sscanf(s, "%d", &n)`;
its spec (`Sscanf.lean`) is **assumed** (Go's `fmt` is not verified here), stated over:

* `decValue s` (pure): the value of `s` if it is a non-empty string of ASCII decimal digits.
* `scanErr err` (persistent): `err` is an error `fmt`'s scanning returns: an `*errors.errorString`
  `fmt` allocates (`"expected integer"`, ...), `io.EOF`, `io.ErrUnexpectedEOF`, or a
  `*strconv.NumError` (an out-of-range number) wrapping `strconv.ErrRange`/`ErrSyntax`. None of these
  has an `Is` method, and unwrapping one reaches only `strconv`'s or `io`'s sentinels: so
  `errors.Is(err, t)` is false for any `errors.New` sentinel `t` of another package (`recipes`'
  `errorsIs_recipeErr` relies on that). Intended realization: a disjunction over those shapes.

Law: `scanErr_persistent`, `scanErr_ne_nil`.
-/
module

public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Fmt

open Iris Iris.BI

/-- The value of `s` if it is a non-empty string of ASCII decimal digits (`'0'` to `'9'`). -/
def decValue (s : GoString) : Option Nat :=
  if s ≠ [] ∧ ∀ b ∈ s, 48 ≤ b.toNat ∧ b.toNat ≤ 57 then
    some (s.foldl (fun acc b => acc * 10 + (b.toNat - 48)) 0)
  else none

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **`err` is an error `fmt`'s scanning returns** (persistent; see the header). -/
opaque scanErr [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (err : GoInterface) : IProp GF := iprop(True)

def scanErr_persistent.spec : Prop := ∀ err, Persistent (scanErr (GF := GF) err)

def scanErr_ne_nil.spec : Prop := ∀ err, scanErr (GF := GF) err ⊢ ⌜err ≠ GoInterface.nil⌝

end res

end Fmt
end EtcdGrove
end Perennial
