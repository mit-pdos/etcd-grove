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

**Printing a gRPC metadata map** (verify round, client-watch's request: `streamKeyFromCtx` is
`fmt.Sprintf("%+v", md)` of a `metadata.MD`, a `map[string][]string`): `printMD md` (opaque pure
function of the map's model, a list of keys with their values, as grpc's `Grpc.MD`): Go prints a map
with its keys sorted, `map[k1:[v11 v12] k2:[v21]]`. Law `printMD_inj`: two maps whose keys and
values hold no space, `:`, `[` or `]` (and no empty value), keys distinct, print equal only if they
are equal up to the order of keys. The `Sprintf` triple over the map's heap representation is
requested of 2a (grpc's `outMD` gives the map): `notes/specs-only/verify/repair-client-core.md`.
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

/-- **`fmt.Sprintf("%+v", m)` of a `map[string][]string` modelled by `md`** (assumed: Go's
printing, keys sorted). -/
opaque printMD (md : List (GoString × List GoString)) : GoString := []

/-- A metadata map whose printing is unambiguous. -/
def mdPrintable (md : List (GoString × List GoString)) : Prop :=
  (md.map (·.1)).Nodup ∧ ∀ kv ∈ md, ∀ s ∈ kv.1 :: kv.2, s ≠ [] ∧
    ∀ b ∈ s, b ≠ W8 32 ∧ b ≠ W8 58 ∧ b ≠ W8 91 ∧ b ≠ W8 93

/-- **Printing is injective on printable maps** (up to the order of keys: Go sorts them). -/
def printMD_inj.spec : Prop := ∀ md md' : List (GoString × List GoString),
  mdPrintable md → mdPrintable md' → printMD md = printMD md' → md.Perm md'

/-- **A printed map is never empty** (`map[` … `]`; re-review S-b: `streamKeyFromCtx` maps "no
metadata" to `""`, which no printed map equals). -/
def printMD_ne_nil.spec : Prop := ∀ md : List (GoString × List GoString), printMD md ≠ []

end Fmt
end EtcdGrove
end Perennial
