/-
`io.WriteString(w, s)` (Go's `io/io.go`): `w.WriteString(s)` if `w`'s dynamic type is an
`io.StringWriter` (the type assertion `w.(StringWriter)`, `go.typeSetContains`), otherwise
`w.Write([]byte(s))` on a fresh slice holding `s`'s bytes; it returns what that call returns. The
caller gives both contracts (`stringWriteOk`), from its `P` to its `Q`; only the one the dynamic
type selects is used. Pending: Perennial translates `io.WriteString` as a name only at the pin
(`notes/perennial-changes.md`); the Links that reach it take this spec as a hypothesis (`section
links_pending`). Lean-first (phase 7 S5, the chunked writer, 2026-11-24).
-/
module

public import Perennial.Proof.io

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- What `io.WriteString` needs of the writer `ii` for the string `s` (see the file header): its
`WriteString(s)`, if its dynamic type has it, and otherwise its `Write` of a slice holding `s`'s
bytes, given back, each from `P` to `Q`. -/
def io.stringWriteOk (ii : GoInterfaceOk) (s : GoString) (P : IProp GF)
    (Q : w64 → GoInterface → IProp GF) : IProp GF :=
  iprop((⌜go.typeSetContains ii.ty _root_.Perennial.io.StringWriter.ty = true⌝ -∗ P -∗
      WP (App (Val #(methods ii.ty go!"WriteString" ii.v)) (Val #s))
        {{ v, ∃ (n : w64) (err : GoInterface), ⌜v = PairV #n #err⌝ ∗ Q n err }}) ∧
    (⌜go.typeSetContains ii.ty _root_.Perennial.io.StringWriter.ty = false⌝ -∗
      ∀ sl : GoSlice, sl ↦* s -∗ P -∗
      WP (App (Val #(methods ii.ty go!"Write" ii.v)) (Val #sl))
        {{ v, ∃ (n : w64) (err : GoInterface), ⌜v = PairV #n #err⌝ ∗ Q n err }}))

/-- See the file header. -/
abbrev io.WriteString.spec : Prop :=
  ∀ (ii : GoInterfaceOk) (s : GoString) (P : IProp GF) (Q : w64 → GoInterface → IProp GF),
  {{ P ∗ io.stringWriteOk ii s P Q }}
    (App (App (Val (@! _root_.Perennial.io.WriteString)) (Val #(interface.ok ii))) (Val #s))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); Q n err }}

end spec

end EtcdGrove
end Perennial
