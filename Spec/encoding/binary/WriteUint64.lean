/-
`binary.Write(w, binary.BigEndian, v)` of a `uint64`, stated over `w`'s `Write`. Proved over
Perennial's translation of `Write` (`Proof/encoding/binary/WriteUint64.lean`; stdlib4, 2026-11-21:
until then names-only, as `Write` falls back on `reflect`). Lean-first.
-/
module

public import Proof.encoding.binary.Defs

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

/-- `binary.Write(w, binary.BigEndian, v)` of a `uint64` makes one `w.Write` of a fresh slice of
`v`'s eight big-endian bytes and returns that call's error (Go 1.27 `binary.go`, `Write`'s fast
path: `intDataSize`, `encodeFast`, `w.Write(bs)`). Stated over that call's triple, `P` to `Q`. -/
abbrev binary.WriteUint64.spec : Prop :=
  ∀ (wi : GoInterfaceOk) (v : w64) (P : IProp GF) (Q : w64 → GoInterface → IProp GF),
    ⊢ (□ ∀ sl : GoSlice, {{ sl ↦* u64Be v ∗ P }}
        (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #sl))
        {{ (n : w64) (err : GoInterface), RET (PairV #n #err); Q n err }}) -∗
      {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ P }}
        (App (App (App (Val (@! _root_.Perennial.encoding.binary.Write))
          (Val #(GoInterface.ok wi))) (Val #bigEndianOrder))
          (Val #(interface.mkOk go.uint64 #v)))
      {{ (err : GoInterface), RET #err; ∃ n, Q n err }}

end spec

end EtcdGrove
end Perennial
