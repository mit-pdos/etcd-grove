/-
`binary.Write(w, binary.BigEndian, v)` of a value whose underlying type is `uint8`: the trust
boundary (`Write`'s reflection path, untranslatable), stated over `w`'s `Write`. Lean-first.
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

/-- `binary.Write(w, binary.BigEndian, v)` of a value of a type `t` whose underlying type is `uint8`
(the msgappv2 encoder's frame tag, a `msgAppV2Type`) makes one `w.Write` of a fresh slice of the byte
and returns that call's error. For a named `t` (the frame tag) this is `Write`'s reflection path,
not its fast path: `intDataSize`'s type switch matches `uint8` itself only, so `Write` computes
`dataSize` (1) through `reflect`, encodes the byte with `encoder.value` (a `reflect.Uint8` kind) and
makes the one `w.Write(buf)` (`binary.go`, `Write`). Hence still the trust boundary, where
`binary.Write` of a `uint64` is proved (`Proof/encoding/binary/WriteUint64.lean`). -/
abbrev binary.WriteUint8.spec : Prop :=
  ∀ (t : go.GoType) [t ↓u go.uint8] (wi : GoInterfaceOk) (v : w8) (P : IProp GF)
    (Q : w64 → GoInterface → IProp GF),
    ⊢ (□ ∀ sl : GoSlice, {{ sl ↦* [v] ∗ P }}
        (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #sl))
        {{ (n : w64) (err : GoInterface), RET (PairV #n #err); Q n err }}) -∗
      {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ P }}
        (App (App (App (Val (@! _root_.Perennial.encoding.binary.Write))
          (Val #(GoInterface.ok wi))) (Val #bigEndianOrder))
          (Val #(interface.mkOk t #v)))
      {{ (err : GoInterface), RET #err; ∃ n, Q n err }}

end spec

end EtcdGrove
end Perennial
