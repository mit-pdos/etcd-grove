/-
`proto.Unmarshal` into any message type at the bytes: the trust boundary
(`google.golang.org/protobuf` is names-only), stated over a `PbType` (`InvProto.lean`). Lean-first.
-/
module

public import Proof.google_golang_org.protobuf.proto.InvProto

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `proto.Unmarshal(b, m)` of any bytes into a zero `*T` the caller owns returns an error, or `nil`
and the `*T` holding some `m` of which the bytes are an encoding; `b` is read, not kept. Bytes that
are an encoding of some message decode: the error is `nil`.

Against protobuf-go v1.36.11 (`proto/decode.go`): `Unmarshal` resets the message, then decodes;
it copies `bytes` fields out of the buffer (the default options do not alias it). -/
abbrev proto.UnmarshalPb.spec : Prop :=
  ∀ (T : PbType GF) (b : GoSlice) (bs : List w8) (dq : DFrac) (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ b ↦*{dq} bs ∗
      T.blank l }}
    (App (App (Val (@! google_golang_org.protobuf.proto.Unmarshal)) (Val #b))
      (Val #(interface.mkOk (go.GoType.PointerType T.ty) #l)))
  {{ (err : GoInterface), RET #err; b ↦*{dq} bs ∗ ⌜(∃ m : T.M, T.wire m bs) → err = GoInterface.nil⌝ ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ m : T.M, T.dec l m ∗ ⌜T.wire m bs⌝) }}

end spec

end EtcdGrove
end Perennial
