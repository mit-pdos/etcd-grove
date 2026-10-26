/-
`proto.Marshal` of any message type at the bytes: the trust boundary (`google.golang.org/protobuf`
is names-only), stated over a `PbType` (`InvProto.lean`). Lean-first.
-/
module

public import Proof.google_golang_org.protobuf.proto.InvProto

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

/-- `proto.Marshal(m)` of a read-only-for-good `*T` holding `m`, a message that `marshals`, returns
a fresh slice of its encoding, an encoding of `m`, and `nil`.

Against protobuf-go v1.36.11 (`proto/encode.go`): `Marshal` fails only on a missing required field,
invalid UTF-8 in a proto3 string or a message changed while it is encoded, which the instance's
`marshals` and `ro` exclude; an empty encoding is a non-nil empty slice. -/
abbrev proto.MarshalPb.spec : Prop :=
  ∀ (T : PbType GF) (l : Loc) (m : T.M), T.marshals m →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ T.ro l m }}
    (App (Val (@! google_golang_org.protobuf.proto.Marshal))
      (Val #(interface.mkOk (go.GoType.PointerType T.ty) #l)))
  {{ (d : GoSlice), RET (PairV #d #(GoInterface.nil));
      d ↦* pbEnc T.ty l ∗ ownSliceCap w8 d (DFrac.own 1) ∗ ⌜T.wire m (pbEnc T.ty l)⌝ }}

end spec

end EtcdGrove
end Perennial
