/-
`proto.MarshalOptions.MarshalAppend` of any message type, with the zero options: the trust
boundary (`google.golang.org/protobuf` is names-only), stated over a `PbType` (`InvProto.lean`).
Lean-first.
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

/-- `o.MarshalAppend(b, m)`, `o` the zero `MarshalOptions`, of a read-only-for-good `*T` holding `m`,
a message that `marshals`, appends its encoding (`Marshal`'s, `pbEnc`) to `b` and returns the
result and `nil`; if it fits `b`'s capacity, in `b`'s array (the same pointer and capacity).

Against protobuf-go v1.36.11 (`proto/encode.go`): `MarshalAppend` is `Marshal` appending to `b`
(Go's `append`: in place within the capacity). -/
abbrev proto.MarshalAppendPb.spec : Prop :=
  ∀ (T : PbType GF) (o : Loc) (dq : DFrac) (l : Loc) (m : T.M) (b : GoSlice) (xs : List w8),
  T.marshals m →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
      o ↦{dq} (zero_val google_golang_org.protobuf.proto.MarshalOptions) ∗ T.ro l m ∗
      b ↦* xs ∗ ownSliceCap w8 b (DFrac.own 1) }}
    (App (App (Val (o @!! go.GoType.PointerType google_golang_org.protobuf.proto.MarshalOptions.ty
      @!! go!"MarshalAppend")) (Val #b)) (Val #(interface.mkOk (go.GoType.PointerType T.ty) #l)))
  {{ (b' : GoSlice), RET (PairV #b' #(GoInterface.nil));
      o ↦{dq} (zero_val google_golang_org.protobuf.proto.MarshalOptions) ∗
      b' ↦* (xs ++ pbEnc T.ty l) ∗ ownSliceCap w8 b' (DFrac.own 1) ∗
      ⌜T.wire m (pbEnc T.ty l) ∧
        ((xs ++ pbEnc T.ty l).length ≤ uint.nat b.cap → b'.ptr = b.ptr ∧ b'.cap = b.cap)⌝ }}

end spec

end EtcdGrove
end Perennial
