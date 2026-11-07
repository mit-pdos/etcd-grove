/-
`proto.MarshalOptions.MarshalAppend` of a registered message type at its wire content, with the
zero options (per-type models, stage A, CP2): the trust boundary, over a registered pair
(`pbModelOf`, `InvProto.lean`). Next to today's `proto.MarshalAppendPb.spec` (CP3 rewires the
users). Lean-first.
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

/-- **`o.MarshalAppend(b, m)`, `o` the zero `MarshalOptions`, of a frozen `*T` of a registered type
holding the wire content `c`**, which marshals, with the result's length below `2^47`: appends `c`'s
encoding (`pbEncC I c`) to `b` and returns the result and `nil`; if it fits `b`'s capacity, in `b`'s
array (the same pointer and capacity).

Against protobuf-go v1.36.11 (`proto/encode.go:153`, `:174`): `MarshalAppend` is `Marshal`
appending to `b` (Go's `append`: in place within the capacity); the premise is the Scope's
(`[v6]` §4, unchanged from revision 5), keeping the grown allocation below `maxAlloc`. -/
abbrev proto.MarshalAppendPbC.spec : Prop :=
  ∀ (I : PbTypeC GF), pbModelOf GF I.data.ty = some I →
  ∀ (o : Loc) (dq : DFrac) (l : Loc) (c : I.data.C) (b : GoSlice) (xs : List w8),
  I.data.marshals (I.data.modelOf c) → xs.length + I.data.size c < 2 ^ 47 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
      o ↦{dq} (zero_val google_golang_org.protobuf.proto.MarshalOptions) ∗ I.data.roC l c ∗
      b ↦* xs ∗ ownSliceCap w8 b (DFrac.own 1) }}
    (App (App (Val (o @!! go.GoType.PointerType google_golang_org.protobuf.proto.MarshalOptions.ty
      @!! go!"MarshalAppend")) (Val #b))
      (Val #(interface.mkOk (go.GoType.PointerType I.data.ty) #l)))
  {{ (b' : GoSlice), RET (PairV #b' #(GoInterface.nil));
      o ↦{dq} (zero_val google_golang_org.protobuf.proto.MarshalOptions) ∗
      b' ↦* (xs ++ pbEncC I c) ∗ ownSliceCap w8 b' (DFrac.own 1) ∗
      ⌜(xs ++ pbEncC I c).length ≤ uint.nat b.cap → b'.ptr = b.ptr ∧ b'.cap = b.cap⌝ }}

end spec

end EtcdGrove
end Perennial
