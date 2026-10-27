/-
`proto.Unmarshal` on an `authpb.User`: the trust boundary (`google.golang.org/protobuf` is
names-only; the encoding `auth.userEncode` is opaque, `auth/Buckets.lean`), as `proto.Unmarshal` on
`mvccpb.KeyValue` (`Unmarshal.lean`). The auth plan's S1 (2026-10-23). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Buckets
public import GeneratedProof.google_golang_org.protobuf.proto

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.protobuf go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `proto.Unmarshal(b, m)` of the encoding of the record `x` into the `*authpb.User` at `p`
(whatever it held) makes it hold `x` (`auth.ownUserX`: a fresh message the caller owns, its byte fields read-only
slices, its `Roles` slice owned with its capacity, the message's internal fields as it
likes; the auth plan's S4c, 2026-10-24: Go's decoder allocates them) and returns `nil`. -/
abbrev proto.UnmarshalUser.spec : Prop :=
  ∀ (b : GoSlice) (x : auth.UserRec) (p : Loc) (v : authpb.User) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
      b ↦*{dq} auth.userEncode x ∗ p ↦ v }}
    (App (App (Val (@! proto.Unmarshal)) (Val #b))
      (Val #(interface.mkOk (go.GoType.PointerType authpb.User.ty) #p)))
  {{ RET #(GoInterface.nil); b ↦*{dq} auth.userEncode x ∗ auth.ownUserX p x }}

end spec

end EtcdGrove
end Perennial
