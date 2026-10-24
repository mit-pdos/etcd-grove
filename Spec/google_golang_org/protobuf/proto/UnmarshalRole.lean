/-
`proto.Unmarshal` on an `authpb.Role`: the trust boundary (`google.golang.org/protobuf` is
names-only; the encoding `auth.roleEncode` is opaque, `auth/Buckets.lean`), as `proto.Unmarshal` on
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `proto.Unmarshal(b, m)` of the encoding of the record `x` into the `*authpb.Role` at `p`
(whatever it held) makes it hold `x` (`auth.ownRoleX`: a fresh message the caller owns, its byte fields read-only
slices, its `KeyPermission` slice owned with its capacity and its permission messages owned, the message's internal fields as it
likes; the auth plan's S4c, 2026-10-24: Go's decoder allocates them) and returns `nil`. -/
abbrev proto.UnmarshalRole.spec : Prop :=
  ∀ (b : GoSlice) (x : auth.RoleRec) (p : Loc) (v : authpb.Role) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
      b ↦*{dq} auth.roleEncode x ∗ p ↦ v }}
    (App (App (Val (@! proto.Unmarshal)) (Val #b))
      (Val #(interface.mkOk (go.GoType.PointerType authpb.Role.ty) #p)))
  {{ RET #(GoInterface.nil); b ↦*{dq} auth.roleEncode x ∗ auth.ownRoleX p x }}

end spec

end EtcdGrove
end Perennial
