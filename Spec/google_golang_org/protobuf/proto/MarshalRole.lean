/-
`proto.Marshal` on an `authpb.Role`: the trust boundary (`google.golang.org/protobuf` is
names-only; the encoding `auth.roleEncode` is opaque, `auth/Buckets.lean`), the twin of
`proto.Unmarshal` on the message (`UnmarshalRole.lean`), as `proto.MarshalUser`
(`MarshalUser.lean`). auth-schema-srv A3 (2026-11-17; Draft `notes/auth-schema-srv-a3-draft.md`):
not yet an axiom (no `Proof/` file until the attack). Its Go tests:
`examples/authpbmarshal/marshal_test.go`.
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

/-- `proto.Marshal(r)` of the `*authpb.Role` at `p` holding the record `x` (`auth.ownRole`: the
message owned, its name and `KeyPermission` read-only, no unknown fields; each permission a
read-only non-nil message without unknown fields, its size cache in an invariant, `auth.ownPermS`)
returns a fresh slice of the encoding `auth.roleEncode x` and `nil`; the message still holds `x`.

Why faithful (as `proto.MarshalUser`; schema's `UnsafePutRole`, `storage/schema/auth_roles.go:51-62`,
calls it and panics on an error): the fields in number order (`name` 1, every permission 2, each
a nested message: `permType` 1 as a varint when not 0, any `int32` (an open enum: 7 and -1 come
back, `TestRoleRoundTrip`), `key` 2, `range_end` 3, nil and empty alike), in the list's order, the
same permission message twice written twice; no string field, so no error: the nested permissions
are non-nil (`ownPermS`; a nil element is refused) and each is checked against the size Marshal has
just recomputed for it (`codec_field.go:163-173`); a permission's size is bounded by its two byte
slices, which memory holds. The writes: the top message's `state` and size cache (owned), each
permission's size cache (its invariant: `TestMarshalWritesNestedSizeCache`,
`TestStaleSizeCacheIgnored`; a permission shared by two roles marshaled at once,
`TestConcurrentSharedNested`); no nested `state` (`TestStateWrites`). Go tests
`TestDeterministicRecord`, `TestRoleRoundTrip`, `TestFreshResult`. -/
abbrev proto.MarshalRole.spec : Prop :=
  ∀ (p : Loc) (x : auth.RoleRec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ auth.ownRole p x }}
    (App (Val (@! proto.Marshal))
      (Val #(interface.mkOk (go.GoType.PointerType authpb.Role.ty) #p)))
  {{ (d : GoSlice), RET (PairV #d #(GoInterface.nil));
      auth.ownRole p x ∗ d ↦* auth.roleEncode x ∗ ownSliceCap w8 d (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
