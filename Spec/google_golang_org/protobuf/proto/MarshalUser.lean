/-
`proto.Marshal` on an `authpb.User`: the trust boundary (`google.golang.org/protobuf` is
names-only; the encoding `auth.userEncode` is opaque, `auth/Buckets.lean`), the twin of
`proto.Unmarshal` on the message (`UnmarshalUser.lean`), as `proto.Marshal` on `mvccpb.KeyValue`
(`Marshal.lean`). auth-schema-srv A3 (2026-11-17; Draft `notes/auth-schema-srv-a3-draft.md`): an axiom
(`Proof/google_golang_org/protobuf/proto/MarshalUser.lean`), attacked independently
(`notes/axiom-review/auth-a3-marshal.md`). Its Go tests:
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

/-- `proto.Marshal(u)` of the `*authpb.User` at `p` holding the record `x` (`auth.ownUser`: the
message owned, its byte fields and `Roles` read-only, no unknown fields; its `Options` nil or a
read-only message with its size cache in an invariant, `auth.userOptsIs`), every role valid UTF-8,
returns a fresh slice of the encoding `auth.userEncode x` and `nil`; the message still holds `x`
(protobuf-go stores the message's `state` and its size cache, which `ownUser` leaves free).

Why faithful (protobuf-go v1.36.12, the fork's `authpb` at the etcd pin 8c28a4296f; schema's
`UnsafePutUser`, `storage/schema/auth_users.go:40-46`, calls it and panics on an error):
- the result: `proto.Marshal` (`proto/encode.go:105-116`) runs `marshal` (`:173-207`): a `Size`
  pass, a fresh buffer of that capacity (`growcap` from 0: exactly the size), then the fast-path
  `marshal` with `UseCachedSize`, appending the known fields in number order (`name` 1, `password`
  2, every role 3, `options` 4 when not nil), then the message's unknown fields (nil here). A field
  is a function of the record: empty and nil byte fields and role lists encode alike (both absent),
  every role is written (an empty one too), a nil `Options` is absent and a non-nil one present
  (tag, length, `no_password` 1 when true, then its unknown fields verbatim). Go tests
  `TestDeterministicRecord`, `TestNilVsEmptyOptions`, `TestOptionsUnknownRoundTrip`; the result
  shares nothing with the message, `TestFreshResult`; an empty encoding is the shared zero-length
  `emptyBuf[:]` (`:141-146`), capacity 0, so `ownSliceCap` is empty there too.
- the error: a proto3 `repeated string` is checked (`internal/impl/codec_gen.go:5250-5260`,
  `errInvalidUTF8`): hence the premise (`TestInvalidUTF8Role`;
  `nonissues/etcd-auth-putuser-invalid-utf8-role.md`). Nothing else fails: no required fields
  (proto3), the only nested message (`Options`) is checked against its own size
  (`codec_field.go:163-173`), which Marshal has just recomputed and which only protobuf-go writes
  (the next item); the top-level size only sizes the buffer (an `int` the code could wrap only for
  an encoding of `2^63` bytes, which no memory holds: the model's allocation never fails, so any
  such run ends in Go's out-of-memory exit, never a wrong result).
- the writes: `User.ProtoReflect` stores the message info in the top message's `state` (once,
  atomically), and the `Size` pass stores `size + 1` (or `0` past `2^31 - 2`) in the size cache of
  the top message and of the `Options` (`internal/impl/encode.go:63-125`, `atomic.StoreInt32`); the
  `marshal` pass reads them with `atomic.LoadInt32` (`:47-60`). A nested message's `state` is not
  touched (`TestStateWrites`). The `Options`' cache is in an invariant (`userOptsIs`): its value is
  never relied on (`TestStaleSizeCacheIgnored`: garbage in any cache gives the same bytes), and
  concurrent Marshals of users sharing one `Options` store the same value
  (`TestConcurrentSharedNested`, `-race`: no report, every result right; etcd shares it:
  `UserChangePassword`/`UserGrantRole`/`UserRevokeRole`/`RoleDelete` copy the stored message's
  `Options` pointer, `auth/store.go:527,633,746`). -/
abbrev proto.MarshalUser.spec : Prop :=
  ∀ (p : Loc) (x : auth.UserRec),
  (∀ r ∈ x.roles, utf8Valid r) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ auth.ownUser p x }}
    (App (Val (@! proto.Marshal))
      (Val #(interface.mkOk (go.GoType.PointerType authpb.User.ty) #p)))
  {{ (d : GoSlice), RET (PairV #d #(GoInterface.nil));
      auth.ownUser p x ∗ d ↦* auth.userEncode x ∗ ownSliceCap w8 d (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
