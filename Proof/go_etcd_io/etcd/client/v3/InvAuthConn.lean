/-
**The client's Auth API over gRPC** (the auth plan's E2h, 2026-10-26): the vocabulary of the
admin calls `examples/authkv`'s `SetUp` makes (`client/v3/auth.go`'s `authClient`, `retry.go`'s
`retryAuthClient`, the generated stub `api/etcdserverpb/rpc_grpc.pb.go`'s `authClient`), the
shape of the KV path's (`InvKVConn.lean`). Lean-first (no Rocq counterpart); the design is in
`notes/decisions.md`, "E2h of the auth plan".

**Messages** (`ProtoMsg` instances): a request's model is what its wire message carries
(`UserAddW`: the name and the password; a grant: the user and the role; a role's name; a
permission grant: the role's name and the permission `auth.PermW`; `AuthEnable`: nothing), the
sender's message the owned struct (its `Options`, its `Perm`, read-only), the decoded copy the
auth store's own predicates (`auth.userAddReqIs`, `auth.userGrantRoleReqIs`, `auth.roleAddReqIs`,
`auth.roleGrantPermissionReqIs`, `auth/Requests.lean`), what the server's handlers read. A
response's model is nothing (`Unit`): `SetUp` reads none of the replies.

**The calls** are specified, as the KV calls, for any spec `Spec` the server registered for the
method (`isGrpcRpcs addr method Spec`) and any caller's postcondition `Q`, with a persistent
precondition `□ ▷ Spec m Q` (the retry interceptor's contract for any number of attempts,
`etcdInterceptorOk`): an admin request may be delivered several times (the interceptor resends a
call that failed before it was sent, or with an expired token), so the client asks nothing of
the server's spec but that it can be run again (D29's write-once mode is the KV methods' only,
`kvMethod`). What the server's Auth service guarantees is the spec `Spec`: a premise of the
callers (`examples/authkv`'s `SetUp`), for the server's side to discharge
(`notes/decisions.md`, "E2h of the auth plan").

**The objects**: `authStubAt ac conn` (the generated `*authClient` on `conn`), `retryAuthAt rac
conn` (a `*retryAuthClient` over one), `authObjAt api addr` (the client's `*authClient` over one,
with its call options: what `NewAuth` returns, the client's `Auth` field, `isNewClient`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.server.v3.auth.Requests

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil errCellOk errCellOk_nil)

section model

/-- A `*pb.AuthUserAddRequest` as the wire carries it: the user's name and password. -/
structure UserAddW where
  name : GoString
  pw : GoString

end model

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-! ## The Auth service's messages -/

/-- The `Options` of a user addition the client sends: a read-only `UserAddOptions` with
`NoPassword` false (`auth.go`'s `UserAdd`). -/
def userOptsFalse (o : Loc) : IProp GF := auth.userOptsAt o false

instance userOptsFalse_persistent (o : Loc) : Persistent (userOptsFalse (GF := GF) o) := by
  unfold userOptsFalse auth.userOptsAt; infer_instance

/-- **A `*pb.AuthUserAddRequest`** on the wire (see the file header). -/
def pbAuthUserAddRequest : ProtoMsg GF where
  ty := etcdserverpb.AuthUserAddRequest.ty
  M := UserAddW
  send inp m := iprop(∃ req : etcdserverpb.AuthUserAddRequest, inp ↦ req ∗
    ⌜req.Name' = m.name ∧ req.Password' = m.pw ∧ req.HashedPassword' = []⌝ ∗
    userOptsFalse req.Options')
  recv r m := iprop(auth.userAddReqIs r m.name ∗
    structFieldRef etcdserverpb.AuthUserAddRequest go!"Password" r ↦□ m.pw)
  recv_persistent _ _ := by unfold auth.userAddReqIs; infer_instance
  blank l := iprop(l ↦ (zero_val etcdserverpb.AuthUserAddRequest))
  own l := iprop(∃ v : etcdserverpb.AuthUserAddRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.AuthUserGrantRoleRequest`** on the wire: the user and the role. -/
def pbAuthUserGrantRoleRequest : ProtoMsg GF where
  ty := etcdserverpb.AuthUserGrantRoleRequest.ty
  M := GoString × GoString
  send inp m := iprop(∃ req : etcdserverpb.AuthUserGrantRoleRequest, inp ↦ req ∗
    ⌜req.User' = m.1 ∧ req.Role' = m.2⌝)
  recv r m := auth.userGrantRoleReqIs r m.1 m.2
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.AuthUserGrantRoleRequest))
  own l := iprop(∃ v : etcdserverpb.AuthUserGrantRoleRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.AuthRoleAddRequest`** on the wire: the role's name. -/
def pbAuthRoleAddRequest : ProtoMsg GF where
  ty := etcdserverpb.AuthRoleAddRequest.ty
  M := GoString
  send inp m := iprop(∃ req : etcdserverpb.AuthRoleAddRequest, inp ↦ req ∗ ⌜req.Name' = m⌝)
  recv r m := auth.roleAddReqIs r m
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.AuthRoleAddRequest))
  own l := iprop(∃ v : etcdserverpb.AuthRoleAddRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.AuthRoleGrantPermissionRequest`** on the wire: the role's name and the permission
(its type as the `int32` the message carries, its key and range end). -/
def pbAuthRoleGrantPermissionRequest : ProtoMsg GF where
  ty := etcdserverpb.AuthRoleGrantPermissionRequest.ty
  M := GoString × auth.PermW
  send inp m := iprop(∃ req : etcdserverpb.AuthRoleGrantPermissionRequest, inp ↦ req ∗
    ⌜req.Name' = m.1⌝ ∗ auth.ownPermW req.Perm' m.2)
  recv r m := auth.roleGrantPermissionReqIs r m.1 (some m.2)
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.AuthRoleGrantPermissionRequest))
  own l := iprop(∃ v : etcdserverpb.AuthRoleGrantPermissionRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.AuthEnableRequest`** on the wire: nothing. -/
def pbAuthEnableRequest : ProtoMsg GF where
  ty := etcdserverpb.AuthEnableRequest.ty
  M := Unit
  send inp _ := iprop(∃ req : etcdserverpb.AuthEnableRequest, inp ↦ req)
  recv r _ := iprop(⌜r ≠ null⌝)
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.AuthEnableRequest))
  own l := iprop(∃ v : etcdserverpb.AuthEnableRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.AuthUserAddResponse`** on the wire: nothing the client reads. -/
def pbAuthUserAddResponse : ProtoMsg GF where
  ty := etcdserverpb.AuthUserAddResponse.ty
  M := Unit
  send _ _ := iprop(True)
  recv _ _ := iprop(True)
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.AuthUserAddResponse))
  own l := iprop(∃ v : etcdserverpb.AuthUserAddResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.AuthUserGrantRoleResponse`** on the wire: nothing the client reads. -/
def pbAuthUserGrantRoleResponse : ProtoMsg GF where
  ty := etcdserverpb.AuthUserGrantRoleResponse.ty
  M := Unit
  send _ _ := iprop(True)
  recv _ _ := iprop(True)
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.AuthUserGrantRoleResponse))
  own l := iprop(∃ v : etcdserverpb.AuthUserGrantRoleResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.AuthRoleAddResponse`** on the wire: nothing the client reads. -/
def pbAuthRoleAddResponse : ProtoMsg GF where
  ty := etcdserverpb.AuthRoleAddResponse.ty
  M := Unit
  send _ _ := iprop(True)
  recv _ _ := iprop(True)
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.AuthRoleAddResponse))
  own l := iprop(∃ v : etcdserverpb.AuthRoleAddResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.AuthRoleGrantPermissionResponse`** on the wire: nothing the client reads. -/
def pbAuthRoleGrantPermissionResponse : ProtoMsg GF where
  ty := etcdserverpb.AuthRoleGrantPermissionResponse.ty
  M := Unit
  send _ _ := iprop(True)
  recv _ _ := iprop(True)
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.AuthRoleGrantPermissionResponse))
  own l := iprop(∃ v : etcdserverpb.AuthRoleGrantPermissionResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.AuthEnableResponse`** on the wire: nothing the client reads. -/
def pbAuthEnableResponse : ProtoMsg GF where
  ty := etcdserverpb.AuthEnableResponse.ty
  M := Unit
  send _ _ := iprop(True)
  recv _ _ := iprop(True)
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.AuthEnableResponse))
  own l := iprop(∃ v : etcdserverpb.AuthEnableResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-! ## What an admin call returns -/

/-- **What a unary admin call returns** to the client (every layer's postcondition: the stub's,
the retry client's, the `*authClient`'s): `nil` with the run's knowledge `Q ()`; or a client error
that grpc's `status` accepts (`statusErrOk`) and no response (as `putCallOut`). -/
def authCallOut (Q : Unit → IProp GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ Q ()) ∨
    (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗ statusErrOk err ∗ errCellOk err))

/-! ## The objects -/

/-- **The generated stub `ac`** (`*etcdserverpb.authClient`) on the connection `conn`. -/
def authStubAt (ac conn : Loc) : IProp GF :=
  iprop(structFieldRef etcdserverpb.authClient go!"cc" ac ↦□
    (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #conn :
      GoInterface))

instance authStubAt_persistent (ac conn : Loc) : Persistent (authStubAt (GF := GF) ac conn) := by
  unfold authStubAt; infer_instance

/-- **The `*retryAuthClient` `rac`** over a stub on `conn`. -/
def retryAuthAt (rac conn : Loc) : IProp GF :=
  iprop(∃ ac : Loc, structFieldRef go_etcd_io.etcd.client.v3.retryAuthClient go!"ac" rac ↦□
      (interface.mkOk (go.GoType.PointerType etcdserverpb.authClient.ty) #ac : GoInterface) ∗
    authStubAt ac conn)

instance retryAuthAt_persistent (rac conn : Loc) : Persistent (retryAuthAt (GF := GF) rac conn) := by
  unfold retryAuthAt; infer_instance

/-- **The client's `*authClient` `api`** (what `NewAuth` returns) over a `*retryAuthClient` on a
connection to the server at `addr`, with the client's call options. -/
def authObjAt (api : Loc) (addr : List GoString) : IProp GF :=
  iprop(∃ (rac conn : Loc) (sl : GoSlice),
    structFieldRef go_etcd_io.etcd.client.v3.authClient go!"remote" api ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryAuthClient.ty) #rac :
        GoInterface) ∗
    retryAuthAt rac conn ∗ isEtcdConn conn addr ∗
    structFieldRef go_etcd_io.etcd.client.v3.authClient go!"callOpts" api ↦□ sl ∗ callOptsAt sl)

instance authObjAt_persistent (api : Loc) (addr : List GoString) :
    Persistent (authObjAt (GF := GF) api addr) := by
  unfold authObjAt; infer_instance

end defs

end EtcdGrove
end Perennial
