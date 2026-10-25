/-
**The Auth service's entry points** (the auth plan's A3, the API layer, 2026-10-24;
`notes/auth-plan.md`): the server's `AuthEnable`, ..., `RoleList` (`v3_server.go`, the
`Authenticator` interface the gRPC `AuthServer` calls), each a `raftRequest` on the request with
its field set. Lean-first (no Rocq counterpart).

**The requests, purely** (`irrAuthEnable`, ..., `irrAuthenticate am`): `apply.irrEmpty` with the one
field, as `irrPut` (`InvProposer.lean`).

**The proposal as a contract** (`authRaftOk s ctx rq T P Q`): `raftRequest`'s spec
(`EtcdServer__raftRequest.lean`) is for a request the proposal path's model covers (`reqPropOk`:
the KV requests and the monitors', `plainCover`), and an auth request is not one (the apply
thread's generic proofs do not cover its dispatch, `KVModelDefs.lean`): so an entry point's spec
takes `raftRequest` on its request as a contract, over the caller's `P`, answering `Q` of the
response (a `*T`, the apply package's response type for the request, which the entry point
asserts) or of the error, an error the apply package's facts describe (`applyErrIs`). What the
entry point adds is nothing of auth: the header's principal is `processInternalRaftRequestOnce`'s
(`AuthInfoFromCtx`), and the admin check of the request is the apply layer's for that principal
(`apply.adminPass`, the auth plan's A3, the apply layer). Making `raftRequest.spec` cover the auth
requests (then the contract is its instance) is the apply thread's business (the plan's S4, E).

**An entry point's outcome** (`authEntryOut Q resp err`): the applied response with `Q resp nil`,
or `nil` and the error with `Q null err`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthGuard

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

/-! ## The requests, purely -/

/-- `&pb.InternalRaftRequest{AuthEnable: r}`. -/
def irrAuthEnable : apply.IRRModel := { apply.irrEmpty with authEnable := true }
/-- `&pb.InternalRaftRequest{AuthDisable: r}`. -/
def irrAuthDisable : apply.IRRModel := { apply.irrEmpty with authDisable := true }
/-- `&pb.InternalRaftRequest{AuthStatus: r}`. -/
def irrAuthStatus : apply.IRRModel := { apply.irrEmpty with authStatus := true }
/-- `&pb.InternalRaftRequest{Authenticate: r}` for `r` holding `am`. -/
def irrAuthenticate (am : apply.AuthenticateModel) : apply.IRRModel :=
  { apply.irrEmpty with authenticate := some am }
/-- `&pb.InternalRaftRequest{AuthUserAdd: r}` for `r` naming `name`. -/
def irrUserAdd (name : GoString) : apply.IRRModel := { apply.irrEmpty with authUserAdd := some name }
/-- `&pb.InternalRaftRequest{AuthUserDelete: r}`. -/
def irrUserDelete : apply.IRRModel := { apply.irrEmpty with authUserDelete := true }
/-- `&pb.InternalRaftRequest{AuthUserGet: r}` for `r` naming `name`. -/
def irrUserGet (name : GoString) : apply.IRRModel := { apply.irrEmpty with authUserGet := some name }
/-- `&pb.InternalRaftRequest{AuthUserChangePassword: r}`. -/
def irrUserChangePassword : apply.IRRModel :=
  { apply.irrEmpty with authUserChangePassword := true }
/-- `&pb.InternalRaftRequest{AuthUserGrantRole: r}`. -/
def irrUserGrantRole : apply.IRRModel := { apply.irrEmpty with authUserGrantRole := true }
/-- `&pb.InternalRaftRequest{AuthUserRevokeRole: r}`. -/
def irrUserRevokeRole : apply.IRRModel := { apply.irrEmpty with authUserRevokeRole := true }
/-- `&pb.InternalRaftRequest{AuthUserList: r}`. -/
def irrUserList : apply.IRRModel := { apply.irrEmpty with authUserList := true }
/-- `&pb.InternalRaftRequest{AuthRoleList: r}`. -/
def irrRoleList : apply.IRRModel := { apply.irrEmpty with authRoleList := true }
/-- `&pb.InternalRaftRequest{AuthRoleAdd: r}` for `r` naming `name`. -/
def irrRoleAdd (name : GoString) : apply.IRRModel := { apply.irrEmpty with authRoleAdd := some name }
/-- `&pb.InternalRaftRequest{AuthRoleDelete: r}`. -/
def irrRoleDelete : apply.IRRModel := { apply.irrEmpty with authRoleDelete := true }
/-- `&pb.InternalRaftRequest{AuthRoleGet: r}` for `r` naming `name`. -/
def irrRoleGet (name : GoString) : apply.IRRModel := { apply.irrEmpty with authRoleGet := some name }
/-- `&pb.InternalRaftRequest{AuthRoleGrantPermission: r}`. -/
def irrRoleGrantPermission : apply.IRRModel :=
  { apply.irrEmpty with authRoleGrantPermission := true }
/-- `&pb.InternalRaftRequest{AuthRoleRevokePermission: r}`. -/
def irrRoleRevokePermission : apply.IRRModel :=
  { apply.irrEmpty with authRoleRevokePermission := true }

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## The proposal as a contract -/

/-- **`s.raftRequest(ctx, p)` on the request `rq`** (persistent; see the file header): for a
`*pb.InternalRaftRequest` `p` holding `rq` but for its header (`irrNoHdrIs`, with the header
field owned), over the caller's `P`: an error the apply package's facts describe, and on `nil` a
response of the type `*T` with `Q` of it, else no response and `Q null` of the error. -/
def authRaftOk (s : Loc) (ctx : GoInterfaceOk) (rq : apply.IRRModel) (T : go.GoType)
    (P : IProp GF) (Q : Loc → GoInterface → IProp GF) : IProp GF :=
  iprop(∀ p : Loc,
    {{ P ∗ irrNoHdrIs p rq ∗
        (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"raftRequest"))
        (Val #(GoInterface.ok ctx))) (Val #p))
    {{ (resp err : GoInterface), RET (PairV #resp #err); applyErrIs err ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ l : Loc,
            ⌜resp = interface.mkOk (go.GoType.PointerType T) #l⌝ ∗ Q l GoInterface.nil) ∨
         (⌜resp = GoInterface.nil ∧ err ≠ GoInterface.nil⌝ ∗ Q null err)) }})

instance authRaftOk_persistent (s : Loc) (ctx : GoInterfaceOk) (rq : apply.IRRModel)
    (T : go.GoType) (P : IProp GF) (Q : Loc → GoInterface → IProp GF) :
    Persistent (authRaftOk s ctx rq T P Q) := by
  unfold authRaftOk; infer_instance

/-- **An entry point's outcome**: the applied response with `Q resp nil`, or `nil` and the error
with `Q null err`. -/
def authEntryOut (Q : Loc → GoInterface → IProp GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ Q resp GoInterface.nil) ∨
    (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ Q null err))

end defs

end EtcdGrove
end Perennial
