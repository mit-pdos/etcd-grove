/-
`apply.CheckTxnAuth(as, ai, lessor, rt)` (`auth.go:110-112`, = `checkTxnPermission`): the
permission checks of a transaction (its comparisons' reads, each operation of both branches,
nested ones included; a put's lease keys), each through the auth store (`isOpPermitted`), in order,
the first error returned.

**Users.** `EtcdServer.Txn` (`v3_server.go:355`, 2c's `EtcdServer.Txn.spec`: a serializable
read-only transaction checked through `doSerialize` at the member's own stores, concurrently with
the apply thread). Snippet `examples/specreq/apply/auth.go` (`ReqCheckTxnAuth`).

**Proof sketch.** `checkTxnPermission.spec`: each `IsRangePermitted` / `IsPutPermitted` /
`IsDeleteRangePermitted` (3d's, with `authRead`: `nil` only if the check passes at an auth state
the cluster reached, `σa.authTables`; its error `ErrUserEmpty`, `ErrAuthOldRevision` or
`ErrPermissionDenied`), `checkLeasePuts` (3c's `Lookup`, `Keys` with `lessorRead`: any answer; the
`IsAdminPermitted` shortcut). The checks are **not atomic**: each passes at its own reached auth
state (a member's store may apply an auth change between two; a token minted at another member may
carry a revision this member has not reached), so the post says each pair is permitted at some auth
state up to one the cluster reached, as W0's reads' checks (`State.authTables`).

**Changes** from `specs-ref`'s `CheckTxnAuth.lean` (two modes through `isAuthStore … on`,
`authApplyErrIs`, the lessor's view): one spec, over the cluster's reached states (2c's need, item
3); the old spec's "`nil` with auth off" is the reached state with auth off.

**Margin.** Nothing about the leases' keys (`checkLeasePuts` reads the lessor's keys at no single
state: a transaction with puts is not checked through this path by etcd's request path; the apply's
own check is `authErr`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Apply

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The permission check of a transaction**: `nil` only if each pair it reads or writes is
permitted to the auth info's user at some auth state of the cluster's history up to a reached
state; else the first check's error (`ErrUserEmpty`, `ErrAuthOldRevision`, `ErrPermissionDenied`). -/
def CheckTxnAuth.spec : Prop :=
  ∀ (ast le : GoInterface) (ai rt : Loc) (γ : Cluster) (u : GoString) (rev : w64) (t : TxnReq)
    (dq : DFrac),
  let who : Principal := if u = [] then none else some u
  let ps := (RequestOp.txn t.compare t.success t.failure).perms
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      authRead ast γ ∗ lessorRead le ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦□ u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦□ rev ∗
      EtcdWire.txnReqOwn rt dq t ∗ threadTok }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.CheckTxnAuth))
      (Val #ast)) (Val #ai)) (Val #le)) (Val #rt))
  {{ (err : GoInterface), RET #err; EtcdWire.txnReqOwn rt dq t ∗ threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ σa, etcdLb γ σa ∗
          ⌜∀ p ∈ ps, ∃ a ∈ σa.authTables, ({ σa with auth := a } : State).permits who [p] []⌝) ∨
       (∃ e, ⌜EtcdServer.srvErrOf err e ∧
          (e = .userEmpty ∨ e = .authOldRevision ∨ e = .permissionDenied)⌝)) }}

end spec

end Apply
end EtcdGrove
end Perennial
