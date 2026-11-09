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

**Margin.** The leases' keys: only the failing key's check (`chkPost`: `checkLeasePuts` reads the
lessor's keys at no single state; the request path checks no put through here). Each check is
reported at its own recorded states from the lower bound `i0` (3d's `checkPost`: the flag, the
backend, the cache); one state for all the passing checks needs 3d's check to report the store's
revision against `rev` (all passing checks then see the token's revision: requested,
`req/go_etcd_io_etcd_server_v3_auth.md`, "from 3a (round 1)").

**Round 1.** Restated over 3d's `authStoreAt`/`authLb`/`checkPost` (W0's read rule: a lower bound,
the states a pass or a denial was made at), in place of the provisional `authRead` and the
reached-`authTables` summary.
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

/-- **The permission checks of a transaction** (`RequestOp.checks`, in order) from the lower bound
`i0`: `nil` and every check passed at its recorded states, or the error of the first failing check
with the states it failed at, the earlier ones passed. -/
def CheckTxnAuth.spec : Prop :=
  ∀ (st ai rt : Loc) (le : GoInterface) (γ : Cluster) (γa : Auth.AuthNames) (i0 : Nat)
    (u : GoString) (rev : w64) (t : TxnReq) (dq dq' : DFrac),
  let cs := RequestOp.checks (RequestOp.txn t.compare t.success t.failure)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      Auth.authStoreAt st γ γa ∗ Auth.authLb γa i0 ∗ lessorRead le ∗
      Auth.authInfoAt ai dq u rev ∗ EtcdWire.txnReqOwn rt dq' t ∗ threadTok }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.CheckTxnAuth))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty) #st)))
      (Val #ai)) (Val #le)) (Val #rt))
  {{ (err : GoInterface), RET #err; Auth.authInfoAt ai dq u rev ∗ EtcdWire.txnReqOwn rt dq' t ∗
      threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ [∗list] c ∈ cs, chkPost γa i0 u rev c GoInterface.nil) ∨
       (∃ (i : Nat) (c : Check), ⌜cs[i]? = some c ∧ err ≠ GoInterface.nil⌝ ∗
          chkPost γa i0 u rev c err ∗ [∗list] c' ∈ cs.take i, chkPost γa i0 u rev c' GoInterface.nil)) }}

end spec

end Apply
end EtcdGrove
end Perennial
