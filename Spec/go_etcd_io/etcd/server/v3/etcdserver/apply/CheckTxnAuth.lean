/-
`apply.CheckTxnAuth(as, ai, lessor, rt)` (`auth.go:110-112`, = `checkTxnPermission`): the
permission checks of a transaction (its comparisons' reads, each operation of both branches,
nested ones included; a put's lease keys), each through the auth store (`isOpPermitted`), in order,
the first error returned.

**Users.** `EtcdServer.Txn` (`v3_server.go:355`, 2c's `EtcdServer.Txn.spec`: a serializable
read-only transaction checked through `doSerialize` at the member's own stores, concurrently with
the apply thread). Snippet `examples/specreq/apply/auth.go` (`ReqCheckTxnAuth`).

**Proof sketch.** `checkTxnPermission.spec` (the body is that call) at `permReads_reader` (from
`Auth.authStoreAt st γ γa ∗ Auth.authLb γa i0`: `A = emp`, `L = false`, `C = chkPost γa i0 u rev`):
for a read-only transaction (`t.readonly`: only ranges in both branches) `RequestOp.checks` has no
lease check, so `L = false` is allowed and the lessor is never called. Each `IsRangePermitted` is
3d's reader triple, reported by `Auth.checkPost` at its recorded states. The checks are **not
atomic**: each is reported at its own states (a member's store may apply an auth change between
two), as W0's reads' checks (`State.permittedSince`, `deniedSince`, from the lower bound).

**Changes** from `specs-ref`'s `CheckTxnAuth.lean` (two modes through `isAuthStore … on`,
`authApplyErrIs`, the lessor's view): one spec, over 3d's recorded states (2c's need, item 3); the
old spec's "`nil` with auth off" is a recorded state with auth off.

**Margin.** Each check is reported at its own recorded states from the lower bound `i0` (3d's
`checkPost`: the flag, the backend, the cache, the revision); one state for all the passing checks is
not claimed (`nonissues/etcd-auth-revision-before-visible.md`: W0's `permittedSince` admits it).

**Integration (I5).** Premise `t.readonly` (2c's only call is for a read-only transaction,
`v3_server.go`); the provisional `lessorRead le` dropped (a read-only transaction never reaches the
lessor, which a reader could only call with a reader token of 3c's, `lessorReaders`); the sketch
goes through `checkTxnPermission.spec` at `permReads_reader` (per-check reports).

**Integration (I5), the empty end** (the coordinator's decision): premise `endsDecoded rt`: every
range end of the message is `nil` or non-empty, as gRPC's decoding gives (2c discharges it from the
handler's unmarshalled request). A non-`nil` empty end (the in-process adapter only) is checked as
the key alone but read from the key on (`nonissues/etcd-auth-empty-range-end-point-check.md`), so
the post is false there; the premise excludes it.

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
      Auth.authStoreAt st γ γa ∗ Auth.authLb γa i0 ∗ ⌜t.readonly⌝ ∗
      Auth.authInfoAt ai dq u rev ∗ EtcdWire.txnReqOwn rt dq' t ∗ endsDecoded rt ∗ threadTok }}
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
