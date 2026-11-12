/-
`checkTxnPermission(as, ai, lessor, rt)` (`auth.go:128-138`): the checks of a transaction: its comparisons' reads, then both branches

**Users.** the auth applier (the apply thread: `permReads_writer`, `C` exact at the stores' one state) and `CheckTxnAuth` (the request path: `permReads_reader`, `C` 3d's `checkPost` from a lower bound, no lease check)

**Proof sketch.** 3d's `IsRangePermitted` per comparison; `checkTxnReqsPermission.spec` twice.

**Changes** from `specs-ref`'s file of the same name: one spec for both callers, parametric in how each check is reported (`permReads`' `C`); the old two-mode `isAuthStore … on` and `authApplyErrIs` gone
recheck (RR3): the `endsDecoded` premise dropped, `txnReqOwn` carries `endsOk`.
verify-round, second pass (grpc-v3rpc's P-F2): `endsDecoded` was 3h's share-holding `EtcdServerPb.endsDecoded` (no
longer a persistent opaque), given back in the post.

**Margin.** None.

**Integration (I5).** `permReads` takes the auth info and a per-check report `C` in place of a
set of states `S` (3d's reader check names three views, not one state), and `L` (lease checks
allowed: the request path holds no lessor reader token).

**Integration (I5), the empty end.** Every range end `nil` or non-empty (a non-`nil` empty
`RangeEnd` is checked as the key alone while mvcc reads from the key on:
`nonissues/etcd-auth-empty-range-end-point-check.md`): since the recheck (RR3), `txnReqOwn`'s own
`endsOk` (3h's `txnReqOwn_msgAt`), no separate premise.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult

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

/-- **The checks of a transaction: its comparisons' reads, then both branches** each check reported by `C`: `checksOut`. -/
def checkTxnPermission.spec : Prop :=
  ∀ (ast le : GoInterface) (ai : Loc) (dq : DFrac) (u : GoString) (rev : w64) (A : IProp GF)
    (L : Bool)
    (C : Check → GoInterface → IProp GF) (rt : Loc) (t : TxnReq) (dq' : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ permReads ast le u rev A L C ∗ A ∗ ⌜L = false → ∀ c ∈ (RequestOp.checks (RequestOp.txn t.compare t.success t.failure)), c.isLease = false⌝ ∗  ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev ∗ EtcdWire.txnReqOwn rt dq' t ∗ threadTok }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnPermission)) (Val #ast)) (Val #ai)) (Val #le)) (Val #rt))
  {{ (err : GoInterface), RET #err; A ∗ ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Username"] ↦{dq} u ∗
      ai.[go_etcd_io.etcd.server.v3.auth.AuthInfo, go!"Revision"] ↦{dq} rev ∗ threadTok ∗ EtcdWire.txnReqOwn rt dq' t ∗
      checksOut C (RequestOp.checks (RequestOp.txn t.compare t.success t.failure)) err }}

end spec

end Apply
end EtcdGrove
end Perennial
