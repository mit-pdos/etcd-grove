/-
`(*applierV3backend).Txn(rt, skipRangeExecution)` (`backend.go:62-64`): `txn.Txn(ctx, lg, rt, sharedBuf, kv, lessor, skip)`.

**Users.** `uberApplier.dispatch` through the chain (promoted methods of the outer layers).

**Proof sketch.** 3b's `txn.Txn` (`TxnRun` at the store; with `skip` the ranges' answers empty,
`skipRanges`): its `⌜txnSafe t⌝` from `op.ok`'s `txnAdmitted`, its `targetOk` from `t.valid`'s
`validSort`, its `leasesLive σ₀.kv.store ls` from `stAt`'s `lessorSt`, the writer's resources from
`kvSt`/`kvOk`.

**Changes** from `specs-ref`'s `applierV3backend__Txn.lean`: the old triple over the chain's `AEnv`, the mvcc log and the write tokens (`putPre`, `kvPostF`, `mPostW`, ...) restated over the model state (`stAt`, `layersStep`): any auth mode, leases, compaction.
verify-round (A9 F1, F2): `op.ok` now carries `Txn.txnSafe` (`txnAdmitted`), `stAt` `leasesLive`
(`lessorSt`); the statement is unchanged.

**Margin.** The header's other fields (cluster, member, term, leader) any.
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

/-- **`Txn` at the applierV3backend layer**: the layers' step (exact). -/
def applierV3backend.Txn.spec : Prop :=
  ∀ (p : Loc) (b aa : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (rq : Loc) (op : IrrOp) (sk : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty) #p) [Layer.backend] p aa ∗
      beAt p mc γ γc R ∗
      stAt p σ ∗
      reqMsgAt rq op ∗ ⌜(∃ x, op = .req (.txn x)) ∧ op.ok⌝ ∗
      R ∗
      threadTok }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty @!! go!"Txn")) (Val #rq)) (Val #sk))
  {{ (resp : Loc) (trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      R ∗ threadTok ∗ ∃ σ' res, ⌜layersStep mc σ [] 0 op [Layer.backend] σ' res⌝ ∗ stAt p σ' ∗
      replyAt γ op res (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.TxnResponse.ty) #resp) err ∗ TraceUtil.traceOpt trace }}

end spec

end Apply
end EtcdGrove
end Perennial
