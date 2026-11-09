/-
`(*applierV3backend).Put(r)` (`backend.go:50-52`): `txn.Put(ctx, lg, lessor, kv, p)`.

**Users.** `uberApplier.dispatch` through the chain (promoted methods of the outer layers).

**Proof sketch.** 3b's `Txn.Put.spec` with `context.TODO()`: the store's writer update pinned at
`σ₀` (`σ₀.kv = σ.kv`, `pending = []`: from `stAt`'s `kvSt`, provisional, 3b's S6), `Mvcc.isMvcc`,
`mvccBackend` and `txnWriter B Pk Post` (the backend's hook under `R`) from `beAt`'s `kvOk`, the
lessor's `lessorState` (`lessorSt`, `leasesLive`); its answer `putAns pr σ.kv ls.table` is `opStep`'s;
the lessor's new state `evsLs` is the store's attachment; the reply with the header's revision.

**Changes** from `specs-ref`'s `applierV3backend__Put.lean`: the old triple over the chain's `AEnv`, the mvcc log and the write tokens (`putPre`, `kvPostF`, `mPostW`, ...) restated over the model state (`stAt`, `layersStep`): any auth mode, leases, compaction.
verify-round (A9 F2): `lessorSt` (inside `stAt`, from `optsSt`) now states `Txn.leasesLive`; the
statement is unchanged.

**Margin.** The header's other fields (cluster, member, term, leader) any.
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

/-- **`Put` at the applierV3backend layer**: the layers' step (exact). -/
def applierV3backend.Put.spec : Prop :=
  ∀ (p : Loc) (b aa : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (rq : Loc) (op : IrrOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty) #p) [Layer.backend] p aa ∗
      beAt p mc γ γc R ∗
      stAt p σ ∗
      reqMsgAt rq op ∗ ⌜(∃ x, op = .req (.put x)) ∧ op.ok⌝ ∗
      R ∗
      threadTok }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty @!! go!"Put")) (Val #rq))
  {{ (resp : Loc) (trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      R ∗ threadTok ∗ ∃ σ' res, ⌜layersStep mc σ [] 0 op [Layer.backend] σ' res⌝ ∗ stAt p σ' ∗
      replyAt γ op res (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.PutResponse.ty) #resp) err ∗ TraceUtil.traceOpt trace }}

end spec

end Apply
end EtcdGrove
end Perennial
