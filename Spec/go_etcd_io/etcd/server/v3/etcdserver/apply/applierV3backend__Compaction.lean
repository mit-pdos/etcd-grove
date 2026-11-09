/-
`(*applierV3backend).Compaction(r)` (`backend.go:66-81`): mvcc's `Compact(trace, rev)`, then the current revision for the header.

**Users.** `uberApplier.dispatch` through the chain (promoted methods of the outer layers).

**Proof sketch.** 3e's `Compact` (the compaction revision moved, a channel closed once the physical compaction is done) and `Range` (no error at the current revision).

**Changes** from `specs-ref`'s `applierV3backend__Compaction.lean`: the old triple over the chain's `AEnv`, the mvcc log and the write tokens (`putPre`, `kvPostF`, `mPostW`, ...) restated over the model state (`stAt`, `layersStep`): any auth mode, leases, compaction

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

/-- **`Compaction` at the applierV3backend layer**: the layers' step (exact). -/
def applierV3backend.Compaction.spec : Prop :=
  ∀ (p : Loc) (b aa : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (rq : Loc) (op : IrrOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty) #p) [Layer.backend] p aa ∗
      beAt p mc γ γc R ∗
      stAt p σ ∗
      reqMsgAt rq op ∗ ⌜(∃ r ph, op = .req (.compact r ph)) ∧ op.ok⌝ ∗
      R ∗
      threadTok }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty @!! go!"Compaction")) (Val #rq))
  {{ (resp : Loc) (ch : Loc) (trace : Loc) (err : GoInterface), RET (PairV (PairV (PairV #resp #ch) #trace) #err);
      R ∗ threadTok ∗ ∃ σ' res, ⌜layersStep mc σ [] 0 op [Layer.backend] σ' res⌝ ∗ stAt p σ' ∗
      replyAt γ op res (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse.ty) #resp) err ∗ TraceUtil.traceOpt trace ∗ (⌜ch = null⌝ ∨ Read.recvAny ch) }}

end spec

end Apply
end EtcdGrove
end Perennial
