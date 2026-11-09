/-
`(*applierV3backend).LeaseRevoke(r)` (`backend.go:94-97`): the lessor's `Revoke(id)` (its keys deleted at one revision).

**Users.** `uberApplier.dispatch` through the chain (promoted methods of the outer layers).

**Proof sketch.** 3c's `lessor.Revoke` at the writer's `lessorState`, with `ls.rd ≠ func.nil` and the
deleter's contract `Lease.rdOk γl ls.rd n ls P D Q` (3e's `Mvcc.mvccDeleter_rdOk` until the first
snapshot, 2d's closure after: inside `stAt`, the apply thread's): `ErrLeaseNotFound`, or the lease's
keys deleted at one revision (`lessorSt`'s attachment: W0's `State.attachedKVs`, so `State.revoke`)
and the lease removed; `newHeader`.

**Changes** from `specs-ref`'s `applierV3backend__LeaseRevoke.lean`: the old triple over the chain's `AEnv`, the mvcc log and the write tokens (`putPre`, `kvPostF`, `mPostW`, ...) restated over the model state (`stAt`, `layersStep`): any auth mode, leases, compaction

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

/-- **`LeaseRevoke` at the applierV3backend layer**: the layers' step (exact). -/
def applierV3backend.LeaseRevoke.spec : Prop :=
  ∀ (p : Loc) (b aa : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (rq : Loc) (op : IrrOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty) #p) [Layer.backend] p aa ∗
      beAt p mc γ γc R ∗
      stAt p σ ∗
      reqMsgAt rq op ∗ ⌜(∃ i, op = .req (.leaseRevoke i)) ∧ op.ok⌝ ∗
      R ∗
      threadTok }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty @!! go!"LeaseRevoke")) (Val #rq))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      R ∗ threadTok ∗ ∃ σ' res, ⌜layersStep mc σ [] 0 op [Layer.backend] σ' res⌝ ∗ stAt p σ' ∗
      replyAt γ op res (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.LeaseRevokeResponse.ty) #resp) err }}

end spec

end Apply
end EtcdGrove
end Perennial
