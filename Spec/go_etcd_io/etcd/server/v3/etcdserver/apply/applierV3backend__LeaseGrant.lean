/-
`(*applierV3backend).LeaseGrant(r)` (`backend.go:83-92`): the lessor's `Grant(id, ttl)` (the TTL raised to the member's minimum).

**Users.** `uberApplier.dispatch` through the chain (promoted methods of the outer layers).

**Proof sketch.** 3c's `lessor.Grant` at the writer's `Lease.lessorState γl n ls` (`stAt`'s
`lessorSt`) with the backend's hook (`Lease.beHook ls.be Pk f ∗ Pre ∗ Mvcc.hookRun Pk f Pre Q ∗ (Q ={⊤}=∗
Pk ∗ Post)`, from `R`: provisional, 4a's): `ErrLeaseNotFound` (id `0`), `ErrLeaseTTLTooLarge`,
`ErrLeaseExists`, or the state `ls.grant id l (grantTTL c ttl)` at `n + 1` (`grantTTL c ttl = max ttl
mc.minLeaseTTL`, `lessorOk`'s `c.minTTL`); `l.ID`, `l.TTL()` (`lessorAt_obj`, `Lease.TTL.spec`);
`newHeader`.

**Changes** from `specs-ref`'s `applierV3backend__LeaseGrant.lean`: the old triple over the chain's `AEnv`, the mvcc log and the write tokens (`putPre`, `kvPostF`, `mPostW`, ...) restated over the model state (`stAt`, `layersStep`): any auth mode, leases, compaction

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

/-- **`LeaseGrant` at the applierV3backend layer**: the layers' step (exact). -/
def applierV3backend.LeaseGrant.spec : Prop :=
  ∀ (p : Loc) (b aa : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (rq : Loc) (op : IrrOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty) #p) [Layer.backend] p aa ∗
      beAt p mc γ γc R ∗
      stAt p σ ∗
      reqMsgAt rq op ∗ ⌜(∃ i t, op = .req (.leaseGrant i t)) ∧ op.ok⌝ ∗
      R ∗
      threadTok }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty @!! go!"LeaseGrant")) (Val #rq))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      R ∗ threadTok ∗ ∃ σ' res, ⌜layersStep mc σ [] 0 op [Layer.backend] σ' res⌝ ∗ stAt p σ' ∗
      replyAt γ op res (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.LeaseGrantResponse.ty) #resp) err }}

end spec

end Apply
end EtcdGrove
end Perennial
