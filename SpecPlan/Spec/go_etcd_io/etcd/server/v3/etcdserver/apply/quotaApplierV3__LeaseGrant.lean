/-
`(*quotaApplierV3).LeaseGrant(r)` (`quota.go:54-61`): the quota's `Available` before, then the backend's; `ErrNoSpace` if the backend was over its quota and the operation succeeded (**the write stays applied**).

**Users.** `uberApplier.dispatch` through the chain (promoted methods of the outer layers).

**Proof sketch.** `BackendQuota.Available` (2e's `ServerStorage`, any answer); the embedded backend applier's spec.

**Changes** from `specs-ref`'s `quotaApplierV3__LeaseGrant.lean`: no `backendUnderQuota` (the over-quota answer is the result's margin, `resMatch`); the old per-mode chain predicates (`apply.chainRes`, `kvOwnPre`) restated over `applierAt`, `stAt` and `layersStep`

**Margin.** `ErrNoSpace` after a write (`nonissues/etcd-apply-quota-nospace-after-write.md`).
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

/-- **`LeaseGrant` at the quotaApplierV3 layer**: the layers' step (the result `resMatch`). -/
def quotaApplierV3.LeaseGrant.spec : Prop :=
  ∀ (p : Loc) (b aa : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (rq : Loc) (op : IrrOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.quotaApplierV3.ty) #p) [Layer.quota, Layer.backend] b aa ∗
      beAt b mc γ γc R ∗
      stAt b σ ∗
      reqMsgAt rq op ∗ ⌜(∃ i t, op = .req (.leaseGrant i t)) ∧ op.ok⌝ ∗
      R ∗
      threadTok }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.quotaApplierV3.ty @!! go!"LeaseGrant")) (Val #rq))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      R ∗ threadTok ∗ ∃ σ' res res', ⌜layersStep mc σ [] 0 op [Layer.quota, Layer.backend] σ' res ∧ resMatch op false res res'⌝ ∗
      stAt b σ' ∗ replyAt γ op res' (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.LeaseGrantResponse.ty) #resp) err }}

end spec

end Apply
end EtcdGrove
end Perennial
