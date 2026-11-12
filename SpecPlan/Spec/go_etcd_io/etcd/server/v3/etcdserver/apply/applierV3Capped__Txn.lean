/-
`(*applierV3Capped).Txn(rt, skipRangeExecution)` (`capped.go:37-42`): `ErrNoSpace` if the transaction puts (`Cost > 0`), else the base's.

**Users.** `uberApplier.dispatch` through the chain (promoted methods of the outer layers).

**Proof sketch.** `BackendQuota.Cost` (2e's: requested exact, `cappedRefused`: positive iff a put anywhere); the base's.

**Changes** from `specs-ref`'s `applierV3Capped__Txn.lean`: the old per-mode chain predicates (`apply.chainRes`, `kvOwnPre`) restated over `applierAt`, `stAt` and `layersStep`

**Margin.** None.
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

/-- **`Txn` at the applierV3Capped layer**: the layers' step (the result `resMatch`). -/
def applierV3Capped.Txn.spec : Prop :=
  ∀ (p : Loc) (b aa : Loc) (ls : List Layer) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (u : GoString) (rev : w64) (rq : Loc) (op : IrrOp) (sk : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Capped.ty) #p) (Layer.capped :: ls) b aa ∗
      beAt b mc γ γc R ∗
      stAt b σ ∗
      aiAt aa u rev ∗
      reqMsgAt rq op ∗ ⌜(∃ x, op = .req (.txn x)) ∧ op.ok⌝ ∗
      R ∗
      threadTok }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Capped.ty @!! go!"Txn")) (Val #rq)) (Val #sk))
  {{ (resp : Loc) (trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      R ∗ threadTok ∗ aiAt aa u rev ∗ ∃ σ' res res', ⌜layersStep mc σ u (uint.nat rev) op (Layer.capped :: ls) σ' res ∧ resMatch op sk res res'⌝ ∗
      stAt b σ' ∗ replyAt γ op res' (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.TxnResponse.ty) #resp) err ∗ TraceUtil.traceOpt trace }}

end spec

end Apply
end EtcdGrove
end Perennial
