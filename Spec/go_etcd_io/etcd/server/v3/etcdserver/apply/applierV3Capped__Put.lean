/-
`(*applierV3Capped).Put(r)` (`capped.go:33-35`): `ErrNoSpace`.

**Users.** `uberApplier.dispatch` through the chain (promoted methods of the outer layers).

**Proof sketch.** Immediate.

**Changes** from `specs-ref`'s `applierV3Capped__Put.lean`: the old per-mode chain predicates (`apply.chainRes`, `kvOwnPre`) restated over `applierAt`, `stAt` and `layersStep`

**Margin.** None.
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

/-- **`Put` at the applierV3Capped layer**: the layers' step (the result `resMatch`). -/
def applierV3Capped.Put.spec : Prop :=
  ∀ (p : Loc) (b aa : Loc) (ls : List Layer) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (u : GoString) (rev : w64) (rq : Loc) (op : IrrOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Capped.ty) #p) (Layer.capped :: ls) b aa ∗
      beAt b mc γ γc R ∗
      stAt b σ ∗
      aiAt aa u rev ∗
      reqMsgAt rq op ∗ ⌜(∃ x, op = .req (.put x)) ∧ op.ok⌝ ∗
      R ∗
      threadTok }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Capped.ty @!! go!"Put")) (Val #rq))
  {{ (resp : Loc) (trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      R ∗ threadTok ∗ aiAt aa u rev ∗ ∃ σ' res res', ⌜layersStep mc σ u (uint.nat rev) op (Layer.capped :: ls) σ' res ∧ resMatch op false res res'⌝ ∗
      stAt b σ' ∗ replyAt γ op res' (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.PutResponse.ty) #resp) err ∗ TraceUtil.traceOpt trace }}

end spec

end Apply
end EtcdGrove
end Perennial
