/-
`(*applierV3Corrupt).LeaseGrant(r)` (`corrupt.go:49-51`): `ErrCorrupt`.

**Users.** `uberApplier.dispatch` through the chain (promoted methods of the outer layers).

**Proof sketch.** Immediate.

**Changes** from `specs-ref`'s `applierV3Corrupt__LeaseGrant.lean`: the old per-mode chain predicates (`apply.chainRes`, `kvOwnPre`) restated over `applierAt`, `stAt` and `layersStep`

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

/-- **`LeaseGrant` at the applierV3Corrupt layer**: the layers' step (the result `resMatch`). -/
def applierV3Corrupt.LeaseGrant.spec : Prop :=
  ∀ (p : Loc) (b aa : Loc) (ls : List Layer) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (u : GoString) (rev : w64) (rq : Loc) (op : IrrOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt.ty) #p) (Layer.corrupt :: ls) b aa ∗
      beAt b mc γ γc R ∗
      stAt b σ ∗
      aiAt aa u rev ∗
      reqMsgAt rq op ∗ ⌜(∃ i t, op = .req (.leaseGrant i t)) ∧ op.ok⌝ ∗
      R ∗
      threadTok }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt.ty @!! go!"LeaseGrant")) (Val #rq))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      R ∗ threadTok ∗ aiAt aa u rev ∗ ∃ σ' res res', ⌜layersStep mc σ u (uint.nat rev) op (Layer.corrupt :: ls) σ' res ∧ resMatch op false res res'⌝ ∗
      stAt b σ' ∗ replyAt γ op res' (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.LeaseGrantResponse.ty) #resp) err }}

end spec

end Apply
end EtcdGrove
end Perennial
