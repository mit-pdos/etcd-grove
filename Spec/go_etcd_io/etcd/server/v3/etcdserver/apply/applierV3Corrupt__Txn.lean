/-
`(*applierV3Corrupt).Txn(rt, skipRangeExecution)` (`corrupt.go:41-43`): `ErrCorrupt`.

**Users.** `uberApplier.dispatch` through the chain (promoted methods of the outer layers).

**Proof sketch.** Immediate.

**Changes** from `specs-ref`'s `applierV3Corrupt__Txn.lean`: the old per-mode chain predicates (`apply.chainRes`, `kvOwnPre`) restated over `applierAt`, `stAt` and `layersStep`

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

/-- **`Txn` at the applierV3Corrupt layer**: the layers' step (the result `resMatch`). -/
def applierV3Corrupt.Txn.spec : Prop :=
  ∀ (p : Loc) (b aa : Loc) (ls : List Layer) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (u : GoString) (rev : w64) (rq : Loc) (op : IrrOp) (sk : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt.ty) #p) (Layer.corrupt :: ls) b aa ∗
      beAt b mc γ γc R ∗
      stAt b σ ∗
      aiAt aa u rev ∗
      reqMsgAt rq op ∗ ⌜(∃ x, op = .req (.txn x)) ∧ op.ok⌝ ∗
      R ∗
      threadTok }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt.ty @!! go!"Txn")) (Val #rq)) (Val #sk))
  {{ (resp : Loc) (trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      R ∗ threadTok ∗ aiAt aa u rev ∗ ∃ σ' res res', ⌜layersStep mc σ u (uint.nat rev) op (Layer.corrupt :: ls) σ' res ∧ resMatch op sk res res'⌝ ∗
      stAt b σ' ∗ replyAt γ op res' (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.TxnResponse.ty) #resp) err ∗ EtcdServer.traceAt trace }}

end spec

end Apply
end EtcdGrove
end Perennial
