/-
`(*uberApplier).dispatch(r, shouldApplyV3)` (`uber_applier.go:93-212`): the membership requests in both modes; `nil` without `shouldApplyV3`; else the request through the current chain's method (an alarm through `uberApplier.Alarm`), into a fresh `Result`; the deferred metrics and warnings.

**Users.** the chain's `Apply` (`authApplierV3.Apply`'s `applyFunc`, the method value `a.dispatch`).

**Proof sketch.** The membership methods (`applierV3backend.ClusterVersionSet.spec`, `ClusterMemberAttrSet.spec` with `memberUpd`, `DowngradeInfoSet.spec`, through the outer layers' promoted methods); the chain's method for the request's kind (the layer specs: `layersStep` at `chainLayers σ`, the result's `resMatch`), `uberApplier.Alarm.spec`; `replyAt_result` for the `Result`'s fields; `txn.ApplySecObserve`, `WarnOfExpensiveRequest`, `WarnOfFailedRequest` (3b's: logging only; `errors.Is` on `ar.Err`). The `default` branch's `lg.Panic` is excluded by `ir.op.ok` (the decoded request has a known field).

`nextOk` (the next state's auth reached and fitting; `Authenticate`'s index) is passed down to
the backend's admin methods (3d's `AdminTriple`; integration I5).

**Changes** from `specs-ref`'s file of the same name: restated over the new vocabulary (`beAt`, `stAt`, `applierAt`, the model state); one spec for every mode.

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

/-- **Dispatch the request** past the administrator check: `irrStep`'s other cases. -/
def uberApplier.dispatch.spec : Prop :=
  ∀ (p b aa r : Loc) (ir : Irr) (sk v3 : Bool) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (Qm : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ uberAt p b aa mc γ γc R ∗ uberChain p (chainLayers σ) ∗ stAt b σ ∗
      aiAt aa ir.user ir.revW ∗ wrapperAt r ir sk ∗
      ⌜ir.op.ok ∧ (sk = true → ir.op.isTxn = true) ∧
        (ir.op.needAdmin = true → adminErr σ.auth ir.user = none)⌝ ∗
      nextOk γ R ir.op (fun σ' => ∃ res, irrStep mc σ ir v3 σ' res) ∗
      memberUpd γc ir.op Qm ∗ R ∗ threadTok }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier.ty @!! go!"dispatch")) (Val #r)) (Val #v3))
  {{ (ar : Loc), RET #ar; R ∗ threadTok ∗ Qm ∗ (∃ u rv, aiAt aa u rv) ∗
      ∃ σ' res, ⌜irrStep mc σ ir v3 σ' res ∧
        (v3 = false → ir.op.isMembership = false → ar = null)⌝ ∗ uberChain p (chainLayers σ') ∗ stAt b σ' ∗
        resultAt γ ar ir sk res }}

end spec

end Apply
end EtcdGrove
end Perennial
