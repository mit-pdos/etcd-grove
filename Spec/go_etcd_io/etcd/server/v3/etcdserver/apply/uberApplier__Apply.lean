/-
`(*uberApplier).Apply(r, shouldApplyV3)` (`uber_applier.go:261-268`): the current chain's `Apply`
with `dispatch` (promoted down to the auth applier's: its lock, the header's auth info, the
administrator check, then `dispatch`).

**Users.** `apply.Apply` (through the `UberApplier` interface: `isUber_apply` is this spec in the
method form). Snippets `examples/specreq/apply/` (all).

**Proof sketch.** `smAt_unfold`: `uberChain p (chainLayers σ)` (`p.applyV3 ↦ v`, `applierAt v
(chainLayers σ) b aa`) and `stAt b σ`. `v.Apply(r, v3, a.dispatch)`: the corrupt and capped
appliers' `Apply` are the embedded one's, down to `authApplierV3.Apply.spec` (the mutex gives
`aiAt aa ir.user ir.authRev`; the administrator check `adminErr`, whose refusal `&Result{Err}` is
`irrStep`'s first case: 2c's `applyResult` of `.err e`); its base's `Apply` (the quota applier's,
promoted, then `applierV3backend.Apply.spec`) calls the function value, whose triple is
`uberApplier.dispatch.spec` (with `aiAt`, `uberChain`, `stAt`, the membership update, `R`):
`irrStep`'s other cases, the chain re-chosen after an alarm. `smAt_unfold` back.

**Changes** from `specs-ref`'s `uberApplier__Apply.lean` (its 25 premises: `kvOwnPre`, `certPreV`,
`rqOk`, `cmpAdmit`, `ltHalf`, `everOwn`, `grantFresh`, `revokeOwn`, `restReqOk`, `cmpOwn`, ...;
two auth modes): one triple over the model state, any request kind, any mode; the answer is
`irrStep`'s, a function of the state; no `backendUnderQuota`.

**Margin.** The result's answer is `resMatch`'s (an alarm list's order, a skipped transaction, the
quota's `ErrNoSpace`); the trace is any.
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

/-- **Apply `ir`**: the state machine moves by the apply's step (`irrStep`, at the member's
configuration), the result carries its answer (`resultAt`), the membership update fired. -/
def uberApplier.Apply.spec : Prop :=
  ∀ (p : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (r : Loc)
    (ir : Irr) (sk v3 : Bool) (σ : State) (Qm : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      isUber (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier.ty) #p) mc γ γc R ∗
      wrapperAt r ir sk ∗ ⌜ir.op.ok ∧ (sk = true → ir.op.isTxn = true)⌝ ∗
      smAt (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier.ty) #p) σ ∗
      memberUpd γc ir.op Qm ∗ R ∗ threadTok }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier.ty @!!
      go!"Apply")) (Val #r)) (Val #v3))
  {{ (ar : Loc), RET #ar; R ∗ threadTok ∗ Qm ∗ ∃ σ' res, ⌜irrStep mc σ ir v3 σ' res⌝ ∗
      smAt (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier.ty) #p) σ' ∗
      resultAt γ ar ir sk res }}

end spec

end Apply
end EtcdGrove
end Perennial
