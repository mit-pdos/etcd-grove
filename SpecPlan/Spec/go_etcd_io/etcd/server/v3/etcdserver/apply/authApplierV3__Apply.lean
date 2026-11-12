/-
`(*authApplierV3).Apply(r, shouldApplyV3, applyFunc)` (`auth.go:43-63`): under `aa.mu`, the header's user and revision into `authInfo`; for an administration request, `IsAdminPermitted` (its error the result, `applyFunc` not called); else the base's `Apply` with `applyFunc`; `authInfo` reset.

**Users.** `uberApplier.Apply` (the chain's outer layers' `Apply` are this one, promoted).

**Proof sketch.** The mutex (`applierAt`'s realization: its invariant `aa.authInfo ↦ ("", 0)`, which
every path restores before unlocking, `auth.go:54-55,60-61`) gives the field at `("", 0)`; with a
header it is set to the header's user and revision, without one it stays `("", 0)` (`Irr.user`,
`Irr.revW` of `hdr = none`): either way `aiAt aa ir.user ir.revW`; `needAdminPermission.spec`; 3d's
`IsAdminPermitted` at the stores' auth state (`stAt`: `adminErr`); the base's `Apply` (the quota
applier's promoted one, then `applierV3backend.Apply.spec`) with the function value's triple; the
field reset to `("", 0)` from the `∃ u rv, aiAt aa u rv` it gives back, and the mutex released.

**Changes** from `specs-ref`'s file of the same name: restated over the new vocabulary (`beAt`, `stAt`, `applierAt`, the model state); one spec for every mode.
verify-round (A9 F5): the mutex invariant pinned to `("", 0)` (it was `∃ ai`, too weak for a
header-less request); the statement is unchanged.

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

/-- **The auth layer's `Apply`**: the administrator's refusal, or `applyFunc` with the request's auth info. -/
def authApplierV3.Apply.spec : Prop :=
  ∀ (aa b r : Loc) (ir : Irr) (sk v3 : Bool) (af : GoFunc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State) (A : IProp GF)
    (B : Loc → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3.ty) #aa) baseLayers b aa ∗ beAt b mc γ γc R ∗
      wrapperAt r ir sk ∗ stAt b σ ∗ A ∗
      ({{ aiAt aa ir.user ir.revW ∗ stAt b σ ∗ A ∗
            ⌜ir.op.needAdmin = true → adminErr σ.auth ir.user = none⌝ }}
          (App (App (Val #af) (Val #r)) (Val #v3))
        {{ (ar : Loc), RET #ar; (∃ u rv, aiAt aa u rv) ∗ B ar }}) }}
    (App (App (App (Val (aa @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3.ty @!! go!"Apply")) (Val #r)) (Val #v3)) (Val #af))
  {{ (ar : Loc), RET #ar; B ar ∨
      ∃ e, ⌜ir.op.needAdmin = true ∧ adminErr σ.auth ir.user = some e⌝ ∗ stAt b σ ∗ A ∗
        resultAt γ ar ir sk (.err e) }}

end spec

end Apply
end EtcdGrove
end Perennial
