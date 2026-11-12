/-
`newAuthApplierV3(as, base, lessor)` (`auth.go:39-41`): the auth applier over `base` (its mutex, an empty `authInfo`).

**Users.** `newApplierV3`.

**Proof sketch.** Allocation; the mutex's invariant `∃ ai, aa.authInfo ↦ ai` (`applierAt`'s realization).

**Changes** from `specs-ref`'s file of the same name: restated over the new vocabulary (`beAt`, `stAt`, `applierAt`, the model state); one spec for every mode.

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

/-- **The auth applier over `base`**, with the options' auth store and lessor. -/
def newAuthApplierV3.spec : Prop :=
  ∀ (ast le base : GoInterface) (b aa0 : Loc) (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ applierAt base [Layer.quota, Layer.backend] b aa0 ∗ beAt b mc γ γc R ∗ beOpts b opts ∗
      ⌜ast = opts.AuthStore' ∧ le = opts.Lessor'⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.newAuthApplierV3)) (Val #ast)) (Val #base)) (Val #le))
  {{ (aa : Loc), RET #aa;
      applierAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3.ty) #aa) baseLayers b aa }}

end spec

end Apply
end EtcdGrove
end Perennial
