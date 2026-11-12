/-
`newApplierV3(opts)` (`uber_applier.go:61-68`): the base chain: auth over quota over backend.

**Users.** `NewUberApplier`.

**Proof sketch.** `newApplierV3Backend.spec`, `newQuotaApplierV3.spec` (the logger, backend and quota size of the options), `newAuthApplierV3.spec`.

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

/-- **The base chain over the options.** -/
def newApplierV3.spec : Prop :=
  ∀ (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ optsOk opts mc γ γc R ∗ optsSt opts σ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3)) (Val #opts))
  {{ (v : GoInterface), RET #v; ∃ b aa : Loc, beAt b mc γ γc R ∗ beOpts b opts ∗ stAt b σ ∗
      applierAt v baseLayers b aa }}

end spec

end Apply
end EtcdGrove
end Perennial
