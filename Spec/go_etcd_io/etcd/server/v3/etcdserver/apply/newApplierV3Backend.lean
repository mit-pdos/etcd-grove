/-
`newApplierV3Backend(opts)` (`backend.go:40-44`): the backend applier holding the options.

**Users.** `newApplierV3`.

**Proof sketch.** Allocation; `beAt` and `stAt` are the options' slots (`optsOk`, `optsSt`) behind the field.

**Changes** from `specs-ref`'s file of the same name: restated over the new vocabulary (`beAt`, `stAt`, `applierAt`, the model state); one spec for every mode.
verify-round (A9 F2, F3, F6): the slots now carry the hooks (`hooksOk`) and the lessor's deleter and
live leases (`lessorSt`); the statement is unchanged.

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

/-- **The backend applier over the options.** -/
def newApplierV3Backend.spec : Prop :=
  ∀ (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ optsOk opts mc γ γc R ∗ optsSt opts σ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3Backend)) (Val #opts))
  {{ (v : GoInterface), RET #v; ∃ b : Loc,
      ⌜v = (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty) #b)⌝ ∗ beAt b mc γ γc R ∗ beOpts b opts ∗ stAt b σ ∗
      ∀ aa, applierAt v [Layer.backend] b aa }}

end spec

end Apply
end EtcdGrove
end Perennial
