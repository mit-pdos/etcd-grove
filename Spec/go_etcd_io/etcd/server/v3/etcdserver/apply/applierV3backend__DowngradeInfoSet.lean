/-
`(*applierV3backend).DowngradeInfoSet(r, shouldApplyV3)` (`backend.go:298-304`): the downgrade info set (`RaftCluster.SetDowngradeInfo`).

**Users.** `uberApplier.dispatch` (through the outer layers' promoted methods), in both modes.

**Proof sketch.** 2e's `SetDowngradeInfo` (requested).

**Changes** from `specs-ref`'s file of the same name: restated over the new vocabulary (`beAt`, `stAt`, `applierAt`, the model state); one spec for every mode.

**Margin.** Outside the model.
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

/-- **The downgrade info set**: nothing in the model. -/
def applierV3backend.DowngradeInfoSet.spec : Prop :=
  ∀ (p rq : Loc) (v3 en : Bool) (ver : GoString) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ beAt p mc γ γc R ∗ stAt p σ ∗ reqMsgAt rq (.downgradeInfoSet en ver) ∗ threadTok }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty @!! go!"DowngradeInfoSet")) (Val #rq)) (Val #v3))
  {{ RET #(); stAt p σ ∗ threadTok }}

end spec

end Apply
end EtcdGrove
end Perennial
