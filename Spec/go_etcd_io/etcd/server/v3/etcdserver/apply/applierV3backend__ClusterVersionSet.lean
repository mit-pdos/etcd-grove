/-
`(*applierV3backend).ClusterVersionSet(r, shouldApplyV3)` (`backend.go:270-285`): the cluster's version set (`semver.MustParse`, `RaftCluster.SetVersion`); after a downgrade, a forced snapshot.

**Users.** `uberApplier.dispatch` (through the outer layers' promoted methods), in both modes.

**Proof sketch.** `semver.MustParse` and `SetVersion`'s `MustDetectDowngrade` (`clusterVerOk`: 2e's/4b's, requested); `RaftCluster.Version`/`SetVersion` (2e's, requested); `snapSrvOk`'s `ForceSnapshot` with `R`.

**Changes** from `specs-ref`'s file of the same name: restated over the new vocabulary (`beAt`, `stAt`, `applierAt`, the model state); one spec for every mode.

**Margin.** The version is outside the model.
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

/-- **The cluster version set**: nothing in the model. -/
def applierV3backend.ClusterVersionSet.spec : Prop :=
  ∀ (p rq : Loc) (v3 : Bool) (ver : GoString) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ beAt p mc γ γc R ∗ stAt p σ ∗ reqMsgAt rq (.clusterVersionSet ver) ∗
      ⌜clusterVerOk ver⌝ ∗ R ∗ threadTok }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty @!! go!"ClusterVersionSet")) (Val #rq)) (Val #v3))
  {{ RET #(); stAt p σ ∗ R ∗ threadTok }}

end spec

end Apply
end EtcdGrove
end Perennial
