/-
`(*applierV3backend).ClusterVersionSet(r, shouldApplyV3)` (`backend.go:270-285`): the cluster's version set (`semver.MustParse`, `RaftCluster.SetVersion`); after a downgrade, a forced snapshot.

**Users.** `uberApplier.dispatch` (through the outer layers' promoted methods), in both modes.

**Proof sketch.** `semver.MustParse` (`clusterVerOk`'s `Semver.parse ver = some sv`);
2e's `RaftCluster.Version.spec` (its update fired in `optsOk`'s `Membership.clusterVerInv γc`: the
previous version, any); `RaftCluster.SetVersion.spec` with `verFits sv` (`clusterVerOk`), the
backend's `Membership.beVer` (`stAt`'s `optsSt`, moved by `shouldApplyV3`) and its update fired in
the same invariant (`{v with ver := some sv}` keeps `VerSt.ok` by `verFits sv`); `onSet`
(`api.UpdateCapability`) with the logger; `snapSrvOk`'s `ForceSnapshot` with `R` after a downgrade.

**Changes** from `specs-ref`'s file of the same name: restated over the new vocabulary (`beAt`, `stAt`, `applierAt`, the model state); one spec for every mode.
verify-round (server-boot's request): `clusterVerOk` defined over 2e's `verFits`; 2e's `Version`,
`SetVersion` cited, `beVer` and `clusterVerInv` from the options' slots; the statement is unchanged.

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
