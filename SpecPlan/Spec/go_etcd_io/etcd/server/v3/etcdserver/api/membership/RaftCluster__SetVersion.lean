/-
## `(*RaftCluster).SetVersion(ver, onSet, shouldApplyV3)` (`cluster.go:589-624`): trusted (names only)

**Users.** 3a's `applierV3backend.ClusterVersionSet` (`apply/backend.go:270-285`: `semver.MustParse`
of the request's version, then this, with `api.UpdateCapability` as `onSet`), in both modes;
`shouldApplyV3` false for an entry replayed below the backend's consistent index.

**Why it is true.** Under the mutex: a log line, `c.version = ver` (the pointer: the caller's
read-only `*Version` is kept), `MustDetectDowngrade(binary, ver)` (a panic if the binary's
major.minor is below `ver`: `verFits`), at `shouldApplyV3` the version saved to the backend
(4b's `MustSaveClusterVersionToBackend`: `beVer`), the metrics' gauges (trusted, no failure), the
version-changed notifier's `Notify` if one was set (pkg notify's `Notifier.Notify.spec`, its update
fired in the `clusterNotifyN` invariant that `SetVersionChangedNotifier` took; the lock invariant
keeps `notifierAt` and that invariant), then `onSet(lg, ver)` under the lock (its contract: the premise; the
cluster's logger is a `Zap.isLogger`). The view's update fires at the field write.

**Changes**: new (verify-round, A8 completeness F3; 3a's request). Second pass: the notifier's
`Notify` cited (server-core's request 4).
**Margin.** The backend write's post-lock hook (the consistent index at `shouldApplyV3`) is not
stated, as `AddMember`'s; the metrics are not stated.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api
public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Membership

open Iris Iris.BI EtcdModel Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

/-- **Sets the cluster version** to `sv` (in the view always, in the backend at `shouldApplyV3`),
then calls `onSet`. -/
def RaftCluster.SetVersion.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64) (ver : Loc) (sv : Semver.SemVer) (onSet : GoFunc)
    (apply : Bool) (vb : VerSt) (Q R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid ∗ Semver.verAt ver sv ∗ ⌜verFits sv⌝ ∗
      beVer c vb ∗
      (∀ lg : Loc, Zap.isLogger lg -∗ Q -∗
        WP (App (App (Val #onSet) (Val #lg)) (Val #ver)) {{ fun _ => R }}) ∗
      (AU <{ ∃∃ (v : VerSt), clusterVer γ v }> @ ⊤, ∅
        <{ clusterVer γ { v with ver := some sv }, COMM Q }>) }}
    (App (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"SetVersion")) (Val #ver)) (Val #onSet)) (Val #apply))
  {{ RET #(); R ∗ beVer c (if apply then { vb with ver := some sv } else vb) }}

end spec

end Membership
end EtcdGrove
end Perennial
