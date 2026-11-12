/-
## `(*RaftCluster).SetDowngradeInfo(d, shouldApplyV3)` (`cluster.go:809-818`): trusted (names only)

**Users.** 3a's `applierV3backend.DowngradeInfoSet` (a committed downgrade enable/cancel), in both
modes.

**Why it is true.** Under the mutex: at `shouldApplyV3` the info saved to the backend (4b's
`MustSaveDowngradeToBackend`: `beVer`), then `c.downgradeInfo = d` (the pointer: the caller's
read-only struct is kept, `DowngradeInfo()` copies its fields later). No panic. The view's update
fires at the field write.

**Changes**: new (verify-round, A8 completeness F3; 3a's request).
**Margin.** The backend write's post-lock hook is not stated, as `AddMember`'s.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api

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

/-- **Sets the downgrade info** to `d`'s (in the view always, in the backend at `shouldApplyV3`). -/
def RaftCluster.SetDowngradeInfo.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64) (d : Loc)
    (di : go_etcd_io.etcd.server.v3.etcdserver.version.DowngradeInfo) (apply : Bool) (vb : VerSt)
    (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid ∗ d ↦□ di ∗ beVer c vb ∗
      (AU <{ ∃∃ (v : VerSt), clusterVer γ v }> @ ⊤, ∅
        <{ clusterVer γ { v with dg := some (di.Enabled', di.TargetVersion') }, COMM Q }>) }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"SetDowngradeInfo")) (Val #d)) (Val #apply))
  {{ RET #(); Q ∗ beVer c (if apply then { vb with dg := some (di.Enabled', di.TargetVersion') } else vb) }}

end spec

end Membership
end EtcdGrove
end Perennial
