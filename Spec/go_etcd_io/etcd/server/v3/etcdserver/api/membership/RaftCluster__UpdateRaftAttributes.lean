/-
## `(*RaftCluster).UpdateRaftAttributes(id, raftAttr, shouldApplyV3)` (`cluster.go:535-578`): names only

**Users.** 2d's `applyConfChange` (an `UpdateNode`: a `MemberUpdate`).
**Why it is true.** Under the lock: a member's peer URLs replaced (at any `shouldApplyV3`; nothing
for an unknown id), saved at `shouldApplyV3`. **Changes**: new. **Margin.** Exact.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api

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

/-- **Sets member `id`'s peer URLs.** -/
def RaftCluster.UpdateRaftAttributes.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64) (id : w64)
    (ra : go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftAttributes) (urls : List GoString) (apply : Bool) (stb : ClusterSt)
    (Q : IProp GF),
  let upd : ClusterSt → ClusterSt := fun st =>
    st.update (uint.nat id) (fun m => { m with peerURLs := urls })
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid ∗ ra.PeerURLs' ↦*□ urls ∗ beView c stb ∗
      (AU <{ ∃∃ (st : ClusterSt), clusterSt γ st }> @ ⊤, ∅ <{ clusterSt γ (upd st), COMM Q }>) }}
    (App (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"UpdateRaftAttributes")) (Val #id)) (Val #ra)) (Val #apply))
  {{ RET #(); Q ∗ beView c (if apply then upd stb else stb) }}

end spec

end Membership
end EtcdGrove
end Perennial
