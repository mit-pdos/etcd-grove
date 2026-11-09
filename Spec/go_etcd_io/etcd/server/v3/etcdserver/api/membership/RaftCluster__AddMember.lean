/-
## `(*RaftCluster).AddMember(m, shouldApplyV3)` (`cluster.go:394-427`): translated

**Users.** 2d's `applyConfChange` (an `AddNode`/`AddLearnerNode` the check accepted; `shouldApplyV3`
false for an entry at or below the backend's consistent index, replayed after a restart).

**Proof sketch.** Under the lock: at `shouldApplyV3` the member saved to the backend
(`MustSaveMemberToBackend`, 4b: `beView`) and put in the map (the pointer: the caller's member
moves in); else only a log line. The view's update fires at the map write.

**Changes** (from `specs-ref`'s `RaftCluster__AddMember.lean`): the view's update and the backend's
view. **Margin.** Exact.
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

/-- **Adds member `m`** (at `shouldApplyV3`) to the view and the backend. -/
def RaftCluster.AddMember.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64) (p : Loc) (mm : Member) (apply : Bool)
    (stb : ClusterSt) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid ∗ memberPts p (DFrac.own 1) mm ∗ beView c stb ∗
      (AU <{ ∃∃ (st : ClusterSt), clusterSt γ st }> @ ⊤, ∅ <{ clusterSt γ (if apply then st.add mm else st), COMM Q }>) }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"AddMember")) (Val #p)) (Val #apply))
  {{ RET #(); Q ∗ beView c (if apply then stb.add mm else stb) }}

end spec

end Membership
end EtcdGrove
end Perennial
