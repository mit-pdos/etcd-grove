/-
## `(*RaftCluster).PromoteMember(id, shouldApplyV3)` (`cluster.go:498-533`): names only

**Users.** 2d's `applyConfChange` (an `AddNode` promoting a learner).
**Why it is true.** Under the lock, at `shouldApplyV3`: a member's learner flag cleared and saved
(nothing for an unknown id). **Changes**: new. **Margin.** Exact.
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

/-- **Promotes member `id`** (at `shouldApplyV3`). -/
def RaftCluster.PromoteMember.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64) (id : w64) (apply : Bool) (stb : ClusterSt)
    (Q : IProp GF),
  let upd : ClusterSt → ClusterSt := fun st =>
    if apply then st.update (uint.nat id) (fun m => { m with isLearner := false }) else st
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid ∗ beView c stb ∗ (AU <{ ∃∃ (st : ClusterSt), clusterSt γ st }> @ ⊤, ∅ <{ clusterSt γ (upd st), COMM Q }>) }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"PromoteMember")) (Val #id)) (Val #apply))
  {{ RET #(); Q ∗ beView c (upd stb) }}

end spec

end Membership
end EtcdGrove
end Perennial
