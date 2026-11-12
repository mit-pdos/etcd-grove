/-
## `(*RaftCluster).RemoveMember(id, shouldApplyV3)` (`cluster.go:429-465`): translated

**Users.** 2d's `applyConfChange` (a `RemoveNode` the check accepted).
**Proof sketch.** Under the lock, at `shouldApplyV3`: deleted from the backend (4b), from the map,
recorded as removed. The log lines' `c.cid.String()`, `c.localID.String()` and `id.String()` are
client-core's `Types.ID.String_ptr.spec` (pointer receivers: the fields read-only in `isCluster`'s
realization, `id` a local). **Changes**: from `specs-ref`. Second pass: `ID.String_ptr` cited.
**Margin.** Exact.
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

/-- **Removes member `id`** (at `shouldApplyV3`). -/
def RaftCluster.RemoveMember.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64) (id : w64) (apply : Bool) (stb : ClusterSt)
    (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid ∗ beView c stb ∗
      (AU <{ ∃∃ (st : ClusterSt), clusterSt γ st }> @ ⊤, ∅ <{ clusterSt γ (if apply then st.remove (uint.nat id) else st), COMM Q }>) }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"RemoveMember")) (Val #id)) (Val #apply))
  {{ RET #(); Q ∗ beView c (if apply then stb.remove (uint.nat id) else stb) }}

end spec

end Membership
end EtcdGrove
end Perennial
