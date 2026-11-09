/-
## `(*RaftCluster).UpdateAttributes(id, attr, shouldApplyV3)` (`cluster.go:467-496`): names only

**Users.** The apply of a `ClusterMemberAttrSet` (a member's `publishV3`: 3a's/2d's,
`EnvStep.publish`).

**Why it is true.** Under the lock: a member's attributes replaced in the map (at any
`shouldApplyV3`), saved to the backend at `shouldApplyV3`; a removed id: a warning; **an id neither a
member nor removed: `lg.Panic`** (the premise: the apply of a publication of a member the cluster
knows, which the cluster's invariant gives: only a member publishes, and only itself).

**Changes**: new (the publication was invisible to the old model). **Margin.** Exact.
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

/-- **Sets member `id`'s name and client URLs.** -/
def RaftCluster.UpdateAttributes.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64) (id : w64)
    (attr : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes) (name : GoString) (urls : List GoString) (apply : Bool)
    (stb : ClusterSt) (Q : IProp GF),
  let upd : ClusterSt → ClusterSt := fun st =>
    st.update (uint.nat id) (fun m => { m with name := name, clientURLs := urls })
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid ∗ ⌜attr.Name' = name⌝ ∗ attr.ClientURLs' ↦*□ urls ∗
      beView c stb ∗
      (AU <{ ∃∃ (st : ClusterSt), clusterSt γ st ∗
              ⌜st.isMember (uint.nat id) ∨ uint.nat id ∈ st.removed⌝ }> @ ⊤, ∅
        <{ clusterSt γ (upd st), COMM Q }>) }}
    (App (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"UpdateAttributes")) (Val #id)) (Val #attr)) (Val #apply))
  {{ RET #(); Q ∗ beView c (if apply then upd stb else stb) }}

end spec

end Membership
end EtcdGrove
end Perennial
