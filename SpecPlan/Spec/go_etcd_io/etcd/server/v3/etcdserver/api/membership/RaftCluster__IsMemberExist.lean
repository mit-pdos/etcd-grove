/-
## `(*RaftCluster).IsMemberExist(id)` (`cluster.go`): translated

**Users.** the server's `IsMemberExist` (2a's interceptors). **Proof sketch.** Under the lock, a map lookup: a read of the view.
**Changes**: from `specs-ref`'s `RaftCluster__IsMemberExist.lean`: the view's atomic read. **Margin.** Exact.
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

/-- **whether `id` is a member** in the view. -/
def RaftCluster.IsMemberExist.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64) (id : w64) (Q : ClusterSt → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid ∗ (AU <{ ∃∃ (st : ClusterSt), clusterSt γ st }> @ ⊤, ∅ <{ clusterSt γ st, COMM Q st }>) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"IsMemberExist")) (Val #id))
  {{ (b : Bool), RET #b; ∃ st : ClusterSt, Q st ∗ ⌜b = decide (st.isMember (uint.nat id))⌝ }}

end spec

end Membership
end EtcdGrove
end Perennial
