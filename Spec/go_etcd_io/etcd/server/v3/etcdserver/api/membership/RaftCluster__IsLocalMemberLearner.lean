/-
## `(*RaftCluster).IsLocalMemberLearner()` (`cluster.go:786-797`): translated

**Users.** The server's `IsLearner` (2a's interceptors refuse a learner's unsupported RPCs).
**Proof sketch.** Under the lock, the local member's flag (the fork's: `false` for a removed local
member, no panic). **Changes**: from `specs-ref`. **Margin.** Exact.
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

/-- **Whether the local member is a learner** in the view (`false` if it is not a member). -/
def RaftCluster.IsLocalMemberLearner.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64) (Q : ClusterSt → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid ∗ (AU <{ ∃∃ (st : ClusterSt), clusterSt γ st }> @ ⊤, ∅ <{ clusterSt γ st, COMM Q st }>) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"IsLocalMemberLearner")) (Val #()))
  {{ (b : Bool), RET #b; ∃ st : ClusterSt, Q st ∗
      ⌜b = decide (∃ m ∈ st.members, m.id = uint.nat lid ∧ m.isLearner = true)⌝ }}

end spec

end Membership
end EtcdGrove
end Perennial
