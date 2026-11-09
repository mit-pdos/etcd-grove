/-
## `(*RaftCluster).Members()` (`cluster.go:123-132`): translated

**Users.** 2c's `MemberList` (after a linearizable read: the members at the applied state),
`adjustTicks`, the error classification's quorum count (`isConnectedToQuorumSince`), the
interceptors. Go test of the view's behavior: `etcdserverboot/members.go` (`ReqMembers`).

**Proof sketch.** Under the lock, a clone of each member (`Member.Clone.spec`), sorted by id
(`sort.Sort(MembersByID)`: Perennial's sort over `Len`/`Less`/`Swap`): the read fires the update
with the view unchanged.

**Changes** (from `specs-ref`'s `RaftCluster__Members.lean`): the view's atomic read.

**Margin.** The order (by id) is not stated.
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

/-- **The view's members**, fresh copies (a read of the view). -/
def RaftCluster.Members.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64) (Q : ClusterSt → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid ∗ (AU <{ ∃∃ (st : ClusterSt), clusterSt γ st }> @ ⊤, ∅ <{ clusterSt γ st, COMM Q st }>) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"Members")) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ (st : ClusterSt) (ms : List Member), Q st ∗ membersOwn sl ms ∗
      ⌜ms.Perm st.members⌝ }}

end spec

end Membership
end EtcdGrove
end Perennial
