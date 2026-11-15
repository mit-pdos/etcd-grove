/-
## `(*RaftCluster).ID()` (`cluster.go:121`): translated

**Users.** v3rpc's headers (`member.go:113`), the server's logging, the transport's cluster id.
**Proof sketch.** A read-only field. **Changes**: from `specs-ref`'s `RaftCluster__ID.lean`.
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

/-- **The cluster id.** -/
def RaftCluster.ID.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"ID")) (Val #()))
  {{ RET #cid; True }}

end spec

end Membership
end EtcdGrove
end Perennial
