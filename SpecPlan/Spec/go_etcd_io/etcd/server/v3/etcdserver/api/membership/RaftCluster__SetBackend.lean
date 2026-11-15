/-
## `(*RaftCluster).SetBackend(be)` (`cluster.go:247-250`): names only

**Users.** `bootstrap` (`Finalize`), 2d's `applySnapshot` (the new backend). **Why it is true.** The
field set and the buckets created (`MustCreateBackendBuckets`: existing ones kept). The old
backend's view is dropped (its backend replaced). **Changes**: from `specs-ref`'s
`RaftCluster__SetBackend.lean`. **Margin.** None.
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

/-- **Switches the cluster to the backend `mb`.** -/
def RaftCluster.SetBackend.spec : Prop :=
  ∀ (c : Loc) (γ : CNames) (cid lid : w64) (mb : GoInterface) (st0 st : ClusterSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ isCluster c γ cid lid ∗ beView c st0 ∗ beMembers mb st }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"SetBackend")) (Val #mb))
  {{ RET #(); beView c st }}

end spec

end Membership
end EtcdGrove
end Perennial
