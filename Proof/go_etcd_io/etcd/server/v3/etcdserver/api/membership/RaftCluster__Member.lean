/-
The trust boundary: `membership.RaftCluster.Member` (`cluster.go`, names-only; etcd-io/etcd#22525).
Its body (`c.Lock(); defer c.Unlock(); return c.members[id].Clone()`) would be provable from
`isRaftCluster` and `Member.Clone` (both here) but for the meaning of the result, `attrsHeld`,
which no invariant here states (the members map's writers, the apply thread's membership changes
and `Recover`, are names-only).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Member

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

axiom membership.RaftCluster.Member.wp_proof :
  membership.RaftCluster.Member.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
