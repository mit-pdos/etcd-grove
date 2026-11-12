/-
The trust boundary: `membership.RaftCluster.updateMembershipMetric` (`cluster.go`, names only; D43
M4, 2026-10-26): a prometheus gauge (see the spec's docstring).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__updateMembershipMetric

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

axiom membership.RaftCluster.updateMembershipMetric.wp_proof :
  membership.RaftCluster.updateMembershipMetric.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
