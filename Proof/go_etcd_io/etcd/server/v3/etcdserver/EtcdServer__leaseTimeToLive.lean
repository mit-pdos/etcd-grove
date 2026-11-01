/-
The trust boundary: `(*EtcdServer).leaseTimeToLive` (names only; the lease-read plan's S1, the
user's choice, 2026-10-31): the leader's lookup (`waitAppliedIndex`, `Lookup`, `Remaining`, `TTL`,
`Keys`, `Demoted`) and a follower's forwarding to the leader (`waitLeader`, `leasehttp`, a loop to
the request's timeout). It returns, reading its request; nothing is claimed of the response.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__leaseTimeToLive

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

axiom EtcdServer.leaseTimeToLive.wp_proof : EtcdServer.leaseTimeToLive.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
