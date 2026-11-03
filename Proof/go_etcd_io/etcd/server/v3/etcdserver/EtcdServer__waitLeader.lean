/-
The trust boundary: `(*EtcdServer).waitLeader` (names only; the lease-renew plan's C4, 2026-11-01).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__waitLeader

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

axiom EtcdServer.waitLeader.wp_proof : EtcdServer.waitLeader.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
