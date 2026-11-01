module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__LeaseKeepAlive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__leaseKeepAlive

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.LeaseServer.LeaseKeepAlive.wp_proof
    (hLoop : v3rpc.LeaseServer.leaseKeepAlive.spec (GF := GF) (hG := hG)) :
    v3rpc.LeaseServer.LeaseKeepAlive.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
