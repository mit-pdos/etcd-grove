/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/NewClusterServer.lean` (item 4, the server
start). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewClusterServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Cluster

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
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

theorem v3rpc.NewClusterServer.wp_proof
    (hCl : EtcdServer.Cluster.spec (GF := GF) (hG := hG)) :
    v3rpc.NewClusterServer.spec (GF := GF) (hG := hG) := by
  intro s cl
  wp_start as #Hcl
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  wp_auto
  wp_apply (hCl s cl)
  · iframe #
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
