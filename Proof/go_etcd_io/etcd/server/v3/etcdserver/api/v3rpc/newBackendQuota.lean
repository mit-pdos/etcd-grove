/-
Proof of the spec of the same name (unit P3b). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newBackendQuota
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Backend
public import Spec.go_etcd_io.etcd.server.v3.storage.NewBackendQuota

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

theorem v3rpc.newBackendQuota.wp_proof
    (wp_Logger : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (wp_Backend : EtcdServer.Backend.spec (GF := GF) (hG := hG))
    (wp_NewBackendQuota : storage.NewBackendQuota.spec (GF := GF) (hG := hG)) :
    v3rpc.newBackendQuota.spec (GF := GF) (hG := hG) := by
  intro s lg qb name Hbuq
  wp_start as ⟨#Hlg, %Hlgn, Hlr, #Hqb, Hbr⟩
  wp_auto
  wp_apply wp_Logger s lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe; iframe #; ipureintro; exact Hlgn
  iunfold srvBemuReader at Hbr
  icases Hbr with ⟨%γbe, Hbr⟩
  wp_apply wp_Backend s γbe $$ [Hbr] as %be ⟨Hbr, -⟩
  · iframe
  wp_apply wp_NewBackendQuota _ _ _ _ Hbuq as %qv #Hq
  iapply HΦ
  iframe
  iframe #
  iunfold srvBemuReader
  iexists γbe
  iexact Hbr

end proof

end EtcdGrove
end Perennial
