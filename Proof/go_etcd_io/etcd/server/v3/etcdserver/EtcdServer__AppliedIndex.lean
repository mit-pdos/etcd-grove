/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__AppliedIndex.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AppliedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getAppliedIndex

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.AppliedIndex.wp_proof
    (hG' : EtcdServer.getAppliedIndex.spec (GF := GF) (hG := hG)) :
    EtcdServer.AppliedIndex.spec (GF := GF) (hG := hG) := by
  intro s E γr
  wp_start as #Hinv
  wp_auto
  wp_apply hG' s E γr $$ [] as %v #Hv
  · iframe #
  iapply HΦ
  iexact Hv

end proof

end EtcdGrove
end Perennial
