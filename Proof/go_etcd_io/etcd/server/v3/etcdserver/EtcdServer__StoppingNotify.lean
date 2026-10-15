/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__StoppingNotify.lean`. Lean-first
(no Rocq counterpart); the watch slice's unit W-W (2026-10-15).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__StoppingNotify

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

theorem EtcdServer.StoppingNotify.wp_proof :
    EtcdServer.StoppingNotify.spec (GF := GF) (hG := hG) := by
  intro s ch
  wp_start as #Hf
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
