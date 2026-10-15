/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__FirstCommitInTermNotify.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__FirstCommitInTermNotify

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

theorem EtcdServer.FirstCommitInTermNotify.wp_proof
    (hRecv : notify.Notifier.Receive.spec (GF := GF) (hG := hG)) :
    EtcdServer.FirstCommitInTermNotify.spec (GF := GF) (hG := hG) := by
  intro s n
  wp_start as ⟨#Hf, Hr⟩
  ihave #Pn : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify $$ []
  · iPkgInit
  wp_auto
  wp_apply hRecv n $$ [Hr] as %ch ⟨Hr, #Hc⟩
  · iframe #; iframe Hr
  iapply HΦ
  iframe Hr Hc

end proof

end EtcdGrove
end Perennial
