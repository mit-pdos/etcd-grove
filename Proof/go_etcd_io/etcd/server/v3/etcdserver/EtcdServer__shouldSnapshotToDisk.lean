/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__shouldSnapshotToDisk.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__shouldSnapshotToDisk

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

theorem EtcdServer.shouldSnapshotToDisk.wp_proof :
    EtcdServer.shouldSnapshotToDisk.spec (GF := GF) (hG := hG) := by
  intro s ep f ai d sc
  wp_start as ⟨Hf, Hai, Hd, #Hsc⟩
  wp_auto
  cases f
  · wp_auto
    iapply HΦ
    iframe
  · wp_auto
    by_cases hd : ai = d
    · simp only [hd, decide_true]
      wp_auto
      iapply HΦ
      iframe
    · simp only [hd, decide_false]
      wp_auto
      iapply HΦ
      iframe

end proof

end EtcdGrove
end Perennial
