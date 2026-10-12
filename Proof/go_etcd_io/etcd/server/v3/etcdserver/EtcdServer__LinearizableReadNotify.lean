/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__LinearizableReadNotify.lean`. Lean-first (no Rocq
counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LinearizableReadNotify

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.LinearizableReadNotify.wp_proof :
    EtcdServer.LinearizableReadNotify.spec (GF := GF) (hG := hG) := by
  intro s r γr ctx cd c
  wp_start as ⟨#Hr, #HR, #Hctx, #Hc⟩
  wp_auto
  iunfold isRead at HR
  wp_apply HR $$ [] as %err Herr
  · iframe #
  try wp_auto
  iapply HΦ
  iexact Herr

end proof

end EtcdGrove
end Perennial
