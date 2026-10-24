/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Backend.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Backend

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

theorem EtcdServer.Backend.wp_proof : EtcdServer.Backend.spec (GF := GF) (hG := hG) := by
  intro s γbe
  wp_start as Hrd
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold srvBemuReaderAt at Hrd
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HP⟩
  iunfold bemuP at HP
  icases HP with ⟨%d, Hb, Hg, #Hro⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hb Hg] as Hrd
  · inext; iunfold bemuP; iexists d; iframe Hb Hg Hro
  iapply HΦ
  iunfold srvBemuReaderAt
  iframe Hrd
  iexists d
  iframe Hro
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
