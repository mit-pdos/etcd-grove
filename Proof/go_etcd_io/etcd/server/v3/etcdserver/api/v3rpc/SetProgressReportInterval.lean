/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.SetProgressReportInterval

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.SetProgressReportInterval.wp_proof :
    v3rpc.SetProgressReportInterval.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start as ⟨#Hv, %Hb⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold v3rpc.watchVars at Hv
  icases Hv with ⟨-, #Hv⟩
  iunfold v3rpc.watchPkgVars at Hv
  icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hg⟩
  -- the lock's guard, from its pool (2026-10-20)
  iunfold v3rpc.intervalPool at Hg
  icases Hg with ⟨#Hg, -⟩
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hg] as ⟨Hl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := v3rpc.intervalP 1)) $$ Hlc1 HP with HP
  iunfold v3rpc.intervalP at HP
  icases HP with ⟨%d0, Hd, -⟩
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_Unlock_guard $$ [$Hl Hd]
  · iframe #
    inext
    iunfold v3rpc.intervalP
    iexists d
    iframe
    ipureintro; exact Hb
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
