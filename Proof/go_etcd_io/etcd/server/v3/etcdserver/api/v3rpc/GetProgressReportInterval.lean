/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.GetProgressReportInterval
public import Spec.math.rand.Int63n

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

theorem v3rpc.GetProgressReportInterval.wp_proof
    (hRand : rand.Int63n.spec (GF := GF) (hG := hG)) :
    v3rpc.GetProgressReportInterval.spec (GF := GF) (hG := hG) := by
  wp_start_folded as ⟨#Hv, Htok, %Hb⟩
  wp_func_call
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  -- the pool, from the package's fact
  ihave #Hv' := Hv
  iunfold v3rpc.watchVars at Hv'
  icases Hv' with ⟨-, #Hwpv⟩
  iunfold v3rpc.watchPkgVars at Hwpv
  icases Hwpv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hpool⟩
  wp_auto_lc 1
  -- borrow a reader slot
  imod (v3rpc.intervalPool_borrow ⊤ (by simp) Hb) $$ [Hpool Hlc1 Htok] with ⟨Hrd, Hloan⟩
  · iframe #; iframe
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := v3rpc.intervalP sync.rfrac)) $$ Hlc1 HP with HP
  iunfold v3rpc.intervalP at HP
  icases HP with ⟨%d, Hd, %Hb⟩
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl Hd] as Hrd
  · iframe #
    inext
    iunfold v3rpc.intervalP
    iexists d
    iframe
    ipureintro; exact Hb
  wp_auto_lc 1
  -- return it
  imod (v3rpc.intervalPool_return ⊤ (by simp)) $$ [Hloan Hlc1 Hrd] with Htok
  · iframe
  (try wp_auto)
  have hdiv : sint.Z (BitVec.sdiv d (W64 10)) = sint.Z d / 10 := by word
  wp_apply hRand (BitVec.sdiv d (W64 10)) as %x %Hx
  · ipureintro; rw [hdiv]; omega
  (try wp_auto)
  iapply HΦ
  iframe Htok
  ipureintro
  rw [hdiv] at Hx
  word

end proof

end EtcdGrove
end Perennial
