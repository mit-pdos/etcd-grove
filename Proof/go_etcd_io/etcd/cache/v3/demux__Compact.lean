/-
Proof of `Spec/demux__Compact.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.demux__Compact
public import Spec.go_etcd_io.etcd.cache.v3.demux__purge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem demux.Compact.wp_proof (wp_purge : demux.purge.spec (GF := GF) (hG := hG)) :
    demux.Compact.spec (GF := GF) (hG := hG) := by
  intro d γd cap C c compactRev
  wp_start as ⟨#Hd, Hw⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold demuxWriter
  icases Hw with ⟨Hgw, Hmu, %Hinv⟩
  unfold demuxHandle
  wp_apply (lc := 3) sync.RWMutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HP⟩
  icombine Hlc1 Hlc2 as Hlc12
  imod demux_lock_acquire d γd cap $$ [$Hd $HP $Hlc12] with ⟨%c', %regs, %views, Hcore, Hl, %Hinv'⟩
  icombine Hgw Hcore gives % ⟨_, Heq⟩
  subst Heq
  wp_apply wp_purge $$ [$Hl] as ⟨%views', Hl⟩
  · ipureintro; exact Hinv
  imod ghostVar_update_halves DemuxCore.init γd.core c c $$ Hgw Hcore with ⟨Hgw, Hcore⟩
  have Hinit : DemuxInv cap DemuxCore.init := by
    constructor <;> (try simp [DemuxCore.init]) <;>
      first | exact Hinv.cap_pos | exact Hinv.cap_le | exact ⟨by simp, by simp [RevSorted], by simp⟩ | word
  have hrel := demux_lock_release (hG := hG) (C := C) d γd cap DemuxCore.init regs views'
  rw [show DemuxCore.init.stream.length = 0 from rfl] at hrel
  imod hrel $$ [$Hd $Hcore $Hl $Hlc3] with HP
  · ipureintro; exact Hinit
  wp_apply sync.RWMutex.wp_Unlock $$ [$Hlocked $HP] as Hmu
  iapply HΦ
  iframe
  ipureintro; exact Hinit

end proof

end EtcdGrove
end Perennial
