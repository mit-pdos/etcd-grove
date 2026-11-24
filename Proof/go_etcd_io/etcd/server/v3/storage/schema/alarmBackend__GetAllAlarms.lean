/-
Proof of `Spec/.../schema/alarmBackend__GetAllAlarms.lean`: `ReadTx`, `RLock` (a reader slot borrowed with
the thread token, `reader_RLock`), the idle-read law (`backend.rtHeld_rbOwnIn_idle`: the readers' alarm
bucket is the writer's, empty), `unsafeGetAllAlarms`, the deferred `RUnlock` (`reader_RUnlock`). Lean-first
(prove-ps2-v3alarm, 2026-11-24).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.alarmBackend__GetAllAlarms
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.alarmBackend__unsafeGetAllAlarms
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ReadTx
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RLock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RUnlock
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.IdleRead

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.alarmBackend.GetAllAlarms.wp_proof
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hU : schema.alarmBackend.unsafeGetAllAlarms.spec (GF := GF) (hG := hG)) :
    schema.alarmBackend.GetAllAlarms.spec (GF := GF) (hG := hG) := by
  intro abl γ P W Pk be qo r hRB hhas hr
  wp_start as ⟨#Hbe, #HB, Ho, #Hpl, Htk, Hin, Hct⟩
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply +noauto (hRT γ P W Pk be) $$ [$Hbpkg $HB] as %rt #Hrt
  wp_auto_lc 1
  wp_apply (backend.reader_RLock hRL γ P W Pk be rt qo) $$ [$Hbpkg $HB $Hrt $Hpl $Htk $Hlc1 $Ho]
    as ⟨%rtx, %rv, Hh, Hloan, Ho⟩
  -- the readers' alarm bucket: the idle part's, empty
  iapply fupd_wp
  imod (backend.rtHeld_rbOwnIn_idle γ P be rtx rv go!"alarm" r ⟨_, hhas⟩ hRB ⊤
      (fun _ _ => CoPset.mem_full)) $$ [$Hh $Hin $Hct] with ⟨Hh, Hin, Hct, %Hrv⟩
  imodintro
  icases backend.rtHeld_wf γ P be rtx rv $$ Hh with ⟨Hh, %Hwf⟩
  rw [backend.rtHeld_eq]
  (try wp_auto)
  wp_apply (hU abl γ P W Pk be rt rtx rv _ hhas (by rw [Hrv]; exact hr) Hwf)
    $$ [$Hpkg $HB $Hrt $Hh] as %ms %err ⟨%Herr, Hms, Hh⟩
  (try wp_auto)
  rw [← backend.rtHeld_eq]
  wp_apply (backend.reader_RUnlock hRU γ P W Pk be rt rtx rv) $$ [$Hbpkg $HB $Hrt $Hh $Hloan] as Htk
  (try wp_auto)
  iapply HΦ
  iframe Hms Ho Htk Hin Hct
  ipureintro; exact Herr

end proof

end EtcdGrove
end Perennial
