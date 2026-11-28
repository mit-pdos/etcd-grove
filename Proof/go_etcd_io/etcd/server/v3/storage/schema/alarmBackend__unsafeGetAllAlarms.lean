/-
Proof of `Spec/.../schema/alarmBackend__unsafeGetAllAlarms.lean`: `readTx.UnsafeForEach` of `Alarm` at a
readers' state whose alarm bucket is empty walks nothing (`schema.rtForEach_mem`), so the visitor is never
called and `ms` stays nil. Lean-first (prove-ps2-v3alarm, 2026-11-24).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.alarmBackend__unsafeGetAllAlarms
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__UnsafeForEach
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthRealRead

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

theorem schema.alarmBackend.unsafeGetAllAlarms.wp_proof
    (hFE : backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    schema.alarmBackend.unsafeGetAllAlarms.spec (GF := GF) (hG := hG) := by
  intro abl γ P W Pk be rt rtx rv p hhas hemp hwf
  wp_start as ⟨#HB, #Hrt, Hh⟩
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%bk, #HA, #HAb⟩, -⟩
  ihave #Hbk : backend.isBucket bk mvcc.alarmBI $$ []
  · unfold mvcc.alarmBI
    iapply mvcc.bucketIs_isBucket hID hName hSafe $$ [$Hpkg $HAb]
  -- the readers' alarm bucket is empty: the walk visits nothing
  have hnil : backend.rtForEach rv mvcc.alarmBI = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro e he
    have h := (schema.rtForEach_mem hhas hwf e.1 e.2).1 he
    rw [show mvcc.alarmBI.name = go!"alarm" from rfl, hemp] at h
    simp at h
  wp_auto
  wp_apply (hFE γ P W Pk be rt rtx rv p bk mvcc.alarmBI _ (fun _ => iprop(True))
      (fun _ _ => iprop(False))) $$ [$Hbpkg $HB $Hrt $Hh $Hbk] as %err ⟨Hh, Hcase⟩
  · isplitr
    · itrivial
    iintro !> %i %e %k %v %Hi
    rw [hnil] at Hi
    simp at Hi
  icases Hcase with (⟨%Herr, -⟩ | ⟨%i, %Hi, -⟩)
  · (try wp_auto)
    iapply HΦ
    iframe Hh
    isplitr
    · ipureintro; exact Herr
    iapply (ownSlice_nil (V := Loc) (DFrac.own 1))
  · rw [hnil] at Hi
    simp at Hi

end proof

end EtcdGrove
end Perennial
