/-
Proof of `Spec/.../schema/alarmBackend__CreateAlarmBucket.lean`: the backend's `BatchTx`,
`LockOutsideApply`, `UnsafeCreateBucket(Alarm)` of a tracked bucket (created empty if absent), the
deferred `Unlock` (nothing the readers see changed, the part idle). Lean-first (prove-ps2-v3alarm,
2026-11-24; the bucket steps as `lessor.initAndRecover`'s of the lease bucket).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.alarmBackend__CreateAlarmBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__BatchTx
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__LockOutsideApply
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeCreateBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Unlock
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge

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

theorem schema.alarmBackend.CreateAlarmBucket.wp_proof
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    schema.alarmBackend.CreateAlarmBucket.spec (GF := GF) (hG := hG) := by
  intro abl γ P W Pk be qo S r hS hRB hhas
  wp_start as ⟨#Hbe, #HB, Ho, Hwb, Hrb⟩
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%bk, #HA, #HAb⟩⟩
  ihave #Hbk : backend.isBucket bk mvcc.alarmBI $$ []
  · unfold mvcc.alarmBI
    iapply mvcc.bucketIs_isBucket hID hName hSafe $$ [$Hpkg $HAb]
  icases backend.isBackend_b γ P W Pk be $$ HB with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -,
    -, -, -, %HPw⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (hBT γ P W Pk be) $$ [$Hbpkg $HB] as %t #Ht
  (try wp_auto)
  wp_apply (hLO γ P W Pk be t qo) $$ [$Hbpkg $HB $Ht $Ho] as ⟨%st, Hl, %Hfree, ⟨HW, HPk⟩, Ho⟩
  (try wp_auto)
  -- the alarm bucket's part apart from the rest
  have hsplit : ∀ n, S n ↔ (n = go!"alarm" ∨ (S n ∧ n ≠ go!"alarm")) := by
    intro n; by_cases hn : n = go!"alarm"
    · subst hn; exact ⟨fun _ => Or.inl rfl, fun _ => hS⟩
    · exact ⟨fun h => Or.inr ⟨h, hn⟩, fun h => h.elim (fun e => absurd e hn) And.left⟩
  ihave Hrb := (backend.rbPart_set γ S _ r hsplit).1 $$ Hrb
  icases (backend.rbPart_split γ (· = go!"alarm") (fun n => S n ∧ n ≠ go!"alarm") r
    (fun n h1 h2 => h2.2 h1)).1 $$ Hrb with ⟨HrbA, HrbR⟩
  icases backend.batchLocked_rbPart γ P be st (· = go!"alarm") r $$ [$Hl $HrbA]
    with ⟨Hl, HrbA, %Hag⟩
  have hagA : (backend.rbData P st.S).lookup go!"alarm" = r.lookup go!"alarm" := Hag _ rfl
  have hrp : ∀ S' : backend.Data, backend.rbPut (GF := GF) γ P mvcc.alarmBI.name S' =
      backend.rbPart γ (· = go!"alarm") (backend.rbData P S') := by
    intro S'
    unfold backend.rbPut; rw [show mvcc.alarmBI.name = go!"alarm" from rfl, hRB]; rfl
  ihave HrbA : backend.rbPut γ P mvcc.alarmBI.name st.S $$ [HrbA]
  · rw [hrp]
    iapply (backend.rbPart_congr γ _ (backend.rbData P st.S) r (fun n hn => Hag n hn)).2 $$ HrbA
  have hlim := HPw.2.2.1
  have hpend : sint.Z st.pend + 1 < 2 ^ 58 := by have := Hfree.2.1; omega
  -- `tx.UnsafeCreateBucket(Alarm)`: the bucket present
  wp_apply (hCB γ P W Pk be t st bk mvcc.alarmBI hhas (by decide) (by decide) hpend false false
      (_hkc := by decide)) $$ [$Hbpkg $HB $Ht $Hl $Hbk $HrbA] as ⟨Hl, HrbA⟩
  (try wp_auto)
  -- the bucket's contents: the part's, empty if absent
  have hSr : st.S.lookup go!"alarm" = r.lookup go!"alarm" := by
    rw [← hagA, backend.rbData_lookup, hRB]; rfl
  have hS1 : (st.create mvcc.alarmBI).S.lookup go!"alarm" =
      some ((r.lookup go!"alarm").getD ∅) := by
    show (if st.S.lookup go!"alarm" = none then st.S.insert go!"alarm" ∅ else st.S).lookup
      go!"alarm" = _
    rw [← hSr]
    rcases hc : st.S.lookup go!"alarm" with _ | b
    · simp
    · simp [hc]
  have hr1 : ∀ n, n = go!"alarm" →
      (backend.rbData P (st.create mvcc.alarmBI).S).lookup n =
        (r.insert go!"alarm" ((r.lookup go!"alarm").getD ∅)).lookup n := by
    rintro n rfl
    rw [backend.rbData_lookup, hRB, GMap.lookup_insert]; exact hS1
  ihave HrbA : backend.rbPart γ (· = go!"alarm")
      (r.insert go!"alarm" ((r.lookup go!"alarm").getD ∅)) $$ [HrbA]
  · ihave HrbA : backend.rbPart γ (· = go!"alarm")
        (backend.rbData P (st.create mvcc.alarmBI).S) $$ [HrbA]
    · rw [← hrp]; iExactEq HrbA; rfl
    iapply (backend.rbPart_congr γ _ _ _ hr1).1 $$ HrbA
  ihave HrbR : backend.rbPart γ (fun n => S n ∧ n ≠ go!"alarm")
      (r.insert go!"alarm" ((r.lookup go!"alarm").getD ∅)) $$ [HrbR]
  · iapply (backend.rbPart_congr γ _ _ _ (fun n hn => by
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hn.2)])).1 $$ HrbR
  ihave Hrb := (backend.rbPart_split γ (· = go!"alarm") (fun n => S n ∧ n ≠ go!"alarm") _
    (fun n h1 h2 => h2.2 h1)).2 $$ [$HrbA $HrbR]
  ihave Hrb := (backend.rbPart_set γ S _ _ hsplit).2 $$ Hrb
  -- the deferred `tx.Unlock()`: nothing the readers see changed; the part idle
  have hvs := mvcc.viewSame_create mvcc.alarmBI (backend.viewSame_of_freeOk Hfree)
  have hroom : sint.Z (st.create mvcc.alarmBI).pend + P.hookMax < 2 ^ 58 := by
    have h2 := HPw.2.2.2.1
    have h3 := Hfree.2.1
    have hpz : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
    show sint.Z (st.pend + W64 1) + P.hookMax < 2 ^ 58
    omega
  ihave ⟨#Hth, %Hnw⟩ := backend.viewSame_thin γ P _ hvs
  wp_apply (backend.batchTxBuffered.Unlock.spec_free hUL γ P W Pk be t (st.create mvcc.alarmBI)
      iprop(True) S (r.insert go!"alarm" ((r.lookup go!"alarm").getD ∅)) Hfree.2.2.2.2.1 hroom)
    $$ [$Hbpkg $HB $Ht $Hl $Hwb $Hrb HW HPk] as ⟨-, Hrb⟩
  · ileft; iframe HW HPk Hth; ipureintro; exact Hnw
  (try wp_auto)
  iapply HΦ
  iframe Ho Hrb

end proof

end EtcdGrove
end Perennial
