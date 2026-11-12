/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__restoreAlarms
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3Capped
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3Corrupt

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.uberApplier.restoreAlarms.wp_proof
    (hCap : apply.newApplierV3Capped.spec (GF := GF) (hG := hG))
    (hCor : apply.newApplierV3Corrupt.spec (GF := GF) (hG := hG)) :
    apply.uberApplier.restoreAlarms.spec (GF := GF) (hG := hG) := by
  intro p ast base a T z
  wp_start as ⟨#Has, #HGet, HT, #Hbs, Ha⟩
  iunfold apply.alarmGetIs at HGet
  wp_auto
  wp_bind (App (Val (ast @!! go.GoType.PointerType
    go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore.ty @!! go!"Get")) (Val _))
  iapply HGet $$ HT
  inext
  iintro %s1 ⟨HT, %Hg1⟩
  (try wp_auto)
  wp_bind (App (Val (ast @!! go.GoType.PointerType
    go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore.ty @!! go!"Get")) (Val _))
  iapply HGet $$ HT
  inext
  iintro %s2 ⟨HT, %Hg2⟩
  (try wp_auto)
  wp_if_destruct
  · -- a `NOSPACE` alarm: capped
    have hz : z = false := by
      cases z
      · rfl
      · exfalso; have := Hg1 rfl; rw [this] at Hif; simp at Hif
    subst hz
    wp_apply (hCap base) $$ [] as %a1 ⟨#Hk1, #Ha1⟩
    (try wp_auto)
    wp_if_destruct
    · wp_apply (hCor a1) $$ [] as %a2 ⟨#Hk2, #Ha2⟩
      (try wp_auto)
      iapply HΦ
      iframe HT
      iexists true, true, _
      iframe
      isplitr
      · ipureintro; intro h; cases h
      isplitr
      · iintro !> %E #Hb
        simp only [apply.alarmChain, ↓reduceIte]
        iapply Ha2 $$ %E %_ (Ha1 $$ %E %_ Hb)
      iunfold apply.alarmShape
      iexists a1
      simp only [apply.cappedShape, apply.corruptShape]
      isplitr
      · iexact Hk1
      iexists a2
      iframe Hk2
      ipureintro; rfl
    · iapply HΦ
      iframe HT
      iexists true, false, _
      iframe
      isplitr
      · ipureintro; intro h; cases h
      isplitr
      · iintro !> %E #Hb
        simp only [apply.alarmChain, ↓reduceIte, Bool.false_eq_true]
        iapply Ha1 $$ %E %_ Hb
      iunfold apply.alarmShape
      iexists a1
      simp only [apply.cappedShape, apply.corruptShape]
      isplitr
      · iexact Hk1
      ipureintro; simp
  · (try wp_auto)
    wp_if_destruct
    · have hz : z = false := by
        cases z
        · rfl
        · exfalso; have := Hg2 rfl; rw [this] at Hif; simp at Hif
      subst hz
      wp_apply (hCor base) $$ [] as %a2 ⟨#Hk2, #Ha2⟩
      (try wp_auto)
      iapply HΦ
      iframe HT
      iexists false, true, _
      iframe
      isplitr
      · ipureintro; intro h; cases h
      isplitr
      · iintro !> %E #Hb
        simp only [apply.alarmChain, ↓reduceIte, Bool.false_eq_true]
        iapply Ha2 $$ %E %_ Hb
      iunfold apply.alarmShape
      iexists base
      simp only [apply.cappedShape, apply.corruptShape]
      isplitr
      · ipureintro; simp
      iexists a2
      iframe Hk2
      ipureintro; rfl
    · iapply HΦ
      iframe HT
      iexists false, false, _
      iframe
      isplitr
      · ipureintro; intro _; exact ⟨rfl, rfl⟩
      isplitr
      · iintro !> %E #Hb
        simp only [apply.alarmChain, ↓reduceIte, Bool.false_eq_true]
        iexact Hb
      iunfold apply.alarmShape
      iexists base
      simp only [apply.cappedShape, apply.corruptShape]
      ipureintro; simp

end proof

end EtcdGrove
end Perennial
