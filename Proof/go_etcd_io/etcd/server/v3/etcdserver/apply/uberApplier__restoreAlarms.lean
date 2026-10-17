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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.uberApplier.restoreAlarms.wp_proof
    (hCap : apply.newApplierV3Capped.spec (GF := GF) (hG := hG))
    (hCor : apply.newApplierV3Corrupt.spec (GF := GF) (hG := hG)) :
    apply.uberApplier.restoreAlarms.spec (GF := GF) (hG := hG) := by
  intro p ast base a
  wp_start as ⟨#Has, #HGet, #Hbs, Ha⟩
  iunfold apply.alarmGetOk at HGet
  wp_auto
  wp_apply HGet as %s1 -
  wp_apply HGet as %s2 -
  wp_if_destruct
  · -- a `NOSPACE` alarm: capped
    wp_apply (hCap base) $$ [] as %a1 #Ha1
    (try wp_auto)
    wp_if_destruct
    · wp_apply (hCor a1) $$ [] as %a2 #Ha2
      (try wp_auto)
      iapply HΦ
      iexists true, true, _
      iframe
      iintro !> %E #Hb
      simp only [apply.alarmChain, ↓reduceIte]
      iapply Ha2 $$ %E %_ (Ha1 $$ %E %_ Hb)
    · iapply HΦ
      iexists true, false, _
      iframe
      iintro !> %E #Hb
      simp only [apply.alarmChain, ↓reduceIte, Bool.false_eq_true]
      iapply Ha1 $$ %E %_ Hb
  · (try wp_auto)
    wp_if_destruct
    · wp_apply (hCor base) $$ [] as %a2 #Ha2
      (try wp_auto)
      iapply HΦ
      iexists false, true, _
      iframe
      iintro !> %E #Hb
      simp only [apply.alarmChain, ↓reduceIte, Bool.false_eq_true]
      iapply Ha2 $$ %E %_ Hb
    · iapply HΦ
      iexists false, false, _
      iframe
      iintro !> %E #Hb
      simp only [apply.alarmChain, ↓reduceIte, Bool.false_eq_true]
      iexact Hb

end proof

end EtcdGrove
end Perennial
