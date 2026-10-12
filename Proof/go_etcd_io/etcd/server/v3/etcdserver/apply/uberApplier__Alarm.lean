/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__Alarm
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__restoreAlarms

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

theorem apply.uberApplier.Alarm.wp_proof
    (hR : apply.uberApplier.restoreAlarms.spec (GF := GF) (hG := hG)) :
    apply.uberApplier.Alarm.spec (GF := GF) (hG := hG) := by
  intro E p opts c a r am log Pre Q Post
  wp_start as ⟨#Hu, Ha, #Hs, #Hr, Hpre⟩
  ihave #Hs' := Hs
  iunfold apply.applierSpec at Hs'
  icases Hs' with ⟨%ai, %Hai, #Ht⟩
  subst Hai
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, -, -, #HResp, -⟩
  ihave #Hr' := Hr
  iunfold apply.alarmRequestIs at Hr'
  icases Hr' with ⟨%Hrnn, #Hact, -, -⟩
  wp_auto
  wp_apply HResp $$ %go!"Alarm" %r %log %Pre %Q %Post [] [Hpre] as %resp %err ⟨Hpost, #HeI⟩
  · ipureintro; simp [apply.respMethods]
  · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
    iframe Hpre
    iexists am
    iexact Hr
  wp_if_destruct
  · -- `ACTIVATE`: the chain the alarms ask for
    wp_apply (hR E p opts (.ok ai)) $$ [Ha] as ⟨%ns, %cr, Hown⟩
    · iframe #
      iexact Ha
    iunfold apply.uberOwn at Hown
    icases Hown with ⟨%a', Ha', #Hs''⟩
    iapply HΦ
    iframe Hpost HeI
    iexists a', (apply.alarmChain ns cr)
    iframe Ha' Hs''
    ipureintro; right; exact ⟨ns, cr, rfl⟩
  wp_if_destruct
  · -- `DEACTIVATE`: likewise
    wp_apply (hR E p opts (.ok ai)) $$ [Ha] as ⟨%ns, %cr, Hown⟩
    · iframe #
      iexact Ha
    iunfold apply.uberOwn at Hown
    icases Hown with ⟨%a', Ha', #Hs''⟩
    iapply HΦ
    iframe Hpost HeI
    iexists a', (apply.alarmChain ns cr)
    iframe Ha' Hs''
    ipureintro; right; exact ⟨ns, cr, rfl⟩
  · -- `GET` (or another action): the chain as it is
    iapply HΦ
    iframe Hpost HeI
    iexists (.ok ai), c
    iframe Ha Hs
    ipureintro; left; exact ⟨rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
