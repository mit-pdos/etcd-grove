/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__raftRequest.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__raftRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__processInternalRaftRequestOnce
public import Spec.go_opentelemetry_io.otel.trace.SpanFromContext
public import Spec.context.ValueStartTime
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__GetStartTime
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__SetStartTime
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__InsertStep
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__LogIfLong

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option hygiene false in
/-- The success return: the apply's answer, dispatched, no error. -/
local macro "rr_ok" : tactic => `(tactic| (
  iapply HΦ
  iframe Hrd
  ileft
  isplitr
  · ipureintro; rfl
  iexists hm, rq'
  isplitr
  · ipureintro; exact Hwire
  iunfold appliedOk
  iexists y, y', o, skip
  iframe Hcert
  isplitr
  · ipureintro; exact Hstep
  rw [← hve]
  iexact Hans))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem EtcdServer.raftRequest.wp_proof
    (hP : EtcdServer.processInternalRaftRequestOnce.spec (GF := GF) (hG := hG))
    (hSp : trace.SpanFromContext.spec (GF := GF) (hG := hG))
    (hV : context.ValueStartTime.spec (GF := GF) (hG := hG))
    (hGS : traceutil.Trace.GetStartTime.spec (GF := GF) (hG := hG))
    (hSS : traceutil.Trace.SetStartTime.spec (GF := GF) (hG := hG))
    (hIS : traceutil.Trace.InsertStep.spec (GF := GF) (hG := hG))
    (hLL : traceutil.Trace.LogIfLong.spec (GF := GF) (hG := hG)) :
    EtcdServer.raftRequest.spec (GF := GF) (hG := hG) := by
  intro s E ρ ctx cd p rq Hid0
  wp_start as ⟨#Hsrv, Hrd, Hcred, #Hctx, #Hirr, Hhdr⟩
  ihave #Ptrace : isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.trace $$ []
  · iPkgInit
  ihave #Ptu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_auto
  wp_apply hP s E ρ ctx cd p rq Hid0 $$ [Hrd Hcred Hhdr] as %res %err ⟨Hrd, Hres⟩
  · iframe # Hrd Hcred Hhdr
  (try wp_auto)
  icases Hres with (⟨%Herr, %hm, %rq', %Hwire, Hri⟩ | ⟨%Hres, #HaE, Hdep⟩)
  · subst Herr
    (try wp_auto)
    iunfold resultIs at Hri
    icases Hri with ⟨%Hnn, %y, %y', %out, %Hstep, Hres, #Hcert⟩
    rcases out with _ | _ | ⟨o, skip⟩
    · simp only [apply.applyResultIs]
      icases Hres with %Hn
      exact absurd Hn Hnn
    · simp only [apply.applyResultIs]
      ihave #Hrej := Hres
      ihave #Hres' := Hrej
      iunfold apply.rejectedResultIs at Hres'
      icases Hres' with ⟨-, %v, #Hv, %Hv', #HerrIs⟩
      obtain ⟨HvE, -⟩ := Hv'
      ihave Hv2 := Hv
      iStructNamed Hv2
      (try wp_auto)
      rcases hve : v.Err' with ei | _
      · rw [hve] at HvE
        (try wp_auto)
        iapply HΦ
        iframe Hrd
        iright
        isplitr
        · ipureintro; exact ⟨rfl, by simp⟩
        isplitr
        · rw [← hve]; iexact HerrIs
        ileft
        iexists hm, rq'
        isplitr
        · ipureintro; exact Hwire
        iunfold appliedErr
        iexists res, v
        iframe Hv
        isplitr
        · ipureintro; exact hve
        iunfold resultIs
        isplitr
        · ipureintro; exact Hnn
        iexists y, y', .rejected
        iframe Hcert
        isplitr
        · ipureintro; exact Hstep
        simp only [apply.applyResultIs]
        iexact Hrej
      · rw [hve] at HvE; exact absurd rfl HvE
    · simp only [apply.applyResultIs, apply.dispatchResult, or_true, ↓reduceIte]
      icases Hres with ⟨-, %v, #Hv, Hans, #HerrIs⟩
      ihave Hv2 := Hv
      iStructNamed Hv2
      (try wp_auto)
      rcases hve : v.Err' with ei | _
      · (try wp_auto)
        iapply HΦ
        iframe Hrd
        iright
        isplitr
        · ipureintro; exact ⟨rfl, by simp⟩
        isplitr
        · rw [← hve]; iexact HerrIs
        ileft
        iexists hm, rq'
        isplitr
        · ipureintro; exact Hwire
        iunfold appliedErr
        iexists res, v
        iframe Hv
        isplitr
        · ipureintro; exact hve
        iunfold resultIs
        isplitr
        · ipureintro; exact Hnn
        iexists y, y', .dispatched o skip
        iframe Hcert
        isplitr
        · ipureintro; exact Hstep
        simp only [apply.applyResultIs, apply.dispatchResult, or_true, ↓reduceIte]
        isplitr
        · ipureintro; exact Hnn
        iexists v
        rw [hve]
        iframe Hv Hans
        rw [← hve]
        iexact HerrIs
      · (try wp_auto)
        wp_apply hV ctx _ cd rfl $$ [] as %val %Hval
        · iframe #
        rcases Hval with rfl | ⟨tm, rfl⟩
        · (try wp_auto)
          rr_ok
        · simp only [interface.mkOk, ↓reduceIte]
          (try wp_auto)
          wp_if_destruct
          · (try wp_auto)
            rr_ok
          · wp_apply hGS v.Trace' $$ [] as %ast -
            · iframe #; ipureintro; simpa using Hif
            (try wp_auto)
            wp_apply hSS v.Trace' $$ []
            · iframe #; ipureintro; simpa using Hif
            (try wp_auto)
            wp_apply hIS v.Trace' $$ []
            · iframe #; ipureintro; simpa using Hif
            (try wp_auto)
            wp_apply hLL v.Trace' $$ []
            · iframe #; ipureintro; simpa using Hif
            (try wp_auto)
            rr_ok
  · obtain ⟨rfl, Hne⟩ := Hres
    rcases err with ei | _
    · (try wp_auto)
      wp_apply hSp ctx cd $$ [] as %sp #Hsp
      · iframe #
      iunfold trace.isSpan at Hsp
      icases Hsp with ⟨%si, %Hsi, -, -, #HRec⟩
      subst Hsi
      (try wp_auto)
      wp_apply HRec
      (try wp_auto)
      iapply HΦ
      iframe Hrd
      iright
      isplitr
      · ipureintro; exact ⟨rfl, Hne⟩
      isplitr
      · iexact HaE
      iright; iexact Hdep
    · exact absurd rfl Hne

end proof

end EtcdGrove
end Perennial
