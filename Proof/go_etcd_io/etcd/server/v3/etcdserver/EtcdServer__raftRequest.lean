/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__raftRequest.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ModeSpecs
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option hygiene false in
/-- The success return: the apply's answer, dispatched, no error. -/
local macro "rr_ok" : tactic => `(tactic| (
  iapply HΦ
  iframe Hrd Hard
  ileft
  isplitr
  · ipureintro; rfl
  iexists hm, rq', L
  isplitr
  · ipureintro; exact Hwire
  iframe HL HpAf Hhb
  isplitr [HQL]
  · iunfold appliedOkM
    iexists y, y', o, skip
    iframe Hcert HMint Hwit Hok
    isplitr
    · ipureintro; exact ⟨Hstep.1, Hstep.2.1, Hstep.2.2.1, Hstep.2.2.2, Hadm⟩
    isplitl [Hans]
    · rw [← hve]
      iexact Hans
    iexact Hau'
  iexact HQL))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem EtcdServer.raftRequest.wp_proofM (on : Bool)
    (hP : EtcdServer.processInternalRaftRequestOnce.specM (GF := GF) (hG := hG) on)
    (hSp : trace.SpanFromContext.spec (GF := GF) (hG := hG))
    (hV : context.ValueStartTime.spec (GF := GF) (hG := hG))
    (hGS : traceutil.Trace.GetStartTime.spec (GF := GF) (hG := hG))
    (hSS : traceutil.Trace.SetStartTime.spec (GF := GF) (hG := hG))
    (hIS : traceutil.Trace.InsertStep.spec (GF := GF) (hG := hG))
    (hLL : traceutil.Trace.LogIfLong.spec (GF := GF) (hG := hG)) :
    EtcdServer.raftRequest.specM (GF := GF) (hG := hG) on := by
  intro s E ρ ctx cd p rq Qh F Hid0 Hdpt
  wp_start as ⟨#Hsrv, Hrd, Hard, Hcred, #Hctx, #Hirr, Hok, Hhdr, #HF⟩
  ihave #Ptrace : isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.trace $$ []
  · iPkgInit
  ihave #Ptu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_auto
  wp_apply hP s E ρ ctx cd p rq Qh F Hid0 Hdpt $$ [Hrd Hard Hcred Hhdr Hok] as %res %err ⟨Hrd, Hard, Hres⟩
  · iframe # Hrd Hard Hcred Hhdr Hok
  (try wp_auto)
  icases Hres with (⟨%Herr, %hm, %rq', %Hwire, HTr, %L, #HL, Hri, #HpAf, HQL, #Hhb⟩ | ⟨%Hres, #HaE, Hdep⟩)
  · subst Herr
    (try wp_auto)
    iunfold resPostM at Hri
    icases Hri with ⟨%Hnn, %y, %y', %out, %Hstep, Hres, #Hcert, HMint, #Hwit, #Hok, #HtM, Hau⟩
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
        iframe Hrd Hard
        iright
        isplitr
        · ipureintro; exact ⟨rfl, by simp⟩
        isplitr
        · rw [← hve]; iexact HerrIs
        ileft
        iexists hm, rq'
        iframe Hhb
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
        iframe Hcert HMint
        isplitr
        · ipureintro; exact ⟨Hstep.1, Hstep.2.1⟩
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
        iframe Hrd Hard
        iright
        isplitr
        · ipureintro; exact ⟨rfl, by simp⟩
        isplitr
        · rw [← hve]; iexact HerrIs
        ileft
        iexists hm, rq'
        iframe Hhb
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
        iframe Hcert HMint
        isplitr
        · ipureintro; exact ⟨Hstep.1, Hstep.2.1⟩
        simp only [apply.applyResultIs, apply.dispatchResult, or_true, ↓reduceIte]
        isplitr
        · ipureintro; exact Hnn
        iexists v
        rw [hve]
        iframe Hv Hans
        rw [← hve]
        iexact HerrIs
      · -- (E3x) no error: an admin request's step succeeded
        ihave %Hadm := adminDoneM_of_tie on ρ.kv rq' L res o skip v hve $$ HtM Hv
        -- (C1's A3) an `Authenticate`'s response
        ihave Hau' := authnAnsM_of_ar on E res rq' o skip v hve $$ Hau Hv
        (try wp_auto)
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
          · -- the result's trace, handed over by the apply thread (`apply.resTrace`)
            iunfold apply.resTrace at HTr
            icases HTr with (%Hrn | ⟨%v', #Hv', HTr⟩)
            · exact absurd Hrn Hnn
            icombine Hv Hv' gives %Hvv
            subst Hvv
            icases HTr with (%He | HTr)
            · exact absurd hve He
            iunfold apply.traceRes at HTr
            icases HTr with (%Htn | ⟨%te, Htrc⟩)
            · exact absurd Htn (by simpa using Hif)
            wp_apply hGS v.Trace' te $$ [$Htrc] as %ast Htrc
            (try wp_auto)
            wp_apply hSS v.Trace' te _ $$ [$Htrc] as Htrc
            (try wp_auto)
            wp_apply hIS v.Trace' te _ _ _ slice.nil $$ [$Htrc] as Htrc
            · isplitl []
              · iapply traceutil.ownFields_nil
              ipureintro; decide
            (try wp_auto)
            wp_apply hLL v.Trace' te _ $$ [$Htrc]
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
      iframe Hrd Hard
      iright
      isplitr
      · ipureintro; exact ⟨rfl, Hne⟩
      isplitr
      · iexact HaE
      iright; iexact Hdep
    · exact absurd rfl Hne

theorem EtcdServer.raftRequest.wp_proof
    (hP : EtcdServer.processInternalRaftRequestOnce.spec (GF := GF) (hG := hG))
    (hSp : trace.SpanFromContext.spec (GF := GF) (hG := hG))
    (hV : context.ValueStartTime.spec (GF := GF) (hG := hG))
    (hGS : traceutil.Trace.GetStartTime.spec (GF := GF) (hG := hG))
    (hSS : traceutil.Trace.SetStartTime.spec (GF := GF) (hG := hG))
    (hIS : traceutil.Trace.InsertStep.spec (GF := GF) (hG := hG))
    (hLL : traceutil.Trace.LogIfLong.spec (GF := GF) (hG := hG)) :
    EtcdServer.raftRequest.spec (GF := GF) (hG := hG) := by
  intro s E ρ
  exact EtcdServer.raftRequest.wp_proofM E.authOn
    (EtcdServer.processInternalRaftRequestOnce.spec_M hP _) hSp hV hGS hSS hIS hLL s E ρ

end proof

end EtcdGrove
end Perennial
