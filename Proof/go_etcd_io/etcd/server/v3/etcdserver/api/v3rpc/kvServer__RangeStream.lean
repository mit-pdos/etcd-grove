/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart); auth-mediation M3 (2026-11-21).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer__RangeStream
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkRangeStreamRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.togRPCError
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.headerFillingRangeStream__Send
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKV

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.kvServer.RangeStream.wp_proof
    (hChk : v3rpc.checkRangeStreamRequest.spec (GF := GF) (hG := hG))
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG))
    (hSend : v3rpc.headerFillingRangeStream.Send.spec (GF := GF) (hG := hG))
    (hRS : EtcdServer.RangeStream.spec (GF := GF) (hG := hG)) :
    v3rpc.kvServer.RangeStream.spec (GF := GF) (hG := hG) := by
  intro p s A cid mid nt E ρ γr c ctx cd tok r o rs Ψ Ξ ot te n hany
  wp_start as ⟨#Hsrv, #Hpe, #Hreq, #Hrd, #HaLb, #Hpub, Hcall, #HrsC, #Hctx, #Hlib, #HtokC, #Hct, Hto,
    Hr, #Hsend, #HΞ, #HΨ⟩
  ihave #Hsrv' := Hsrv
  iunfold v3rpc.kvServerIs at Hsrv'
  icases Hsrv' with ⟨%Hpn, #Hhdr, #Hkv, -, -, -, -⟩
  wp_auto
  wp_apply (hChk r (DFrac.own 1) o) $$ [Hr] as %err ⟨Hr, Herr⟩
  · iframe #; iapply (rangeRequestOwn_at r o).mp $$ Hr
  ihave Hr := (rangeRequestOwn_at r o).mpr $$ Hr
  cases hc : v3rpc.rangeCheck o with
  | some ce =>
    simp only
    icases Herr with #Herr
    ihave He := Herr
    iunfold txn.errVarIs at He
    icases He with ⟨%ee, -, %Hee⟩
    subst Hee
    wp_auto
    iapply HΦ
    iframe Hcall Herr
    iapply rangeRequestBack_of_own $$ Hr
  | none =>
    simp only
    icases Herr with %Herr
    have Hvst : txn.validSortTarget o := v3rpc.validSortTarget_of_rangeCheck o hc
    rcases err with ⟨ei⟩ | _
    · -- `checkRangeStreamRequest`'s `Unimplemented`
      wp_auto
      iapply HΦ
      iframe Hcall
      isplitl [Hr]
      · iapply rangeRequestBack_of_own $$ Hr
      ileft
      ipureintro
      exact ⟨fun h => absurd (Herr.2 h) (by intro h; cases h), by intro h; cases h⟩
    have Hok : v3rpc.streamOk o := Herr.1 rfl
    wp_auto
    -- the wrapped stream
    iunfold v3rpc.streamSendOk at Hsend
    icases Hsend with ⟨%si, %Hsi, #HSend⟩
    iunfold rangeStreamCtx at HrsC
    icases HrsC with ⟨%si', %Hsi', #HCtx⟩
    rw [Hsi] at Hsi'
    cases Hsi'
    wp_alloc wl as Hw
    iStructNamed Hw
    ipersist KV_RangeStreamServer
    ipersist hdr
    wp_auto
    wp_apply (hRS s E ρ γr c ctx cd tok r o
        (interface.mkOk (go.GoType.PointerType v3rpc.headerFillingRangeStream.ty) #wl)
        (fun resp => iprop(∃ (rr h : Loc),
          structFieldRef etcdserverpb.RangeStreamResponse go!"RangeResponse" resp ↦□ rr ∗ ⌜rr ≠ null⌝ ∗
          structFieldRef etcdserverpb.RangeResponse go!"Header" rr ↦□ h ∗
          ((⌜h = null⌝ ∗ Ψ resp) ∨ (v3rpc.hdrW h ∗ (v3rpc.hdrFilled h cid mid -∗ Ψ resp)))))
        Ξ ot te n hany) $$ [Hcall Hto Hr]
      as %e ⟨Hcall, Hback, Hres⟩
    · iframe # Hcall Hto Hr
      isplitr
      · -- the wrapper's promoted `Context`
        iunfold rangeStreamCtx
        iexists _
        isplitr
        · ipureintro; rfl
        iintro %Φ' !> - HΦ'
        dsimp only
        rw [MethodUnfold.method_unfold (t := go.GoType.PointerType v3rpc.headerFillingRangeStream.ty)
          (m := go!"Context")]
        wp_auto
        rw [Hsi]
        wp_auto
        wp_bind (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
        iapply HCtx
        · itrivial
        iintro !> -
        iapply HΦ'; itrivial
      isplitr
      · ipureintro; exact Hvst
      isplitr
      · -- the wrapper's `Send`
        iunfold rangeSendOk
        iexists _
        isplitr
        · ipureintro; rfl
        iintro %resp %Φ' !> ⟨%rr, %h, #Hrr, %Hrrn, #Hh, Hpre⟩ HΦ'
        wp_apply (hSend wl _ s A cid mid rs Ψ Ξ resp rr h) $$ [Hpre] as %err' HΞ'
        · iframe #
          iframe Hpre
          isplitr
          · iunfold v3rpc.streamSendOk; iexists si; isplitr
            · ipureintro; exact Hsi
            iexact HSend
          ipureintro; exact Hrrn
        iapply HΦ'
        iexact HΞ'
      -- each chunk: its header `nil`, or owned and filled before `Ψ`
      iintro !> %resp Hch #HC
      iunfold rangeChunkIs at Hch
      icases Hch with ⟨%rr, %sl, %ps, %kvs, #Hrr, %Hrrn, Hhd, #Hkvs, #Hps, #Hkvi, %Hin⟩
      iexists rr
      icases Hhd with (#Hhn | Hown)
      · iexists null
        iframe Hrr Hhn
        isplitr
        · ipureintro; exact Hrrn
        ileft
        isplitr
        · ipureintro; rfl
        iapply HΨ $$ [] HC
        iunfold v3rpc.rangeChunkOut
        iexists rr, sl, ps, kvs
        iframe Hrr Hkvs Hps Hkvi
        isplitr
        · ipureintro; exact Hrrn
        isplitr
        · ileft; iexact Hhn
        ipureintro; exact Hin
      · iunfold txn.respHdrOwn at Hown
        icases Hown with ⟨%h, #Hhf, %Hhn, %c0, %m0, %t0, %l0, Hc, Hm, Ht, Hl⟩
        iexists h
        iframe Hrr Hhf
        isplitr
        · ipureintro; exact Hrrn
        iright
        isplitl [Hc Hm Ht Hl]
        · iunfold v3rpc.hdrW
          isplitr
          · ipureintro; exact Hhn
          iexists c0, m0, t0, l0
          iframe Hc Hm Ht Hl
        iintro Hf
        iapply HΨ $$ [Hf] HC
        iunfold v3rpc.rangeChunkOut
        iexists rr, sl, ps, kvs
        iframe Hrr Hkvs Hps Hkvi
        isplitr
        · ipureintro; exact Hrrn
        isplitl [Hf]
        · iright; iexists h; iframe Hhf Hf
        ipureintro; exact Hin
    icases Hres with (%He | ⟨%He, #HeE, #HeW⟩ | ⟨%resp, HΞr⟩)
    · subst He
      wp_auto
      iapply HΦ
      iframe Hcall Hback
      iright
      isplitr
      · ipureintro; exact Hok
      ileft; ipureintro; rfl
    · cases e with
      | nil => exact absurd rfl He
      | ok ei =>
        wp_auto
        ihave #HsE := v3rpc.srvErrIs_of_applyErrIs _ He $$ HeE
        ihave #HmE := v3rpc.errMsgP_of_srvErrIs _ $$ HsE
        wp_apply hTog (fun _ => True) _ $$ [] as %e' ⟨%He', -, #Hgo⟩
        · iframe #
        iapply HΦ
        iframe Hcall Hback
        iright
        isplitr
        · ipureintro; exact Hok
        iright; ileft
        iexists (GoInterface.ok ei)
        iframe HeE HeW Hgo
        ipureintro; exact He
    · cases e with
      | nil =>
        wp_auto
        iapply HΦ
        iframe Hcall Hback
        iright
        isplitr
        · ipureintro; exact Hok
        iright; iright
        iexists resp, GoInterface.nil
        iframe HΞr
        ileft; ipureintro; exact ⟨rfl, rfl⟩
      | ok ei =>
        ihave ⟨HΞr, #HsE⟩ := HΞ $$ %resp %(GoInterface.ok ei) %(by intro h; cases h) HΞr
        ihave #HmE := v3rpc.errMsgP_of_srvErrIs _ $$ HsE
        wp_auto
        wp_apply hTog (fun _ => True) _ $$ [] as %e' ⟨%He', -, #Hgo⟩
        · iframe #
        iapply HΦ
        iframe Hcall Hback
        iright
        isplitr
        · ipureintro; exact Hok
        iright; iright
        iexists resp, GoInterface.ok ei
        iframe HΞr
        iright
        iframe Hgo
        ipureintro; intro h; cases h

end proof

end EtcdGrove
end Perennial
