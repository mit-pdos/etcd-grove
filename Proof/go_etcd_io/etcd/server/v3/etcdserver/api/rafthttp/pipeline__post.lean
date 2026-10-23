/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/pipeline__post.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipeline__post
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.urlPicker__pick
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.urlPicker__unreachable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.createPostRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.checkPostResponse
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.waitSchedule
public import Spec.context.WithCancelBackground
public import Spec.errors.Is
public import Perennial.Spec.context.Background
public import Perennial.Golang.Theory.Chan.Idioms.Future
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]
variable [ErrorStringLeaf]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem rafthttp.pipeline.post.wp_proof
    (hPick : rafthttp.urlPicker.pick.spec (GF := GF) (hG := hG))
    (hUnreach : rafthttp.urlPicker.unreachable.spec (GF := GF) (hG := hG))
    (hCreate : rafthttp.createPostRequest.spec (GF := GF) (hG := hG))
    (hCheck : rafthttp.checkPostResponse.spec (GF := GF) (hG := hG))
    (hWait : rafthttp.waitSchedule.spec (GF := GF) (hG := hG))
    (hNewBuffer : http.NewBuffer_spec (GF := GF))
    (hWithContext : http.WithContext_spec (GF := GF))
    (hReadAll : ∀ H : http.HttpNet GF, http.ReadAll_resp_spec H)
    (hClose : ∀ H : http.HttpNet GF, http.RespClose_spec H)
    (hWithCancel : context.WithCancelBackground.spec (GF := GF) (hG := hG))
    (hBackground : context.Background.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG)) :
    rafthttp.pipeline.post.spec (GF := GF) (hG := hG) := by
  intro Rh p to d bs st Hw Hto Hns Hrs
  wp_start as ⟨#Hs, Hd, #HP, HO⟩
  iunfold pipeSenderOk at Hs
  icases Hs with ⟨%tr, %pk, %sc, %ec, %γs, %lg, %urls, %uvs, %lid, %cid, %rt, #Htr, #Hpk, #Hsc, #Hec,
    #Hto, #Hlg, %Hlgnn, #Hurls, #Huvs, #Hlid, #Hcid, #Hrtf, #Hrt, #Hpick, #Hstop, #Hreg⟩
  wp_apply wp_with_defer as %defer defer
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, #HRP, #HIV, #HCM, #HES, #HMR, -, -, -, -⟩
  wp_apply hPick pk (peerURL Rh to) $$ [$Hpick] as %u %Hu
  (try wp_auto)
  wp_apply hNewBuffer d bs $$ [$Hd] as %bf Hbf
  (try wp_auto)
  wp_apply hCreate lg u go!"/raft" _ bs _ urls uvs lid cid Hlgnn Hu.1 $$ [$Hbf $Huvs]
    as %req ⟨%hdrs, Hreq⟩
  wp_apply (chan.wp_make2 (V := Unit) (W64 1))
  · ipureintro; exact ⟨by decide, by decide⟩
  iintro %dc %γd ⟨#Hdc, %Hcap, Hdo⟩
  simp only [show ¬ (W64 1 = W64 0) by decide, ↓reduceIte]
  imod start_future (V := Unit) dc γd _ (Or.inr rfl) $$ Hdc Hdo with ⟨%γf, #Hfut, Haw⟩
  imod future_alloc_promise (V := Unit) γf dc (fun _ => iprop(True)) [] $$ Hfut Haw
    with ⟨Hfl, Haw⟩
  wp_auto
  wp_apply hBackground
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_apply hWithCancel as %ctx' %γc %cancel ⟨#Hcancel, #Hctx⟩
  (try wp_auto)
  wp_apply hWithContext req _ ctx' $$ [$Hreq] as %req' Hreq
  (try wp_auto)
  ipersist done
  ipersist cancel
  ipersist p
  -- the canceller: on `done` or `stopc`, `cancel()`
  wp_apply wp_fork $$ [Haw]
  · wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dc, γf.chanName
      isplitr
      · ipureintro; rfl
      isplitr
      · ihave #Hfc := Hfut
        iunfold isFuture at Hfc
        icases Hfc with ⟨#Hch, -⟩
        iexact Hch
      iapply future_await_au (V := Unit) γf dc _ _ $$ Hfut [$Hlc1 $Hlc2 $Hlc3 $Haw]
      inext
      iintro %v %P %pre %post %_ - -
      wp_auto
      iunfold context.cancelSpec at Hcancel
      wp_apply Hcancel
      · imodintro; itrivial
      iintro -
      wp_auto
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γs
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownBroadcastChan_is_chan $$ Hstop
      iapply broadcast_chan_receive $$ Hstop
      iintro ⟨-, -⟩
      (try wp_auto)
      wp_apply hWait
      (try wp_auto)
      iunfold context.cancelSpec at Hcancel
      wp_apply Hcancel
      · imodintro; itrivial
      iintro -
      wp_auto
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  -- `p.tr.pipelineRt.RoundTrip(req)`, with a fresh ticket and the message's deposit
  iunfold http.roundTripperOk at Hrt
  icases Hrt with ⟨%ti, %Hti, #HRT⟩
  subst Hti
  simp only
  imod http.reqTicket_alloc with ⟨%γk, Htk⟩
  imod pipe_deposit Rh.γn.N γk st ⊤ $$ HO with #Hdep
  ihave #Hpr : ((raftHttpNet Rh).proto u.Host').req
      ⟨go!"POST", u.Host', go!"/raft", hdrs, bs⟩ γk $$ []
  · simp only [raftHttpNet]
    iapply raftProto_req_of_pipe _ _ _ rfl
    iunfold pipeReq
    iexists st
    iframe #
    ipureintro
    exact ⟨Hw, by rw [Hto]; exact Hu.2.symm, Hns, Hrs⟩
  iunfold pipeReg at Hreg
  ihave #Hpa0 := Hreg $$ %u.Host' %Hu.2
  ihave #Hpa : http.httpProtoAt u.Host' ((raftHttpNet Rh).proto u.Host') $$ []
  · rw [show (raftHttpNet Rh).proto u.Host' = raftProto Rh from rfl]
    iexact Hpa0
  wp_apply HRT $$ [$Hreq $Htk $Hpa $Hpr]
    as %resp %rerr ⟨Hreq, Hres⟩
  (try wp_auto)
  -- `done <- struct{}{}`: the future fulfilled
  wp_apply (wp_future_fulfill (V := Unit) γf dc ()) $$ [Hfl]
  · iframe #
    iunfold Fulfilled
    iexists _
    iframe Hfl
  icases Hres with (⟨%Herr, #HerrS⟩ | ⟨%Hnil, %rst, %rd, #Hra, #Hrw, Hrr, -⟩)
  · -- `RoundTrip` failed
    cases rerr with
    | nil => exact absurd rfl Herr
    | ok ei =>
      wp_auto
      wp_apply hUnreach pk (peerURL Rh to) u $$ [$Hpick]
      iapply HΦ; iexact HerrS
  subst Hnil
  wp_auto
  iunfold http.respAt at Hra
  icases Hra with ⟨#HSC, ⟨%rhm, %rhs, #HRH, #Hrhs, %Hrhd⟩, #HBody, %Hrdnn⟩
  wp_auto
  cases rd with
  | nil => exact absurd rfl Hrdnn
  | ok ri =>
  wp_auto
  wp_apply hReadAll (raftHttpNet Rh) _ _ γk rst $$ [$Hrr] as %bsl %berr ⟨%bbs, Hbsl, Hrr, #HberrS⟩
  cases berr with
  | ok bei =>
    -- the read failed
    wp_auto
    wp_apply hUnreach pk (peerURL Rh to) u $$ [$Hpick]
    (try wp_auto)
    wp_apply hClose (raftHttpNet Rh) _ ri _ γk rst bbs rfl $$ [$Hrr]
    iintro %_ -
    wp_auto
    iapply HΦ; iexact HberrS
  | nil =>
  wp_auto
  wp_apply hCheck lg resp rst (GoInterface.ok ri) bsl bbs req' _ to (fun _ => True) Hlgnn
    $$ [$Hbsl $Hreq] as %cerr #Hcerr
  · unfold http.respAt
    iframe #
    ipureintro; exact Hrdnn
  -- the member's response is never a `403` (the protocol)
  icases Hrw with ⟨%w, %Hst, -⟩
  have Hst' : rst ≠ W64 403 := Hst.1 trivial
  iunfold postErr at Hcerr
  icases Hcerr with ⟨#HcerrS, (%Hcn | ⟨%H403, -⟩ | ⟨%e, %He, #Hne⟩)⟩
  · -- `nil`
    subst Hcn
    wp_auto
    wp_apply hClose (raftHttpNet Rh) _ ri _ γk rst bbs rfl $$ [$Hrr]
    iintro %_ -
    wp_auto
    iapply HΦ; iexact HcerrS
  · exact absurd H403 Hst'
  · -- another error: `errors.Is(err, errMemberRemoved)` is `false`
    obtain ⟨rfl, Hel⟩ := He
    wp_auto
    wp_apply hUnreach pk (peerURL Rh to) u $$ [$Hpick]
    iunfold EtcdGrove.errorsNewVar at HMR
    icases HMR with ⟨%xr, #Hxr, -⟩
    ihave %Hner := Hne $$ Hxr
    ihave #Herrp : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
    · iPkgInit
    have hpt := (EtcdGrove.errorString_leaf xr).1
    wp_auto
    wp_apply hIs (· = GoInterface.ok e) (fun _ => False) (GoInterface.ok e)
      (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xr)
      (fun tii h => by cases h; exact hpt)
      (errors.treeTyped_pointer e _ Hel.1) $$ [] as %b ⟨-, -, %h3⟩
    · iframe #
      isplitl
      · iapply errors.errorIsTree_leaf e (fun _ => False) _ Hel.2.1 Hel.2.2
      ipureintro; rfl
    cases b
    · wp_auto
      wp_apply hClose (raftHttpNet Rh) _ ri _ γk rst bbs rfl $$ [$Hrr]
      iintro %_ -
      wp_auto
      iapply HΦ; iexact HcerrS
    · exfalso
      obtain ⟨ii, hii, hor⟩ := h3 _ rfl hpt (by simp) rfl
      cases hii
      rcases hor with h | h
      · exact Hner h
      · exact h

end proof

end EtcdGrove
end Perennial
