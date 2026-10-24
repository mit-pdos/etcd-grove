/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/snapshotSender__post.lean` (rafthttp
stage 7d, D42). Lean-first. The round trip runs on a goroutine, which sends its result on a
one-slot channel (a future, `Future.lean`, whose contract is `postRes`); `post` selects between
the sender's stop channel and that future.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.snapshotSender__post
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.checkPostResponse
public import Spec.go_etcd_io.etcd.pkg.v3.httputil.GracefulClose
public import Spec.context.WithCancelBackground
public import Perennial.Spec.context.Background
public import Perennial.Spec.time.AfterFunc
public import Perennial.Golang.Theory.Chan.Idioms.Future
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

instance responseAndError_countable [FfiSyntax] :
    Pos.Countable go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.responseAndError :=
  .ofInjective (fun x => Pos.Countable.encode (x.resp', x.body', x.err'))
    (by intro a b h; have h := Pos.encode_inj h; cases a; cases b; simp_all)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]
variable [ErrorStringLeaf]

/-- **What the round trip's goroutine sends** for the request `R` to `req` of ticket `γk`: an error
of net/http's (`RoundTrip`'s or the body read's), or no error, a response whose status the
protocol allows, its body's bytes, and the request back. -/
def postRes (Rh : RaftHttp GF) (req : Loc) (R : http.HReq) (γk : GName)
    (v : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.responseAndError) : IProp GF :=
  iprop((⌜v.err' ≠ GoInterface.nil⌝ ∗ http.errStrOk v.err' ∗ http.netErr v.err') ∨
    (⌜v.err' = GoInterface.nil⌝ ∗ ∃ (st : w64) (rd : GoInterface)
        (Hd : List (GoString × GoString) → Prop) (bs : List w8),
      http.respAt v.resp' st rd Hd ∗ (□ ∃ w, (raftProto Rh).resp R γk st w) ∗
      v.body' ↦* bs ∗ http.reqOwn req R))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem rafthttp.snapshotSender.post.wp_proof
    (hCheck : rafthttp.checkPostResponse.spec (GF := GF) (hG := hG))
    (hWithContext : http.WithContext_spec (GF := GF))
    (hReadAll : http.ReadAll_any_spec (GF := GF))
    (hAny : ∀ H : http.HttpNet GF, http.respReadAny_of_spec H)
    (hGraceful : httputil.GracefulClose.spec (GF := GF) (hG := hG))
    (hAfterFunc : time.AfterFunc.spec (GF := GF) (hG := hG))
    (hWithCancel : context.WithCancelBackground.spec (GF := GF) (hG := hG))
    (hBackground : context.Background.spec (GF := GF) (hG := hG)) :
    rafthttp.snapshotSender.post.spec (GF := GF) (hG := hG) := by
  intro Rh s pid req R γk Pre Φs Hpath Hown
  wp_start as ⟨#Hs, Hreq, Hstr, #Hso, Htk, #Hrq⟩
  iunfold snapSenderOk at Hs
  icases Hs with ⟨%tr, %pk, %ps, %r, %ec, %sc, %γs, %lg, %urls, %uvs, %lid, %cid, %rt, %γd, %Rr,
    #Hfrom, #Hto, #Hcid, #Htr, #Hpk, #Hps, #Hr, #Hec, #Hsc, #Hlg, %Hlgnn, #Hurls, #Huvs, #Hrtf,
    #Hrt, #Hpick, #Hpst, #Hraft, #Hstop, #Hreg, %Hmem⟩
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, -, -, -, #HES, #HMR, -, -, -, -, -, -, -, -, -, -, -,
    #Hcells, -, #HcES, -, -, -, -, -, -, -, -, ⟨%dto, #Hdto⟩⟩
  iunfold EtcdGrove.errorsNewVar at HES HMR
  icases HES with ⟨%xES, #HxESg, #HxESM⟩
  icases HMR with ⟨%xMR, #HxMRg, #HxMRM⟩
  simp only [EtcdGrove.errVarCells, EtcdGrove.errVarCell] at *
  icases Hcells with ⟨-, -, ⟨%cMR, #HcMRg, #HcMR⟩, -⟩
  icases HcES with ⟨⟨%cES, #HcESg, #HcES⟩, -⟩
  icombine HxESg HcESg gives %h1
  icombine HxMRg HcMRg gives %h3
  have e1 : xES = cES := by injection h1 with h1; injection h1 with _ h1; exact go.intoVal_inj (V := Loc) h1
  have e3 : xMR = cMR := by injection h3 with h3; injection h3 with _ h3; exact go.intoVal_inj (V := Loc) h3
  subst e1 e3
  wp_apply wp_with_defer as %defer defer
  wp_apply hBackground
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_apply hWithCancel as %ctx' %γc %cancel ⟨#Hcancel, #Hctx⟩
  (try wp_auto)
  wp_apply hWithContext req _ (.stream Pre Φs) ctx' $$ [$Hreq $Hstr] as %req' ⟨Hreq, Hstr⟩
  (try wp_auto)
  wp_apply (chan.wp_make2 (V := go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.responseAndError)
    (W64 1))
  · ipureintro; exact ⟨by decide, by decide⟩
  iintro %rc %γr ⟨#Hrcc, %Hcap, Hro⟩
  simp only [show ¬ (W64 1 = W64 0) by decide, ↓reduceIte]
  imod start_future rc γr _ (Or.inr rfl) $$ Hrcc Hro with ⟨%γf, #Hfut, Haw⟩
  imod future_alloc_promise γf rc (postRes Rh req' R γk) [] $$ Hfut Haw with ⟨Hfl, Haw⟩
  wp_auto_lc 3
  ipersist req
  ipersist s
  ipersist result
  -- the round trip's goroutine
  wp_apply wp_fork $$ [Hreq Hstr Htk Hfl]
  · wp_auto
    iunfold http.roundTripperOk at Hrt
    icases Hrt with ⟨%ti, %Hti, #HRT⟩
    subst Hti
    simp only
    iunfold pipeReg at Hreg
    ihave #Hpa0 := Hreg $$ %R.host %Hown
    ihave #Hpa : http.httpProtoAt R.host ((raftHttpNet Rh).proto R.host) $$ []
    · rw [show (raftHttpNet Rh).proto R.host = raftProto Rh from rfl]
      iexact Hpa0
    ihave #Hrq' : ((raftHttpNet Rh).proto R.host).req R γk $$ []
    · rw [show (raftHttpNet Rh).proto R.host = raftProto Rh from rfl]
      iexact Hrq
    wp_apply HRT $$ [$Hreq $Hstr $Hso $Htk $Hpa $Hrq'] as %resp %rerr ⟨Hreq, Hres⟩
    (try wp_auto)
    icases Hres with (⟨%Herr, #HerrS, #HerrN⟩ | ⟨%Hnil, %rst, %rd, #Hra, #Hrw, Hrr, #Hrc⟩)
    · -- the round trip failed: its error
      cases rerr with
      | nil => exact absurd rfl Herr
      | ok ei =>
      wp_auto
      wp_apply (wp_future_fulfill γf rc _) $$ [Hfl]
      · iframe #
        iunfold Fulfilled
        iexists _
        iframe Hfl
        iunfold postRes
        ileft
        iframe #
        ipureintro; simp
      (try wp_auto)
      itrivial
    subst Hnil
    ihave #Hany := hAny (raftHttpNet Rh) rd R γk rst [] $$ Hrr
    wp_auto
    ipersist resp
    -- the timer: `GracefulClose(resp)`, the body read without a guarantee
    wp_apply hAfterFunc $$ [] as %tm -
    · wp_auto
      wp_apply hGraceful resp rst rd _ $$ [$Hra $Hany]
      (try wp_auto)
      (try (ipureintro; rfl))
      (try itrivial)
    ihave #Hra' := Hra
    iunfold http.respAt at Hra'
    icases Hra' with ⟨#HSC, -, #HBody, %Hrdnn⟩
    (try wp_auto)
    wp_apply hReadAll rd $$ [$Hany] as %sl %berr ⟨%bbs, Hsl, #HbS, #HbN⟩
    (try wp_auto)
    wp_apply (wp_future_fulfill γf rc _) $$ [Hfl Hsl Hreq]
    · iframe #
      iunfold Fulfilled
      iexists _
      iframe Hfl
      iunfold postRes
      by_cases hb : berr = GoInterface.nil
      · iright
        isplitr
        · ipureintro; exact hb
        iexists rst, rd, _, bbs
        iframe; iframe #
        imodintro; simp only [raftProto]; iexact Hrw
      · ileft
        iframe #
        ipureintro; exact hb
    (try wp_auto)
    (try (ipureintro; rfl))
    (try itrivial)
  -- `select` on `stopc` and the result
  (try wp_auto)
  wp_apply_core chan.wp_select_blocking
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
    -- stopped: `errStopped`, after the deferred `cancel()`
    iunfold context.cancelSpec at Hcancel
    wp_apply Hcancel
    · imodintro; itrivial
    iintro -
    wp_auto
    iapply HΦ
    iapply (snapPostErr_errorString _ _ _ _ (by decide)) $$ HxESM HcES HxMRg HcMR
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.responseAndError, inferInstance,
      inferInstance, inferInstance, inferInstance, rc, γf.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · ihave #Hfc := Hfut
      iunfold isFuture at Hfc
      icases Hfc with ⟨#Hch, -⟩
      iexact Hch
    iapply future_await_au γf rc _ _ $$ Hfut [$Hlc1 $Hlc2 $Hlc3 $Haw]
    inext
    iintro %v %P %pre %post %Hpp Hres -
    obtain rfl : P = postRes Rh req' R γk := by
      rcases pre with _ | ⟨a, pre⟩
      · simp only [List.nil_append, List.cons.injEq] at Hpp; exact Hpp.1.symm
      · simp at Hpp
    rcases v with ⟨vresp, vbody, verr⟩
    iunfold postRes at Hres

    wp_auto
    icases Hres with (⟨%Hne, #HeS, #HeN⟩ | ⟨%Hn, %rst, %rd, %Hd, %bs, #Hra, #Hrw, Hb, Hreq⟩)
    · -- the round trip's or the body read's error
      cases verr with
      | nil => exact absurd rfl Hne
      | ok ei =>
      wp_auto
      iunfold context.cancelSpec at Hcancel
      wp_apply Hcancel
      · imodintro; itrivial
      iintro -
      wp_auto
      iapply HΦ
      iunfold snapPostErr
      iframe #
    · -- `checkPostResponse` of the response
      subst Hn
      wp_auto
      wp_apply hCheck lg vresp rst rd vbody bs req' R pid Hd Hlgnn $$ [$Hra $Hb $Hreq]
        as %cerr #Hcerr
      icases Hrw with ⟨%w, #Hw⟩
      ihave %H403 := raftProto_resp_403 Rh R γk rst w $$ Hw
      (try wp_auto)
      iunfold context.cancelSpec at Hcancel
      wp_apply Hcancel
      · imodintro; itrivial
      iintro -
      wp_auto
      iapply HΦ
      iapply snapPostErr_of_postErr rst cerr (H403 (Or.inr Hpath)) $$ Hcerr
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
