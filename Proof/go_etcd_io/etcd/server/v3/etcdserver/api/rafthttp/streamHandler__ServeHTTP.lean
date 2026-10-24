/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/streamHandler__ServeHTTP.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamHandler__ServeHTTP
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.checkClusterCompatibilityFromHeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamType__endpoint
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newCloseNotifier
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.closeNotifier__Close
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.closeNotifier__closeNotify
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__attachOutgoingConn
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.IDFromString
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.path.Dir
public import Spec.path.Base
public import Proof.github_com.Masterminds.semver.v3.Simple
public import Perennial.Spec.strings.Split

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

set_option hygiene false in
/-- A log call (`h.lg.Warn(...)` and the like): its fields' strings, the call. -/
local macro "zap_log" : tactic => `(tactic| (
  repeat' (first
    | (wp_apply hIDStringPtr _ _ _ $$ [«from»] as %_ ⟨«from», -⟩; iexact «from»)
    | (wp_apply hIDStringPtr _ DFrac.discard _ $$ [] as %_ -; iframe #)
    | (wp_apply hIDString as %_ -)
    | (wp_apply hZString as %_ -)
    | (wp_apply hZError as %_ -)
    | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
       iintro %_ ⟨-, -⟩)
    | (wp_apply hWarn hlg _ _ $$ []; (iframe #; ipureintro; exact Hhvok.1))
    | (wp_apply hDebug hlg _ _ $$ []; (iframe #; ipureintro; exact Hhvok.1))
    | wp_auto)))

set_option hygiene false in
/-- `http.Error(w, msg, code)` of a status other than `200` and `403`, with the headers set
(`Hver`), then the return with the writer. -/
local macro "reply_error" : tactic => `(tactic| (
  wp_apply hError (raftHttpNet Rh) _ a R γk $$ [Hw Hhd] as Hw
  · iframe Hw
    simp only [raftHttpNet]
    isplitr
    · imodintro; iapply raftProto_resp_of <;> decide
    isplitr
    · ipureintro; decide
    simp only [http.hdrsReady]
    iexists _; iframe; ipureintro; exact Hver
  (try wp_auto)
  iframe HRs; unfold http.handlerDone; ileft; iexists _, _; iexact Hw))

set_option hygiene false in
/-- After the switch on the path's `Dir`: the reader's id from its `Base`, then the rest. -/
local macro "stream_rest" : tactic => `(tactic| (
  wp_apply hBase R.path as %bs %Hbs
  rw [Hpath, streamPath_base] at Hbs
  rw [Hbs]
  (try wp_auto)
  wp_apply hIDFrom _ as %fid %ferr ⟨#Hferr, %Hf⟩
  obtain ⟨hfid, hferr⟩ := Hf rid rfl
  rw [hfid, hferr]
  (try wp_auto)
  ihave #Ht3 := HIR $$ %rid
  wp_bind (App (Val #(methods ri.ty go!"IsIDRemoved" ri.v)) (Val #rid))
  iapply Ht3
  · itrivial
  inext
  iintro -
  · -- not removed (no member is: `netRaftOk`'s `IsIDRemoved`): the peer
    (try wp_auto)
    rw [Hhvok.2.2]
    (try wp_auto)
    ihave #HG1 := HGet $$ %rid
    wp_bind (App (Val #(methods gi.ty go!"Get" gi.v)) (Val #rid))
    iapply HG1 $$ [HRs]
    · iexact HRs
    inext
    iintro %pi ⟨HRs, Hpi⟩
    icases Hpi with (%Hnil | ⟨%pl, %Hpl, #Hps⟩)
    · -- no peer: `AddRemote` with the request's `X-PeerURLs`, if any; `404`
      subst Hnil
      (try wp_auto)
      wp_apply hHeaderGetPtr _ hm R.hdr _ $$ []
      · iframe #
      (try wp_auto)
      by_cases hu : http.hdrGet R.hdr go!"X-PeerURLs" = []
      · rw [hu]
        (try wp_auto)
        zap_log
        reply_error
      · rw [_root_.decide_eq_false hu]
        (try wp_auto)
        ihave #Hstrp : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
        · iPkgInit
        wp_apply hSplit _ _ (by decide) as %sl ⟨Hsl, -⟩
        ihave #HA1 := HAddR $$ %rid %sl %_
        wp_bind (App (App (Val (htr @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"AddRemote"))
          (Val #rid)) (Val #sl))
        iapply HA1 $$ [Hsl]
        · iexact Hsl
        inext
        iintro -
        (try wp_auto)
        zap_log
        reply_error
    · -- a peer: `X-Raft-To` must be this member, `412` if not
      subst Hpl
      (try wp_auto)
      wp_apply hIDStringPtr _ DFrac.discard hid $$ [] as %ws ⟨-, %Hws⟩
      · iframe #
      (try wp_auto)
      wp_apply hHeaderGetPtr _ hm R.hdr _ $$ []
      · iframe #
      (try wp_auto)
      by_cases hto : http.hdrGet R.hdr go!"X-Raft-To" = ws
      · -- `200`, flushed; the connection attached to the peer, then the wait for its close
        rw [hto]
        (try wp_auto)
        wp_apply hWriteHeader (raftHttpNet Rh) _ wi a R γk (W64 200) rfl $$ [Hw Hhd] as Hw
        · iframe Hw
          simp only [raftHttpNet]
          isplitr
          · imodintro
            iapply raftProto_resp_stream_200 Rh R γk _ (Hpath ▸ streamPath_ne_raft _ _) $$ Hreg
          isplitr
          · ipureintro; decide
          simp only [http.hdrsReady]
          iexists _; iframe; ipureintro; exact Hver
        rw [ite_cond_eq_true _ _ (eq_true hfl)]
        (try wp_auto)
        wp_apply hFlush (raftHttpNet Rh) _ wi a R γk _ _ rfl $$ [Hw] as Hw
        · iframe Hw
        (try wp_auto)
        wp_apply hNewCN (connBack Rh wi a R γk) as %n ⟨%γ, #Hcr, Hcc, Htok⟩
        (try wp_auto)
        rw [ite_cond_eq_true _ _ (eq_true hfl)]
        (try wp_auto)
        iStructNamed «$r0»
        ipersist t; ipersist Writer; ipersist Flusher; ipersist Closer; ipersist localID
        ipersist peerID
        ihave Hoc : outConnOk Rh ty hid rid «$r0_ptr» $$ [Hw Hcc]
        · iunfold outConnOk
          iexists wi, _, a, R, γk, γw
          iframe #
          iframe Hw
          isplitr
          · ipureintro; exact ⟨Hhost ▸ Hhvok.2.1, Hhost, Hpath⟩
          iunfold closeRight
          iexists _
          isplitr
          · ipureintro; rfl
          iintro %Φ HQ HΦ
          wp_apply hCNClose n γ (connBack Rh wi a R γk) $$ [Hcc HQ]
          · iframe #; iframe
          iapply HΦ
        wp_apply hAttach Rh ty hid rid pl «$r0_ptr» $$ [Hoc]
        · iframe #; iframe
        (try wp_auto)
        -- `<-c.closeNotify()`: the writer given back by the closer
        wp_apply hCNNotify n γ _ $$ [] as %dc ⟨%γc, #Hdc⟩
        · iframe #
        (try wp_auto)
        ihave #Hdcc := ownBroadcastChan_is_chan _ _ _ _ $$ Hdc
        wp_bind (App (Val (chan.receive _)) (Val #dc))
        wp_apply_core chan.wp_receive (V := Unit) dc γc $$ Hdcc
        iintro ⟨Hlc, -, -, -⟩
        iapply broadcast_chan_receive dc γc _ _ .Unknown $$ Hdc
        iintro ⟨#HQ, -⟩
        imod cn_take γ _ $$ HQ Htok with HP
        imod lc_fupd_elim_later $$ Hlc HP with HP
        (try wp_auto)
        iframe HRs; unfold http.handlerDone; ileft
        iunfold connBack at HP
        iexact HP
      · (try simp only [hto, _root_.decide_false, Bool.not_false])
        (try wp_auto)
        zap_log
        reply_error))


set_option maxHeartbeats 8000000 in
theorem rafthttp.streamHandler.ServeHTTP.wp_proof
    (hRespHeader : http.RespHeader_spec (GF := GF))
    (hHeaderSet : http.HeaderSet_spec (GF := GF))
    (hHeaderGetPtr : http.HeaderGetPtr_spec (GF := GF))
    (hError : ∀ H : http.HttpNet GF, http.Error_spec H)
    (hWriteHeader : ∀ H : http.HttpNet GF, http.respWriteHeader_spec H)
    (hFlush : ∀ H : http.HttpNet GF, http.Flush_spec H)
    (hCheck : rafthttp.checkClusterCompatibilityFromHeader.spec (GF := GF) (hG := hG))
    (hEndpoint : rafthttp.streamType.endpoint.spec (GF := GF) (hG := hG))
    (hDir : path.Dir.spec (GF := GF) (hG := hG))
    (hBase : path.Base.spec (GF := GF) (hG := hG))
    (hIDFrom : types.IDFromString.spec (GF := GF) (hG := hG))
    (hIDString : types.ID.String.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hSplit : _root_.Perennial.strings.Split.spec (GF := GF) (hG := hG))
    (hNewCN : rafthttp.newCloseNotifier.spec (GF := GF) (hG := hG))
    (hCNClose : rafthttp.closeNotifier.Close.spec (GF := GF) (hG := hG))
    (hCNNotify : rafthttp.closeNotifier.closeNotify.spec (GF := GF) (hG := hG))
    (hAttach : rafthttp.peer.attachOutgoingConn.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hDebug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZError : zap.Error.spec (GF := GF) (hG := hG)) :
    rafthttp.streamHandler.ServeHTTP.spec (GF := GF) (hG := hG) := by
  intro Rh a γd Rs h wi r R γk rd Hhost Hnp
  iintro #Hpkg #Hh #HR #Hreq Htk Hbody Hw Hhd %hfl HRs
  iunfold streamHandlerOk at Hh
  icases Hh with ⟨%hv, %gi, #Hhv, %Hhvok, #HtrID, #Hraft, #HGet, #HAddR, #HPfx⟩
  iunfold netRaftOk at Hraft
  icases Hraft with ⟨%ri, %Hri, -, #HIR, -, -⟩
  obtain ⟨hlg, htr, hpg, hr, hid, hcid⟩ := hv
  simp only at Hri Hhvok ⊢
  subst Hri
  rw [method_unfold (t := go.GoType.PointerType rafthttp.streamHandler.ty) (m := go!"ServeHTTP")]
  wp_pures
  ihave #HR0 := HR
  iunfold http.reqAt at HR
  icases HR with ⟨#HMeth, ⟨%u, #HU, #HUP⟩, ⟨%hm, #HHm, #Hhs⟩, ⟨%ra, #HRA, %Hra⟩, #HB, %Hrdnn⟩
  iStructNamed Hhv
  wp_auto
  wp_if_destruct
  rotate_left
  · -- not a `GET`: `w.Header().Set("Allow", "GET")`, `405`
    wp_apply hRespHeader _ wi [] rfl $$ [$Hhd] as %hm' ⟨Hhm', Hhcl⟩
    wp_apply hHeaderSet hm' [] $$ [$Hhm'] as Hhm'
    ihave Hhd := Hhcl $$ Hhm'
    have Hver : verHdrOk (http.hdrSet [] go!"Allow" go!"GET") :=
      verHdrOk_set _ _ _ (by decide) verHdrOk_nil
    (try wp_auto)
    wp_apply hError (raftHttpNet Rh) _ a R γk $$ [$Hw Hhd] as Hw
    · simp only [raftHttpNet]
      isplitr
      · imodintro; iapply raftProto_resp_of <;> decide
      isplitr
      · ipureintro; decide
      simp only [http.hdrsReady]
      iexists _; iframe; ipureintro; exact Hver
    (try wp_auto)
    iframe HRs; unfold http.handlerDone; ileft; iexists _, _; iexact Hw
  -- a `GET`: a stream request
  ihave Hsr := raftProto_req_stream Rh R γk $$ Hreq
  ihave #Hsr := Hsr $$ %(And.intro Hif Hnp)
  iunfold streamReq at Hsr
  icases Hsr with ⟨%c, #Hreg, %Hpath⟩
  obtain ⟨γw, ty, rid⟩ := c
  simp only at Hpath
  ihave #Hpver : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version $$ []
  · iPkgInit
  ihave #Hvi : iprop(globalAddr go_etcd_io.etcd.api.v3.version.Version ↦□ go!"3.8.0-alpha.0" ∗
      (∃ v : github_com.Masterminds.semver.v3.Version,
        globalAddr go_etcd_io.etcd.api.v3.version.V3_6 ↦□ v) ∗
      globalAddr go_etcd_io.etcd.api.v3.version.MinClusterVersion ↦□ go!"3.0.0") $$ []
  · iapply isPkgInit_access $$ Hpver
  icases Hvi with ⟨#HVer, -⟩
  (try wp_auto)
  -- `w.Header().Set("X-Server-Version", version.Version)`
  wp_apply hRespHeader _ wi [] rfl $$ [$Hhd] as %hm1 ⟨Hhm', Hhcl⟩
  wp_apply hHeaderSet hm1 [] $$ [$Hhm'] as Hhm'
  ihave Hhd := Hhcl $$ Hhm'
  (try wp_auto)
  -- `w.Header().Set("X-Etcd-Cluster-ID", h.cid.String())`
  wp_apply hIDStringPtr _ DFrac.discard hcid $$ [$cid] as %cs ⟨-, %Hcs⟩
  wp_apply hRespHeader _ wi _ rfl $$ [$Hhd] as %hm2 ⟨Hhm', Hhcl⟩
  wp_apply hHeaderSet hm2 _ $$ [$Hhm'] as Hhm'
  ihave Hhd := Hhcl $$ Hhm'
  have Hver : verHdrOk (http.hdrSet (http.hdrSet [] go!"X-Server-Version" go!"3.8.0-alpha.0")
      go!"X-Etcd-Cluster-ID" cs) := by
    apply verHdrOk_set _ _ _ (by decide)
    right
    rw [http.hdrGet_hdrSet_eq]
    exact semver.semverValid_simple _ (by decide)
  -- the header check
  wp_apply hCheck hlg hid hcid hm R.hdr Hhvok.1 $$ [$Hhs] as %rv Hrv
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, -, #HIV, #HCM, -⟩
  icases Hrv with (%Hrv | ⟨%e, %Hre, #He⟩)
  · rcases Hrv with rfl | ⟨p, rfl⟩
    · -- compatible: the stream's type from the path's `Dir`
      (try wp_auto)
      wp_apply hDir R.path as %dr %Hdr
      rw [Hpath, streamPath_dir] at Hdr
      subst Hdr
      (try wp_auto)
      have e2 : rafthttp.streamTypeMsgAppV2 = #(StreamTy.msgAppV2.str) := rfl
      have e1 : rafthttp.streamTypeMessage = #(StreamTy.message.str) := rfl
      simp only [e1, e2]
      haveI : go.NotInterface go.string := ⟨by unfold go.string; trivial⟩
      (try wp_auto)
      wp_apply hEndpoint .msgAppV2 _ $$ []
      · iframe #
      (try wp_auto)
      by_cases hty : ty = StreamTy.msgAppV2
      · rw [_root_.decide_eq_true (show ty.endpoint = StreamTy.msgAppV2.endpoint by rw [hty])]
        (try wp_auto)
        rw [show StreamTy.msgAppV2.str = ty.str by rw [hty]]
        stream_rest
      · have hty' : ty = StreamTy.message := by cases ty <;> simp_all
        rw [_root_.decide_eq_false (show ty.endpoint ≠ StreamTy.msgAppV2.endpoint by rw [hty']; decide)]
        (try wp_auto)
        wp_apply hEndpoint .message _ $$ []
        · iframe #
        (try wp_auto)
        rw [_root_.decide_eq_true (show ty.endpoint = StreamTy.message.endpoint by rw [hty'])]
        (try wp_auto)
        rw [show StreamTy.message.str = ty.str by rw [hty']]
        stream_rest
    · -- a panic, before any write: the writer given back uncommitted
      wp_auto
      iframe HRs; unfold http.handlerDone; iright
      isplitr
      · ipureintro; rfl
      iexact Hw
  · -- one of the check's two errors: `412`, its message
    subst Hre
    icases He with (#He | #He)
    · iunfold EtcdGrove.errorsNewVar at HIV
      icases HIV with ⟨%x, #Hx, #HErr⟩
      icombine He Hx gives %Heq
      subst Heq
      wp_auto
      wp_apply HErr
      wp_apply hError (raftHttpNet Rh) _ a R γk $$ [$Hw Hhd] as Hw
      · simp only [raftHttpNet]
        isplitr
        · imodintro; iapply raftProto_resp_of <;> decide
        isplitr
        · ipureintro; decide
        simp only [http.hdrsReady]
        iexists _; iframe; ipureintro; exact Hver
      (try wp_auto)
      iframe HRs; unfold http.handlerDone; ileft; iexists _, _; iexact Hw
    · iunfold EtcdGrove.errorsNewVar at HCM
      icases HCM with ⟨%x, #Hx, #HErr⟩
      icombine He Hx gives %Heq
      subst Heq
      wp_auto
      wp_apply HErr
      wp_apply hError (raftHttpNet Rh) _ a R γk $$ [$Hw Hhd] as Hw
      · simp only [raftHttpNet]
        isplitr
        · imodintro; iapply raftProto_resp_of <;> decide
        isplitr
        · ipureintro; decide
        simp only [http.hdrsReady]
        iexists _; iframe; ipureintro; exact Hver
      (try wp_auto)
      iframe HRs; unfold http.handlerDone; ileft; iexists _, _; iexact Hw

end proof

end EtcdGrove
end Perennial
