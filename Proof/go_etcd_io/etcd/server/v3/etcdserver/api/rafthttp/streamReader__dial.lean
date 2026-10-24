/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/streamReader__dial.lean`
(rafthttp stage 5e-3). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader__dial
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.urlPicker__pick
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.urlPicker__unreachable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamType__endpoint
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.setPeerURLsHeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.serverVersion
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.compareMajorMinorVersion
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.checkStreamSupport
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_etcd_io.etcd.pkg.v3.httputil.GracefulClose
public import Spec.github_com.Masterminds.semver.v3.MustParse
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.path.Join
public import Spec.strings.TrimSuffix
public import Spec.fmt.ErrorfPlain
public import Proof.github_com.Masterminds.semver.v3.Simple
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.IDStr

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

/-- A member id, as an `fmt` argument: its `String()` returns (`fmt.argOk`). -/
theorem id_stringMethodSpec (hIDString : types.ID.String.spec (GF := GF) (hG := hG)) (id : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ⊢
      fmt.stringMethodSpec ⟨go_etcd_io.etcd.client.pkg.v3.types.ID.ty, #id⟩ go!"String" := by
  iintro #Hp
  rw [fmt.stringMethodSpec_unfold]
  iintro !> %Φ HΦ
  iapply hIDString id $$ []
  · iexact Hp
  inext
  iintro %s -
  iapply HΦ

set_option hygiene false in
/-- A log call (`cr.lg.Warn(...)` and the like): its fields' strings, the call. -/
local macro "zap_log" : tactic => `(tactic| (
  repeat' (first
    | (wp_apply hIDStringPtr _ DFrac.discard _ $$ [] as %_ -; iframe #)
    | (wp_apply hZString as %_ -)
    | (wp_apply hZError as %_ -)
    | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
       iintro %_ ⟨-, -⟩)
    | (wp_apply hWarn lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | (wp_apply hDebug lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | wp_auto)))

set_option hygiene false in
/-- `req.Header.Set(k, v)`, `v` an id's string or a loaded string. -/
local macro "req_set" : tactic => `(tactic| (
  (try (wp_apply hIDStringPtr _ DFrac.discard _ $$ [] as %_ -; iframe #))
  (try wp_auto)
  wp_apply hHeaderSetPtr _ hm _ _ _ $$ [Hho] as Hho
  · iframe #; iframe Hho))

set_option hygiene false in
/-- `httputil.GracefulClose(resp)` then `cr.picker.unreachable(u)`. -/
local macro "close_unreach" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hGraceful (raftHttpNet Rh) resp _ rd (fun _ => True) _ γk _ $$ [Hrr]
  · iframe Hrr
    iunfold http.respAt
    iframe #
    (try (isplitr; · (iexists rhm, rhs; iframe #)))
    (try (ipureintro; exact Hrdnn))
  (try wp_auto)
  wp_apply hUnreach pk (peerURL Rh pid) u $$ []
  · iframe #
  (try wp_auto)))

set_option hygiene false in
/-- The return of an `errors.New` error: a package variable's (`HxUSM`, ...) or `fmt.Errorf`'s
without `%w` (`HE`). -/
local macro "ret_err" : tactic => `(tactic| (
  (try wp_auto)
  iapply HΦ
  isplitr
  · first
      | iapply errorString_errStrOk $$ HxUSM
      | iapply errorString_errStrOk $$ HxMRM
      | iapply errorString_errStrOk $$ HxIVM
      | iapply errorString_errStrOk $$ HxCMM
      | iapply errorString_errStrOk $$ HE
  ileft; ipureintro; simp))

set_option hygiene false in
/-- The status switch, from `resp.StatusCode`. -/
local macro "status_switch" : tactic => `(tactic| (
  (try wp_auto)
  by_cases h410 : rst = W64 410
  · -- `410`: never a member's response (no member is removed)
    subst h410
    iexfalso
    icases Hrw with ⟨%w, %H410, -⟩
    exact absurd rfl H410.2
  rw [_root_.decide_eq_false (show ¬ rst = W64 410 from h410)]
  (try wp_auto)
  by_cases h200 : rst = W64 200
  · -- the stream
    subst h200
    (try wp_auto)
    iapply HΦ
    isplitr
    · iapply http.errStrOk_nil
    iright
    isplitr
    · ipureintro; rfl
    iexists _, γk, γw
    iframe
    iframe #
    ipureintro; exact ⟨⟨howner, streamPath_ne_probing _ _⟩, Hrdnn⟩
  rw [_root_.decide_eq_false (show ¬ rst = W64 200 from h200)]
  (try wp_auto)
  ihave #Htyp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  by_cases h404 : rst = W64 404
  · -- the peer does not know this member
    subst h404
    (try wp_auto)
    close_unreach
    wp_apply wp_slice_literal (V := GoInterface)
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply hErrorf _ _ _ _ (by decide) $$ [Hasl] as %x ⟨-, %msg, #HE⟩
    · iframe #; iframe Hasl
      simp only [show sint.nat (W64 (0 + 1)) = 1 by rfl, List.set_cons_succ, List.set_cons_zero,
        fmt.argsOk, fmt.argOk]
      isplitr
      · iright; iright; iapply id_stringMethodSpec hIDString $$ Htyp
      isplitr
      · iright; iright; iapply id_stringMethodSpec hIDString $$ Htyp
      itrivial
    ret_err
  rw [_root_.decide_eq_false (show ¬ rst = W64 404 from h404)]
  (try wp_auto)
  by_cases h412 : rst = W64 412
  · -- a precondition failed: the body says which
    subst h412
    (try wp_auto)
    wp_apply hReadAll (raftHttpNet Rh) _ _ γk _ $$ [Hrr] as %bsl %berr ⟨%bbs, Hbsl, Hrr, #HberrS⟩
    · iframe Hrr
    cases berr with
    | ok bei =>
      -- the read failed: the body closed, the read's error
      (try wp_auto)
      cases rd with
      | nil => exact absurd rfl Hrdnn
      | ok ri =>
        (try wp_auto)
        wp_apply hClose (raftHttpNet Rh) _ ri _ γk _ _ rfl $$ [Hrr]
        · iframe Hrr
        (try iintro %_ -)
        (try wp_auto)
        wp_apply hUnreach pk (peerURL Rh pid) u $$ []
        · iframe #
        (try wp_auto)
        iapply HΦ
        iframe HberrS
        ileft; ipureintro; simp
    | nil =>
      (try wp_auto)
      close_unreach
      wp_apply wp_bytes_to_string _ _ _ $$ [Hbsl] as Hbsl
      · iframe Hbsl
      ihave #Hstrp : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
      · iPkgInit
      wp_apply hTrim as %ts -
      (try wp_auto)
      wp_apply HxIVM
      (try wp_auto)
      by_cases hiv : ts = go!"incompatible version"
      · -- `errIncompatibleVersion`
        rw [_root_.decide_eq_true hiv]
        (try wp_auto)
        rw [_root_.decide_eq_false (show ¬ lg = null from Hlgnn)]
        zap_log
        ret_err
      rw [_root_.decide_eq_false hiv]
      (try wp_auto)
      wp_apply HxCMM
      (try wp_auto)
      by_cases hcm : ts = go!"cluster ID mismatch"
      · -- `ErrClusterIDMismatch`
        rw [_root_.decide_eq_true hcm]
        (try wp_auto)
        rw [_root_.decide_eq_false (show ¬ lg = null from Hlgnn)]
        zap_log
        wp_apply hHeaderGetPtr _ rhm rhs _ $$ []
        · iframe #
        zap_log
        ret_err
      -- another body
      rw [_root_.decide_eq_false hcm]
      (try wp_auto)
      wp_apply wp_bytes_to_string _ _ _ $$ [Hbsl] as Hbsl
      · iframe Hbsl
      (try wp_auto)
      wp_apply wp_slice_literal (V := GoInterface)
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      wp_apply hErrorf _ _ _ _ (by decide) $$ [Hasl] as %x ⟨-, %msg, #HE⟩
      · iframe #; iframe Hasl
        simp only [show sint.nat (W64 (0 + 1)) = 1 by rfl, List.set_cons_succ, List.set_cons_zero,
          fmt.argsOk, fmt.argOk]
        isplitr
        · ileft; ipureintro
          apply fmt.argWf_of_argsWf
          exact .cons_string _ _ .nil
        itrivial
      ret_err
  rw [_root_.decide_eq_false (show ¬ rst = W64 412 from h412)]
  (try wp_auto)
  -- another status
  close_unreach
  wp_apply wp_slice_literal (V := GoInterface)
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_apply hErrorf _ _ _ _ (by decide) $$ [Hasl] as %x ⟨-, %msg, #HE⟩
  · iframe #; iframe Hasl
    simp only [show sint.nat (W64 (0 + 1)) = 1 by rfl, List.set_cons_succ, List.set_cons_zero,
      fmt.argsOk, fmt.argOk]
    isplitr
    · ileft; ipureintro
      apply fmt.argWf_of_argsWf
      exact .cons_int _ _ _ (.int _) .nil
    itrivial
  ret_err))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem rafthttp.streamReader.dial.wp_proof
    (hPick : rafthttp.urlPicker.pick.spec (GF := GF) (hG := hG))
    (hUnreach : rafthttp.urlPicker.unreachable.spec (GF := GF) (hG := hG))
    (hEndpoint : rafthttp.streamType.endpoint.spec (GF := GF) (hG := hG))
    (hJoin : path.Join.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hIDString : types.ID.String.spec (GF := GF) (hG := hG))
    (hHeaderGetPtr : http.HeaderGetPtr_spec (GF := GF))
    (hURLString : http.URLString_spec (GF := GF))
    (hNewRequest : http.NewRequest_spec (GF := GF))
    (hNilBody : ⊢ http.readerHas (GF := GF) GoInterface.nil [])
    (hHeaderSetPtr : http.HeaderSetPtr_spec (GF := GF))
    (hSetPeer : rafthttp.setPeerURLsHeader.spec (GF := GF) (hG := hG))
    (hWithContext : http.WithContext_spec (GF := GF))
    (hServerVersion : rafthttp.serverVersion.spec (GF := GF) (hG := hG))
    (hMP : semver.MustParse.spec (GF := GF) (hG := hG))
    (hCompare : rafthttp.compareMajorMinorVersion.spec (GF := GF) (hG := hG))
    (hCheckSS : rafthttp.checkStreamSupport.spec (GF := GF) (hG := hG))
    (hGraceful : httputil.GracefulClose.spec (GF := GF) (hG := hG))
    (hReadAll : ∀ H : http.HttpNet GF, http.ReadAll_resp_spec H)
    (hClose : ∀ H : http.HttpNet GF, http.RespClose_spec H)
    (hTrim : strings.TrimSuffix.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.ErrorfPlain.spec (GF := GF) (hG := hG))
    (hDebug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZError : zap.Error.spec (GF := GF) (hG := hG)) :
    rafthttp.streamReader.dial.spec (GF := GF) (hG := hG) := by
  intro Rh lid pid γd cr ty
  wp_start as ⟨#Hf, #Hd⟩
  ihave #Hf' := Hf
  iunfold srFixed at Hf'
  icases Hf' with ⟨%lg, %tr, %ps, %rcc, %pcc, %γr, %γp, %ctx, %cd, #Hlg, %Hlgnn, #Hpid, #Htr,
    #Hlid, -, -, -, -, -, -, #Hmu, #Hctxf, #Hctx⟩
  iunfold srDial at Hd
  icases Hd with ⟨#Hcfg, %ec, #Herrc⟩
  iunfold srCfg at Hcfg
  icases Hcfg with ⟨%rl, %pk, %tr', %urls, %uvs, %cid, %rt, %ec', #Htyp, -, -, #Hpk, #Hpick,
    #Htr2, #Hurls, #Huvs, #Hcid, #Hrtf, #Hrt, -, #Hreg, #Hpreg, #HPfx⟩
  icombine Htr Htr2 gives %Htreq
  subst Htreq
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, #HIV, #HCM, -, #HMR, -, -, -, -, -, -, -, -, -, #HUS, -⟩
  ihave #Hpver : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version $$ []
  · iPkgInit
  ihave #Hvi : iprop(globalAddr go_etcd_io.etcd.api.v3.version.Version ↦□ go!"3.8.0-alpha.0" ∗
      (∃ v : github_com.Masterminds.semver.v3.Version,
        globalAddr go_etcd_io.etcd.api.v3.version.V3_6 ↦□ v) ∗
      globalAddr go_etcd_io.etcd.api.v3.version.MinClusterVersion ↦□ go!"3.0.0") $$ []
  · iapply isPkgInit_access $$ Hpver
  icases Hvi with ⟨#HVer, -, #HMCV⟩
  wp_auto
  -- the URL: one of the peer's, its path the stream's
  wp_apply hPick pk (peerURL Rh pid) $$ [] as %u %Hu
  · iframe #
  haveI : go.NotInterface go.string := ⟨by unfold go.string; trivial⟩
  rw [method_unfold (t := go.GoType.PointerType rafthttp.streamType.ty) (m := go!"endpoint")]
  (try wp_auto)
  wp_apply hEndpoint ty lg $$ []
  · iframe #
  wp_apply hIDStringPtr _ DFrac.discard lid $$ [] as %ls ⟨-, %Hls⟩
  · iframe #
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoString)
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  (try wp_auto)
  wp_apply hJoin _ [ty.endpoint, ls] _ (by
      have := types.idStr_length lid
      subst Hls
      cases ty <;> simp [StreamTy.endpoint] <;> omega) $$ [Hsl] as %jp ⟨%Hjp, -⟩
  · simp only [show sint.nat (W64 (0 + 1)) = 1 by rfl, List.set_cons_succ, List.set_cons_zero]
    iframe #; iexact Hsl
  rw [Hls, streamPath_join] at Hjp
  subst Hjp
  (try wp_auto)
  -- `cr.lg.Debug(...)`
  rw [_root_.decide_eq_false Hlgnn]
  (try wp_auto)
  obtain ⟨⟨hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8, hu9, hhost⟩, howner⟩ := Hu
  wp_apply hIDStringPtr _ DFrac.discard lid $$ [] as %_ -
  · iframe #
  wp_apply hZString as %_ -
  wp_apply hIDStringPtr _ DFrac.discard pid $$ [] as %_ -
  · iframe #
  wp_apply hZString as %_ -
  wp_apply hURLString uu_ptr _ { u with Path' := streamPath ty lid } hu1 hu2 hu3 hu4 hu5 hu6 hu7 hu8 hu9 $$ [$uu] as uu
  zap_log
  -- `http.NewRequest("GET", uu.String(), nil)`: no error
  wp_apply hURLString uu_ptr _ { u with Path' := streamPath ty lid } hu1 hu2 hu3 hu4 hu5 hu6 hu7 hu8 hu9 $$ [$uu] as uu
  ihave Hnb := hNilBody
  wp_apply hNewRequest go!"GET" _ GoInterface.nil [] u.Host' (streamPath ty lid) rfl hhost
    (Or.inr rfl) $$ [$Hnb] as %req Hreq
  (try wp_auto)
  -- the headers
  iunfold http.reqOwn at Hreq
  icases Hreq with ⟨%hm, #HHm, Hho, Hrest⟩
  req_set
  req_set
  req_set
  req_set
  req_set
  ihave Hreq : http.reqOwn req ⟨go!"GET", u.Host', streamPath ty lid, _, []⟩ $$ [Hho Hrest]
  · iunfold http.reqOwn
    iexists hm
    iframe #; iframe Hho
    unfold http.reqRest
    iexact Hrest
  (try wp_auto)
  wp_apply hSetPeer req _ urls uvs $$ [$Hreq] as ⟨%hs, Hreq⟩
  · iframe #
  (try wp_auto)
  wp_apply hWithContext req _ ctx $$ [$Hreq] as %req' Hreq
  (try wp_auto)
  ihave #Hfmtp : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  -- the stopped check, under `mu`
  wp_apply sync.Mutex.wp_Lock _ (srLockInv cr) $$ [] as ⟨Hlocked, Hinv⟩
  · iexact Hmu
  (try wp_auto)
  ihave #Hctx2 := Hctx
  iunfold context.isContext at Hctx2
  iunfold context.isContextDef at Hctx2
  iNamed Hctx2
  wp_apply HDone as %dch %γdn #Hdone
  wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)] _ $$ [] [-] []
  rotate_left
  · iNamedAccu
  · -- not stopped
    iintro HP -
    iNamed HP
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hinv]
    · iframe Hmu Hlocked; inext; iexact Hinv
    (try wp_auto)
    -- `cr.tr.streamRt.RoundTrip(req)`, with a fresh ticket registered as the stream's
    iunfold http.roundTripperOk at Hrt
    icases Hrt with ⟨%ti, %Hti, #HRT⟩
    subst Hti
    simp only
    imod stream_ticket_alloc Rh ty lid ⊤ CoPset.subseteq_top $$ Hreg with ⟨%γk, %γw, Htk, #Hsreg, Hrd⟩
    ihave #Hpr : ((raftHttpNet Rh).proto u.Host').req
        ⟨go!"GET", u.Host', streamPath ty lid, hs, []⟩ γk $$ []
    · simp only [raftHttpNet]
      iapply raftProto_req_of_stream _ _ _ rfl
      iunfold streamReq
      iexists (γw, ty, lid)
      iframe #
      ipureintro; rfl
    iunfold pipeReg at Hpreg
    ihave #Hpa0 := Hpreg $$ %u.Host' %howner
    ihave #Hpa : http.httpProtoAt u.Host' ((raftHttpNet Rh).proto u.Host') $$ []
    · rw [show (raftHttpNet Rh).proto u.Host' = raftProto Rh from rfl]
      iexact Hpa0
    wp_apply HRT $$ [$Hreq $Htk $Hpa $Hpr] as %resp %rerr ⟨Hreq, Hres⟩
    (try wp_auto)
    icases Hres with (⟨%Herr, #HerrS⟩ | ⟨%Hnil, %rst, %rd, #Hra, #Hrw, Hrr, #Hrc⟩)
    · -- `RoundTrip` failed
      cases rerr with
      | nil => exact absurd rfl Herr
      | ok ei =>
        wp_auto
        wp_apply hUnreach pk (peerURL Rh pid) u $$ []
        · iframe #
        (try wp_auto)
        iapply HΦ
        iframe HerrS
        ileft; ipureintro; simp
    subst Hnil
    wp_auto
    iunfold http.respAt at Hra
    icases Hra with ⟨#HSC, ⟨%rhm, %rhs, #HRH, #Hrhs, %Hrhd⟩, #HBody, %Hrdnn⟩
    -- the peer's version: its header parses (a member's response, `rhdr`)
    obtain ⟨hs0, Hrh0, Hsv⟩ := Hrhd
    have Hvh : verHdrOk rhs := by
      unfold verHdrOk
      rw [Hsv _ (by decide)]
      exact Hrh0
    (try wp_auto)
    wp_apply hServerVersion rhm rhs Hvh $$ [] as %rv %Hrv
    · iframe #
    (try wp_auto)
    ihave #Hsp : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
    · iPkgInit
    wp_apply hMP as %lvv %Hlv
    obtain ⟨lv, rfl, Hlvnn⟩ : ∃ v : Loc, lvv = #v ∧ v ≠ null := by
      rcases Hlv with ⟨-, h⟩ | ⟨Hn, -⟩
      · exact h
      · exact absurd (semver.semverValid_simple _ (by decide)) Hn
    (try wp_auto)
    wp_apply hCompare rv lv Hrv Hlvnn as %c -
    (try wp_auto)
    iunfold EtcdGrove.errorsNewVar at HUS HMR HIV HCM
    icases HUS with ⟨%xUS, #HxUS, #HxUSM⟩
    icases HMR with ⟨%xMR, #HxMR, #HxMRM⟩
    icases HIV with ⟨%xIV, #HxIV, #HxIVM⟩
    icases HCM with ⟨%xCM, #HxCM, #HxCMM⟩
    by_cases hc : c = W64 (-1)
    · rw [_root_.decide_eq_true hc]
      (try wp_auto)
      wp_apply hCheckSS rv _ Hrv as %b -
      (try wp_auto)
      cases b
      · -- an older peer without this stream type
        (try wp_auto)
        close_unreach
        ret_err
      · (try wp_auto)
        status_switch
    · rw [_root_.decide_eq_false hc]
      (try wp_auto)
      status_switch
  · -- stopped: an error
    iapply BigSepL2.bigSepL2_singleton.2
    iintro HP
    iNamed HP
    simp only [chan.nonblockingAltClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γdn
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_nonblocking_receive _ _ _ _ _ $$ Hdone
    isplit
    · iintro -
      wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hinv]
      · iframe Hmu Hlocked; inext; iexact Hinv
      (try wp_auto)
      ihave Hnil := ownSlice_nil (V := GoInterface) (GF := GF) DFrac.discard
      wp_apply hErrorf _ slice.nil [] DFrac.discard (by decide) $$ [Hnil] as %x ⟨-, %msg, #HM⟩
      · iframe #
        simp only [fmt.argsOk]; itrivial
      (try wp_auto)
      iapply HΦ
      isplitr
      · iapply errorString_errStrOk $$ HM
      ileft; ipureintro; simp
    · simp only [named]
      iframe

end proof

end EtcdGrove
end Perennial
