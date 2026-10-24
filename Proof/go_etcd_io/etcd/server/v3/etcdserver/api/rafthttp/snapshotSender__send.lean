/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/snapshotSender__send.lean` (rafthttp
stage 7d, D42). Lean-first. The request is a snapshot request of the raft protocol: its body
the envelope's frame then the merged message's reader (`createSnapBody`), its contract
`snapSReq` (the message's one-shot part deposited under a fresh ticket, `pipe_deposit`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.snapshotSender__send
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.snapshotSender__post
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.createSnapBody
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.createPostRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.urlPicker__pick
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.urlPicker__unreachable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peerStatus__activate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peerStatus__deactivate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message__fields
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message__CloseWithError
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.github_com.dustin.go_humanize.Bytes
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Uint64
public import Spec.go_uber_org.zap.Error
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues
public import Spec.github_com.prometheus.client_golang.prometheus.GaugeVec__WithLabelValues
public import Spec.github_com.prometheus.client_golang.prometheus.HistogramVec__WithLabelValues
public import Spec.errors.Is
public import Spec.time.Duration__Seconds
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Since

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

/-- A frozen message's snapshot's metadata (what `send` logs, `m.Snapshot.Metadata.GetIndex()`). -/
theorem msgOwn_snapMeta (ml : Loc) (st : MsgSt) (sn : SnapshotM) (h : st.snap = some sn) :
    msgOwn (GF := GF) ml DFrac.discard st ⊢ ∃ ps pm : Loc,
      ml.[raftpb.Message, go!"Snapshot"] ↦□ ps ∗ ps.[raftpb.Snapshot, go!"Metadata"] ↦□ pm ∗
      smOpt pm DFrac.discard sn.Metadata' := by
  unfold msgOwn msgPts msgPtsC
  rw [h]
  iintro H
  iNamed H
  unfold snapOpt ownSnapM
  iNamed Hsn
  iexists ps, pm
  iframe

set_option hygiene false in
/-- A log call (`lg.Info(...)`, `lg.Warn(...)`): its fields (the snapshot's index, strings, the
error), the call. -/
local macro "zap_log" : tactic => `(tactic| (
  repeat' (first
    | (wp_apply hGetIndex pm DFrac.discard sn.Metadata' $$ [Hsm] as Hsm; iframe; iframe #)
    | (wp_apply hZUint64 as %_ -)
    | (wp_apply hZString as %_ -)
    | (wp_apply hZError as %_ -)
    | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
       iintro %_ ⟨-, -⟩)
    | (wp_apply hInfo lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | (wp_apply hWarn lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | wp_auto)))

set_option hygiene false in
/-- `vec.WithLabelValues(to)` of a metric vector of label `To` (`HWLV`, with the vector `v` and its
label fact `Hl`): the `[]string{to}` literal, the call; the metric's spec as `Hmet`. -/
local macro "with_to" HWLV:term:max v:term:max Hl:term:max : tactic => `(tactic| (
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoString) [ts]
  isplitr
  · ipureintro; rfl
  iintro %lsl ⟨Hlsl, -⟩
  (try wp_auto)
  wp_apply ($HWLV $v _ [go!"To"] [ts] _) $$ [Hlsl] as %met ⟨%meti, %Hmeti, #Hmet, -⟩
  · iframe; iframe #
    ipureintro
    refine ⟨$Hl, by simp, fun v hv => ?_⟩
    simp only [List.mem_singleton] at hv
    subst hv; exact utf8Valid_of_ascii _ (Hts ▸ types.idStr_ascii _)
  subst Hmeti))

set_option hygiene false in
/-- `send`'s deferred calls, in reverse: `merged.CloseWithError(err)`, the in-flight gauge's
`Dec()`, `body.Close()`. -/
local macro "send_defers" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hClose m ml rc _ $$ []
  · iframe #
  with_to hGWLV vSI HSIl
  iunfold go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec at Hmet
  icases Hmet with ⟨-, #HDec, -⟩
  wp_apply HDec
  (try wp_auto)
  iunfold rdCloseOk at Hbc
  wp_apply Hbc as %_ -
  (try wp_auto)
  iapply HΦ; itrivial))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem rafthttp.snapshotSender.send.wp_proof
    (hPost : rafthttp.snapshotSender.post.spec (GF := GF) (hG := hG))
    (hBody : rafthttp.createSnapBody.spec (GF := GF) (hG := hG))
    (hCreate : rafthttp.createPostRequest.spec (GF := GF) (hG := hG))
    (hPick : rafthttp.urlPicker.pick.spec (GF := GF) (hG := hG))
    (hUnreach : rafthttp.urlPicker.unreachable.spec (GF := GF) (hG := hG))
    (hActivate : rafthttp.peerStatus.activate.spec (GF := GF) (hG := hG))
    (hDeactivate : rafthttp.peerStatus.deactivate.spec (GF := GF) (hG := hG))
    (hFields : snap.Message.fields.spec (GF := GF) (hG := hG))
    (hClose : snap.Message.CloseWithError.spec (GF := GF) (hG := hG))
    (hGetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (hGetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (hIDString : types.ID.String.spec (GF := GF) (hG := hG))
    (hBytes : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZUint64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (hZError : zap.Error.spec (GF := GF) (hG := hG))
    (hCWLV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hGWLV : prometheus.GaugeVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hHWLV : prometheus.HistogramVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hNE : netErrNotRemoved_spec (GF := GF))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (hSeconds : time.Duration.Seconds.spec (GF := GF) (hG := hG)) :
    rafthttp.snapshotSender.send.spec (GF := GF) (hG := hG) := by
  intro Rh pid s m ml rc
  wp_start as ⟨#Hs, #Hmsg, Hb⟩
  iunfold snapBundleTo at Hb
  icases Hb with ⟨%st, %sn, %D, #Hml, #HP, HO, %Hst, Hrs, #Himg⟩
  obtain ⟨Hsnap, Hsn, Hrsp, Hto⟩ := Hst
  ihave #Hs' := Hs
  iunfold snapSenderOk at Hs'
  icases Hs' with ⟨%tr, %pk, %ps, %r, %ec, %sc, %γs, %lg, %urls, %uvs, %lid, %cid, %rt, %γd, %Rr,
    #Hfrom, #Hto, #Hcid, #Htr, #Hpk, #Hps, #Hr, #Hec, #Hsc, #Hlg, %Hlgnn, #Hurls, #Huvs, #Hrtf,
    #Hrt, #Hpick, #Hpst, #Hraft, #Hstop, #Hreg, %Hmem⟩
  ihave ⟨#HfM, ⟨%tsz, #HfT, %Htsz⟩, %rd, %ri, #HfR, %Hrd, #Hwrap, #Hclose⟩ := hFields m ml rc $$ Hmsg
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, #HSnP, -, -, -, #HMR, -, -, ⟨%vSB, #HSB, %HSBl⟩,
    ⟨%vSF, #HSF, %HSFl⟩, -, -, -, -, -, -, -, -, -, -, ⟨%vSS, #HSS, %HSSl⟩,
    ⟨%vSI, #HSI, %HSIl⟩, ⟨%vSFl, #HSFl', %HSFll⟩, ⟨%vSSec, #HSSec, %HSSecl⟩, -⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_Now as %t0 -
  (try wp_auto)
  wp_apply hGetTo.1 ml DFrac.discard DFrac.discard false st $$ [$Hml] as -
  haveI : go.NotInterface go.uint64 := ⟨by unfold go.uint64; trivial⟩
  (try wp_auto)
  wp_apply hIDString as %ts %Hts
  (try wp_auto)
  wp_apply hBody lg m ml rc st _ Hlgnn Hrsp $$ [$Hrs] as %body ⟨%bs, %bi, ⟨%Hbi, %Hwire, %Hbl⟩, Hbody, #Hbc⟩
  · iframe #
  subst Hbi
  (try wp_auto)
  wp_apply hPick pk (peerURL Rh pid) $$ [$Hpick] as %u %Hu
  (try wp_auto)
  wp_apply hCreate lg u go!"/raft/snapshot" _ (.stream (snapPre bs) (snapPhi bs (fun t => backend.boltImage t D)))
      _ urls uvs lid cid Hlgnn Hu.1 $$ [Hbody $Huvs] as %req ⟨%hdrs, Hreq, Hstr, %Hfrom⟩
  · unfold http.bodyHas; iexact Hbody
  (try wp_auto)
  wp_apply hBytes as %ssz -
  ihave ⟨%psn, %pm, #HmSn, #HmMd, Hsm⟩ := msgOwn_snapMeta ml st sn Hsn $$ Hml
  (try wp_auto)
  rw [_root_.decide_eq_false (show ¬ lg = null from Hlgnn)]
  ihave #Hzp : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hrpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  zap_log
  -- `snapshotSendInflights.WithLabelValues(to).Inc()`
  with_to hGWLV vSI HSIl
  iunfold go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec at Hmet
  icases Hmet with ⟨#HInc, -, -⟩
  wp_apply HInc
  (try wp_auto)
  -- the post: a fresh ticket, the message's one-shot part deposited under it
  imod http.reqTicket_alloc with ⟨%γk, Htk⟩
  imod pipe_deposit Rh.γn.N γk st ⊤ $$ HO with #Hdep
  ihave #Hsr : snapSReq Rh ⟨go!"POST", u.Host', go!"/raft/snapshot", hdrs, []⟩ γk (snapPre bs)
      (snapPhi bs (fun t => backend.boltImage t D)) $$ []
  · iunfold snapSReq
    iexists st, bs, sn, D
    iframe #
    ipureintro
    refine ⟨Hwire, Hbl, by rw [Hto]; exact Hu.2.symm, Hsnap, Hsn, Hrsp, fun x hx => hx,
      fun x hx => hx⟩
  ihave #Hso : http.reqSendOk (raftHttpNet Rh) ⟨go!"POST", u.Host', go!"/raft/snapshot", hdrs, []⟩ γk
      (.stream (snapPre bs) (snapPhi bs (fun t => backend.boltImage t D))) $$ []
  · simp only [http.reqSendOk, raftHttpNet, raftProto, snapStreamed]
    isplitr
    · ipureintro; simp [snapPath]
    imodintro; iexact Hsr
  ihave #Hrq : (raftProto Rh).req ⟨go!"POST", u.Host', go!"/raft/snapshot", hdrs, []⟩ γk $$ []
  · iapply raftProto_req_of_snap _ _ _ rfl rfl
    iunfold snapReq
    ipureintro
    exact ⟨lid, Hfrom, Hmem.1, by rw [Hu.2]; exact Hmem.2⟩
  wp_apply hPost Rh s pid req _ γk (snapPre bs) (snapPhi bs (fun t => backend.boltImage t D)) rfl
      Hu.2 $$ [$Hreq $Hstr $Htk] as %err #Herr
  · iframe #
  (try wp_auto)
  iunfold netRaftOk at Hraft
  icases Hraft with ⟨%rri, %Hrri, -, -, #HRU, #HRS⟩
  subst Hrri
  cases err with
  | nil =>
    -- sent: the peer active, `SnapshotFinish` reported
    (try wp_auto)
    wp_apply hActivate ps $$ [$Hpst]
    (try wp_auto)
    wp_apply hGetTo.1 ml DFrac.discard DFrac.discard false st $$ [$Hml] as -
    (try wp_auto)
    wp_apply HRS
    (try wp_auto)
    rw [_root_.decide_eq_false (show ¬ lg = null from Hlgnn)]
    zap_log
    -- the metrics: the bytes sent, one more snapshot, its time
    with_to hCWLV vSB HSBl
    iunfold prometheus.counterSpec at Hmet
    icases Hmet with ⟨-, #HAdd⟩
    ihave #HA := HAdd $$ %tsz %Htsz
    wp_apply HA
    with_to hCWLV vSS HSSl
    iunfold prometheus.counterSpec at Hmet
    icases Hmet with ⟨#HInc, -⟩
    wp_apply HInc
    (try wp_auto)
    wp_apply wp_Since as %dd -
    (try wp_auto)
    wp_apply hSeconds as %fs -
    with_to hHWLV vSSec HSSecl
    iunfold prometheus.observerSpec at Hmet
    wp_apply Hmet
    send_defers
  | ok ei =>
    -- not sent
    (try wp_auto)
    rw [_root_.decide_eq_false (show ¬ lg = null from Hlgnn)]
    zap_log
    -- `errors.Is(err, errMemberRemoved)` is `false` (`snapPostErr`)
    iunfold EtcdGrove.errorsNewVar at HMR
    icases HMR with ⟨%xr, #Hxr, -⟩
    ihave #Herrp : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
    · iPkgInit
    ihave #HIs : {{ (True : IProp GF) }}
        (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #(GoInterface.ok ei)))
          (Val #(interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #xr)))
        {{ RET #false; True }} $$ []
    · iunfold snapPostErr at Herr
      icases Herr with ⟨-, (%Hn | #HeN | ⟨%e, %He, #Hne⟩)⟩
      · cases Hn
      · iintro !> %Ψ - HΨ
        wp_apply hNE (GoInterface.ok ei) _ $$ []
        · iframe #
        iapply HΨ; itrivial
      · obtain ⟨he, Hel⟩ := He
        cases he
        ihave %Hner := Hne $$ Hxr
        have hpt := (EtcdGrove.errorString_leaf xr).1
        iintro !> %Ψ - HΨ
        wp_apply hIs (· = GoInterface.ok ei) (fun _ => False) (GoInterface.ok ei)
          (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #xr)
          (fun tii h => by cases h; exact hpt)
          (errors.treeTyped_pointer ei _ Hel.1) $$ [] as %b ⟨-, -, %h3⟩
        · iframe #
          isplitl
          · iapply errors.errorIsTree_leaf ei (fun _ => False) _ Hel.2.1 Hel.2.2
          ipureintro; rfl
        cases b
        · iapply HΨ; itrivial
        · exfalso
          obtain ⟨ii, hii, hor⟩ := h3 _ rfl hpt (by simp) rfl
          cases hii
          rcases hor with h | h
          · exact Hner h
          · exact h
    (try wp_auto)
    wp_apply HIs
    (try wp_auto)
    -- the peer unreachable and inactive, `SnapshotFailure` reported
    wp_apply hUnreach pk (peerURL Rh pid) u $$ []
    · iframe #
    (try wp_auto)
    iunfold snapPostErr at Herr
    icases Herr with ⟨#HeS, -⟩
    iunfold http.errStrOk at HeS
    icases HeS with (%Hn | ⟨%ei', %He, #HE, -⟩)
    · cases Hn
    cases He
    wp_apply HE as %es
    (try wp_auto)
    wp_apply hDeactivate ps _ es $$ []
    · iframe #
    (try wp_auto)
    wp_apply hGetTo.1 ml DFrac.discard DFrac.discard false st $$ [$Hml] as -
    (try wp_auto)
    wp_apply HRU
    (try wp_auto)
    wp_apply hGetTo.1 ml DFrac.discard DFrac.discard false st $$ [$Hml] as -
    (try wp_auto)
    wp_apply HRS
    with_to hCWLV vSF HSFl
    iunfold prometheus.counterSpec at Hmet
    icases Hmet with ⟨#HInc, -⟩
    wp_apply HInc
    with_to hCWLV vSFl HSFll
    iunfold prometheus.counterSpec at Hmet
    icases Hmet with ⟨#HInc', -⟩
    wp_apply HInc'
    send_defers

end proof

end EtcdGrove
end Perennial
