/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/snapshotHandler__ServeHTTP.lean`
(rafthttp stage 7e, D42). Lean-first. A `POST` to the snapshot path is a snapshot sender's
(`snapReq`) with a streamed body of the contract `snapSReq`: the envelope decoded from the body's
prefix is the sender's message (`msgFrame_prefix_eq`: frames comparable with its frame are its
frame), and the rest is a bbolt image of the certificate's data, which `SaveDBFrom` saves.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.snapshotHandler__ServeHTTP
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.checkClusterCompatibilityFromHeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageDecoder__decodeLimit
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__SaveDBFrom
public import Spec.google_golang_org.protobuf.proto.SizeMessage
public import Spec.fmt.SprintfArgs
public import Spec.errors.AsLeaf
public import Spec.context.TODO
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TodoCtx
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Uint64
public import Spec.go_uber_org.zap.Int
public import Spec.go_uber_org.zap.Int64
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues
public import Spec.github_com.prometheus.client_golang.prometheus.GaugeVec__WithLabelValues
public import Spec.github_com.prometheus.client_golang.prometheus.HistogramVec__WithLabelValues
public import Spec.github_com.dustin.go_humanize.Bytes
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.time.Duration__String_ptr
public import Spec.time.Duration__Seconds
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Since
public import Proof.github_com.mit_pdos.etcd_grove.FirstCallee

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **Frames of encodings below `2^63` bytes, one a prefix of the other, are of one encoding.** -/
theorem msgFrame_prefix_eq {bs bs' : List w8} (hl : bs.length < 2 ^ 63) (hl' : bs'.length < 2 ^ 63)
    (h : msgFrame bs' <+: msgFrame bs ∨ msgFrame bs <+: msgFrame bs') : bs' = bs := by
  rcases h with ⟨x, hx⟩ | ⟨x, hx⟩
  · unfold msgFrame at hx
    exact (chunk_eq (x := x) (y := []) hl' hl (by rw [List.append_nil]; exact hx)).1
  · unfold msgFrame at hx
    exact (chunk_eq (x := x) (y := []) hl hl' (by rw [List.append_nil]; exact hx)).1.symm

/-- **A streamed request body is a reader** (`readFullAt`) of its stream's prefixes. -/
theorem bodyStream_readFullAt (hRF : http.ReadFull_stream_spec (GF := GF)) (rd : GoInterface)
    (Pre Φ : List w8 → Prop) :
    ⊢ readFullAt (GF := GF) rd (http.bodyStream rd Pre Φ) (fun rs => iprop(⌜Pre rs⌝)) := by
  unfold readFullAt
  iintro !> %p %xs %rs %Ψ !> ⟨Hp, Hs⟩ HΨ
  wp_apply (hRF rd Pre Φ rs p xs) $$ [$Hs $Hp] as %n %err ⟨%ys, %Hys, Hp, Hs, #He⟩
  iapply HΨ
  iexists ys
  iframe
  iframe #
  isplitr
  · imodintro; ipureintro; exact Hys.2.2.2
  ipureintro; exact ⟨Hys.1, Hys.2.1, Hys.2.2.1⟩

/-- A message's snapshot's metadata, read out of an owned message and put back. -/
theorem msgPtsC_snapMeta (ml : Loc) (dq dqe : DFrac) (cap : Bool) (st : MsgSt) (sn : SnapshotM)
    (h : st.snap = some sn) :
    msgPtsC (GF := GF) ml dq dqe cap st ⊢ ∃ ps pm : Loc,
      ml.[raftpb.Message, go!"Snapshot"] ↦{dq} ps ∗ ps.[raftpb.Snapshot, go!"Metadata"] ↦{dq} pm ∗
      smOpt pm dq sn.Metadata' ∗
      (ml.[raftpb.Message, go!"Snapshot"] ↦{dq} ps -∗ ps.[raftpb.Snapshot, go!"Metadata"] ↦{dq} pm -∗
        smOpt pm dq sn.Metadata' -∗ msgPtsC ml dq dqe cap st) := by
  unfold msgPtsC
  rw [h]
  iintro H
  iNamed H
  have Hml := Hnn
  unfold snapOpt ownSnapM
  iNamed Hsn
  iexists ps, pm
  iframe HSn HM Hm
  iintro HSn HM Hm
  iexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  iframe
  iframe #
  isplitr
  · ipureintro; exact Hml
  iexists _, _, _
  iframe
  iframe #
  ipureintro; exact Hnn

/-- An error whose `Error()` returns is a formatting argument (`fmt.argOk`). -/
theorem argOk_of_errStrOk [_root_.Perennial.fmt.Assumptions] (e : GoInterface) :
    http.errStrOk (GF := GF) e ⊢ fmt.argOk e := by
  unfold http.errStrOk
  iintro (%h | ⟨%ei, %h, #HE, -⟩)
  · subst h; unfold fmt.argOk; itrivial
  · subst h; unfold fmt.argOk; iright; ileft; unfold fmt.stringMethodSpec; iexact HE

/-- One error whose `Error()` returns is a formatting argument list (`fmt.argsOk`). -/
theorem argsOk_of_errStrOk [_root_.Perennial.fmt.Assumptions] (e : GoInterface) :
    http.errStrOk (GF := GF) e ⊢ fmt.argsOk [e] := by
  iintro #He
  unfold fmt.argsOk fmt.argsOk
  isplitr
  · iapply argOk_of_errStrOk $$ He
  itrivial

/-- An application to a panic is that panic. -/
theorem wp_app_panic (e : Expr) (q : val) (Φ : val → IProp GF) :
    Φ (PanicV q) ⊢ WP (App e (Val (PanicV q))) {{ Φ }} :=
  wp_unwind [EctxItem.AppRCtx e] (by simp [EctxItem.unwinds]) q Φ

/-- A member's protocol of a `POST` to the snapshot path: a snapshot request. -/
theorem raftProto_req_snap (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) :
    (raftProto Rh).req R γk ⊢ ⌜R.meth = go!"POST" ∧ R.path = snapPath⌝ → snapReq Rh R γk := by
  show iprop((⌜R.meth = go!"POST" ∧ R.path = go!"/raft"⌝ → pipeReq Rh R γk) ∗
    (⌜R.meth = go!"GET" ∧ R.path ≠ probingPath⌝ → streamReq Rh R γk) ∗
    (⌜R.meth = go!"POST" ∧ R.path = snapPath⌝ → snapReq Rh R γk)) ⊢ _
  iintro ⟨-, -, Hs⟩
  iexact Hs

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

set_option hygiene false in
/-- `http.Error(w, msg, code)` or `w.WriteHeader(code)` of a status other than `403`, `200` and
`410`, the headers set (`Hhd`, `Hver`): the writer committed (`Hw`). -/
local macro "resp_ok" : tactic => `(tactic| (
  simp only [raftHttpNet]
  isplitr
  · imodintro; iapply raftProto_resp_of <;> decide
  isplitr
  · ipureintro; decide
  simp only [http.hdrsReady]
  iexists _; iframe; ipureintro; exact Hver))

set_option hygiene false in
/-- `vec.WithLabelValues(x)` of a metric vector of label `From` (`HWLV`, with the vector `v` and
its label fact `Hl`), `x` ASCII by `hx`: the `[]string{x}` literal, the call; the metric's spec as
`Hmet`. -/
local macro "with_from" HWLV:term:max v:term:max Hl:term:max x:term:max hx:term:max :
    tactic => `(tactic| (
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoString) [$x]
  isplitr
  · ipureintro; rfl
  iintro %lsl ⟨Hlsl, -⟩
  (try wp_auto)
  wp_apply ($HWLV $v _ [go!"From"] [$x] _) $$ [Hlsl] as %met ⟨%meti, %Hmeti, #Hmet, -⟩
  · iframe; iframe #
    ipureintro
    refine ⟨$Hl, by simp, fun v hv => ?_⟩
    simp only [List.mem_singleton] at hv
    subst hv; exact utf8Valid_of_ascii _ $hx
  subst Hmeti))

set_option hygiene false in
/-- A counter's `Inc()` (`Hmet`, `counterSpec`). -/
local macro "cnt_inc" : tactic => `(tactic| (
  iunfold prometheus.counterSpec at Hmet
  icases Hmet with ⟨#HInc, -⟩
  wp_apply HInc))

set_option hygiene false in
/-- A log call's fields and the call. -/
local macro "zap_log" : tactic => `(tactic| (
  repeat' (first_callee
    | "GetIndex" => (wp_apply hGetIndex pm (DFrac.own 1) sn.Metadata' $$ [Hsm] as Hsm; iframe; iframe #)
    | "String" => (wp_apply hIDStringPtr _ DFrac.discard hv.localID' as %_ ⟨-, %_⟩; iframe #)
    | "zap.Uint64" => (wp_apply hZUint64 as %_ -)
    | (wp_apply hZInt as %_ -)
    | "zap.Int64" => (wp_apply hZInt64 as %_ -)
    | "zap.String" => (wp_apply hZString as %_ -)
    | "zap.Error" => (wp_apply hZError as %_ -)
    | "go_humanize.Bytes" => (wp_apply hBytes as %_ -)
    | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
       iintro %_ ⟨-, -⟩)
    | "Info" => (wp_apply hInfo hv.lg' _ _ $$ []; (iframe #; ipureintro; exact Hhvok.1))
    | "Warn" => (wp_apply hWarn hv.lg' _ _ $$ []; (iframe #; ipureintro; exact Hhvok.1))
    | wp_auto)))

set_option hygiene false in
/-- `fmt.Sprintf(format, err)` of an error whose `Error()` returns (`He`, `errStrOk`). -/
local macro "sprintf_err" e:term:max : tactic => `(tactic| (
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoInterface) [$e]
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  (try wp_auto)
  wp_apply hSprintf _ _ _ (DFrac.own 1) $$ [Hasl] as %msg -
  · iframe
    iapply argsOk_of_errStrOk $$ He))

set_option hygiene false in
/-- The deferred `snapshotReceiveInflights.WithLabelValues(from).Dec()`. -/
local macro "run_dec" : tactic => `(tactic| (
  (try wp_auto)
  with_from hGWLV vRI HRIl fs (Hfs ▸ types.idStr_ascii _)
  iunfold go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec at Hmet
  icases Hmet with ⟨-, #HDec, -⟩
  wp_apply HDec
  (try wp_auto)))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
theorem rafthttp.snapshotHandler.ServeHTTP.wp_proof
    (hRespHeader : http.RespHeader_spec (GF := GF))
    (hHeaderSet : http.HeaderSet_spec (GF := GF))
    (hError : ∀ H : http.HttpNet GF, http.Error_spec H)
    (hWriteHeader : ∀ H : http.HttpNet GF, http.respWriteHeader_spec H)
    (hBodyRead : http.bodyStreamRead_spec (GF := GF))
    (hReadFull : http.ReadFull_stream_spec (GF := GF))
    (hCheck : rafthttp.checkClusterCompatibilityFromHeader.spec (GF := GF) (hG := hG))
    (hDecode : rafthttp.messageDecoder.decodeLimit.spec (GF := GF) (hG := hG))
    (hSave : snap.Snapshotter.SaveDBFrom.spec (GF := GF) (hG := hG))
    (hSize : proto.SizeMessage.spec (GF := GF) (hG := hG))
    (hSprintf : fmt.SprintfArgs.spec (GF := GF) (hG := hG))
    (hAs : errors.AsLeaf.spec (GF := GF) (hG := hG))
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZError : zap.Error.spec (GF := GF) (hG := hG))
    (hZUint64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (hZInt : zap.Int'.spec (GF := GF) (hG := hG))
    (hZInt64 : zap.Int64.spec (GF := GF) (hG := hG))
    (hIDString : types.ID.String.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hCWLV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hGWLV : prometheus.GaugeVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hHWLV : prometheus.HistogramVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hBytes : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (hGetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (hGetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (hGetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (hDurString : time.Duration.String_ptr.spec (GF := GF) (hG := hG))
    (hSeconds : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (hAsT : errors.AsTarget rafthttp.writerToResponse.ty) :
    rafthttp.snapshotHandler.ServeHTTP.spec (GF := GF) (hG := hG) := by
  intro Rh a γd Rs h wi r R γk rd Hhost Hpath
  iintro #Hpkg #Hh #HR #Hreq Htk Hbody Hw Hhd HRs
  iunfold snapHandlerOk at Hh
  icases Hh with ⟨%hv, %Rm, #Hhv, %Hhvok, #Hraft, #Hss, #Hdir, #Haddr⟩
  rw [method_unfold (t := go.GoType.PointerType rafthttp.snapshotHandler.ty) (m := go!"ServeHTTP")]
  wp_auto
  ihave #HR0 := HR
  iunfold http.reqAt at HR
  icases HR with ⟨#HMeth, ⟨%u, #HU, #HUP⟩, ⟨%hm, #HHm, #Hhs⟩, ⟨%ra, #HRA, %Hra⟩, #HB, %Hrdnn⟩
  iStructNamed Hhv
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, -, #HIV, #HCM, #HES, -, ⟨%vRB, #HRB, %HRBl⟩,
    ⟨%vRF, #HRF, %HRFl⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%vR, #HRc, %HRl⟩,
    ⟨%vRI, #HRI, %HRIl⟩, ⟨%vRFl, #HRFl, %HRFll⟩, ⟨%vRS, #HRS, %HRSl⟩, -, -⟩
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_Now as %t0 -
  (try wp_auto)
  wp_if_destruct
  · -- a `POST`: `w.Header().Set("X-Etcd-Cluster-ID", h.cid.String())`
    wp_apply hIDStringPtr _ DFrac.discard hv.cid' $$ [$cid] as %cs ⟨-, %_⟩
    wp_apply hRespHeader _ wi [] rfl $$ [$Hhd] as %hm' ⟨Hhm', Hhcl⟩
    wp_apply hHeaderSet hm' [] $$ [$Hhm'] as Hhm'
    ihave Hhd := Hhcl $$ Hhm'
    have Hver : verHdrOk (http.hdrSet [] go!"X-Etcd-Cluster-ID" cs) :=
      verHdrOk_set _ _ _ (by decide) verHdrOk_nil
    -- the header check
    wp_apply hCheck hv.lg' hv.localID' hv.cid' hm R.hdr Hhvok.1 $$ [$Hhs] as %rv Hrv
    icases Hrv with (%Hrv | ⟨%e, %Hre, #He⟩)
    · rcases Hrv with rfl | ⟨p, rfl⟩
      · -- `nil`: `addRemoteFromRequest(h.tr, r)`
        wp_auto
        ihave #Hsr0 : snapReq Rh R γk $$ []
        · iapply raftProto_req_snap $$ Hreq
          ipureintro; exact ⟨Hif, Hpath⟩
        iunfold snapReq at Hsr0
        icases Hsr0 with %Hfrom
        wp_apply Haddr $$ [$HR0]
        · ipureintro; rw [← Hhvok.2, ← Hhost]; exact Hfrom
        -- the body: a stream of the protocol's contract
        iunfold http.reqBody at Hbody
        icases Hbody with (⟨%Hns, -⟩ | ⟨-, %Pre, %Φ, #Hsreq, %Hpc, Hbs⟩)
        · exfalso; exact Hns ⟨Hif, Hpath⟩
        rw [show ((raftHttpNet Rh).proto a).sreq R γk Pre Φ = snapSReq Rh R γk Pre Φ from rfl]
        iunfold snapSReq at Hsreq
        icases Hsreq with ⟨%st0, %bs0, %sn, %D, %Hs0, #HP, #Hdep, #Himg⟩
        obtain ⟨Hw0, Hbl0, Hto0, Hty0, Hsn0, Hrs0, HPre, HPhi⟩ := Hs0
        -- `dec := &messageDecoder{r: r.Body}`; `dec.decodeLimit(snapshotLimitByte)`
        iStructNamedSuffix «$r0» "_d"
        ipersist r_d
        iclear __d
        (try wp_auto)
        ihave #Hrf := bodyStream_readFullAt hReadFull rd Pre Φ
        wp_apply hDecode «$r0_ptr» rd (http.bodyStream rd Pre Φ) (fun rs => iprop(⌜Pre rs⌝)) []
            (W64 67108864) (by decide) $$ [$Hbs] as %ml %err ⟨#Herr, %Hml, %rs', Hbs, Hok⟩
        · iframe #
          iintro !> %bs %Hb
          ipureintro
          intro hl
          have := msgFrame_prefix_eq Hbl0 hl (HPre _ Hb)
          subst this
          exact ⟨st0, Hw0⟩
        ihave #Hzp : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
        · iPkgInit
        ihave #Hrpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
        · iPkgInit
        haveI : go.NotInterface go.uint64 := ⟨by unfold go.uint64; trivial⟩
        cases err with
        | ok ei =>
          -- the envelope does not decode: `400`
          have Hmn : ml = null := by rcases Hml with h | h <;> first | exact h | cases h
          subst Hmn
          (try wp_auto)
          wp_apply hGetFrom.2
          wp_apply hIDString _ as %fs %Hfs
          ihave #He := Herr
          sprintf_err (GoInterface.ok ei)
          zap_log
          wp_apply hError (raftHttpNet Rh) _ a R γk $$ [$Hw Hhd] as Hw
          · resp_ok
          with_from hCWLV vRF HRFl ra Hra
          cnt_inc
          with_from hCWLV vRFl HRFll fs (Hfs ▸ types.idStr_ascii _)
          cnt_inc
          (try wp_auto)
          iframe HRs; unfold http.handlerDone; ileft; iexists _, _; iexact Hw
        | nil =>
          ihave ⟨%bs, %st, %Hb, #HB, Hm⟩ := Hok $$ %rfl
          ihave %HBp := HB
          obtain ⟨Hrs', Hbl, Hwire⟩ := Hb
          simp only [List.nil_append] at Hrs'
          subst Hrs'
          have hbs : bs = bs0 := msgFrame_prefix_eq Hbl0 (by word) (HPre _ HBp)
          subst hbs
          have Hweq : wireEq st0 st := pbMessage_wire_eq Hw0 Hwire
          (try wp_auto)
          wp_apply hGetFrom.1 ml _ _ _ st $$ [$Hm] as Hm
          wp_apply hIDString st.msg.From' as %fs %Hfs
          (try wp_auto)
          -- `receivedBytes.WithLabelValues(from).Add(float64(proto.Size(m)))`
          wp_apply hSize ml _ _ _ st $$ [$Hm] as %msz ⟨Hm, %Hmsz⟩
          with_from hCWLV vRB HRBl fs (Hfs ▸ types.idStr_ascii _)
          iunfold prometheus.counterSpec at Hmet
          icases Hmet with ⟨-, #HAdd⟩
          ihave #HA := HAdd $$ %msz %Hmsz
          wp_apply HA
          -- the type: the sender's `MsgSnap`
          (try wp_auto)
          wp_apply hGetType.1 ml _ _ _ st $$ [$Hm] as Hm
          rw [Hweq.1, Hty0]
          -- `snapshotReceiveInflights.WithLabelValues(from).Inc()`, its `Dec()` deferred
          with_from hGWLV vRI HRIl fs (Hfs ▸ types.idStr_ascii _)
          iunfold go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec at Hmet
          icases Hmet with ⟨#HInc, -, -⟩
          wp_apply HInc
          (try wp_auto)
          -- the log, reading the snapshot's index
          have Hsn' : st.snap = some sn := by rw [Hweq.2.2.1]; exact Hsn0
          ihave ⟨%psn, %pm, Hmsn, Hmmd, Hsm, Hclose⟩ := msgPtsC_snapMeta ml _ _ _ st sn Hsn' $$ Hm
          zap_log
          -- `n, err := h.snapshotter.SaveDBFrom(r.Body, index)`: the rest of the body, an image of `D`
          ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
          · iPkgInit
          ihave #Heof0 := io.eof_of_init $$ Hio
          iunfold errors.newVar at Heof0
          icases Heof0 with ⟨%xe, #Heof, -⟩
          ihave #Hsro := http.bodyStream_streamReaderOk hBodyRead rd Pre Φ
            (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xe) Hrdnn
          wp_apply hSave hv.snapshotter' rd (http.bodyStream rd Pre Φ) Pre Φ _ (msgFrame bs)
              sn.Metadata'.Index' D γd Rh.γn.N.img Rm
              (fun t ht => by
                obtain ⟨t', he, hi⟩ := HPhi _ ht
                rw [List.append_cancel_left he]; exact hi) $$ [$Hbs]
            as %n %serr ⟨#He, %t, Hbs, Hsok⟩
          · iframe #
            unfold http.ioEOF; iexact Heof
          cases serr with
          | ok ei =>
            -- not saved: `500`
            sprintf_err (GoInterface.ok ei)
            zap_log
            wp_apply hError (raftHttpNet Rh) _ a R γk $$ [$Hw Hhd] as Hw
            · resp_ok
            with_from hCWLV vRFl HRFll fs (Hfs ▸ types.idStr_ascii _)
            cnt_inc
            run_dec
            iframe HRs; unfold http.handlerDone; ileft; iexists _, _; iexact Hw
          | nil =>
            ihave ⟨%Hsv, #Hsaved⟩ := Hsok $$ %rfl
            (try wp_auto)
            -- `receivedBytes.WithLabelValues(from).Add(float64(n))`
            with_from hCWLV vRB HRBl fs (Hfs ▸ types.idStr_ascii _)
            iunfold prometheus.counterSpec at Hmet
            icases Hmet with ⟨-, #HAdd'⟩
            ihave #HA' := HAdd' $$ %n %Hsv.2
            wp_apply HA'
            (try wp_auto)
            wp_apply (lc := 1) wp_Since as %dd -
            zap_log
            wp_apply hDurString downloadTook_ptr dd $$ [$downloadTook] as %ds downloadTook
            zap_log
            -- `h.r.Process(context.TODO(), m)`: the decoded message, with its bundle
            ihave Hm := Hclose $$ Hmsn Hmmd Hsm
            wp_apply hTODO
            iunfold netRaftOk at Hraft
            icases Hraft with ⟨%ri, %Hri, #HProc, -⟩
            rw [Hri]
            wp_auto
            -- the one-shot part, withdrawn with the request's ticket
            iapply wp_fupd
            imod pipe_withdraw Rh.γn.N γk st0 ⊤ (by simp) $$ Hdep Htk Hlc1 with HO
            ihave #Hctx : nodeCtx (GF := GF) todoCtxVal bgCd $$ []
            · iunfold nodeCtx
              ileft
              iunfold doneNilCtx
              imodintro
              iapply wp_todoCtx_Done'
            wp_apply HProc $$ %todoCtxVal %bgCd %ml [$HRs HO Hm] as %perr ⟨#Hperr, HRs⟩
            · iframe #
              iunfold netRecv
              iexists st0, st
              iframe Hm HO HP
              isplitr
              · ipureintro
                refine ⟨Hweq, ?_, Hwire.1⟩
                rw [Hto0, Hhost]; exact Hhvok.2
              iunfold netSnapRecv
              iintro -
              iexists sn
              iframe #
              ipureintro; exact Hsn0
            iunfold nodeErr at Hperr
            icases Hperr with (%Hpn | #Hps | #Hpc)
            · -- `nil`: `204`
              subst Hpn
              wp_auto
              wp_apply hWriteHeader (raftHttpNet Rh) _ wi a R γk (W64 204) rfl $$ [$Hw Hhd] as Hw
              · resp_ok
              with_from hCWLV vR HRl fs (Hfs ▸ types.idStr_ascii _)
              cnt_inc
              (try wp_auto)
              wp_apply wp_Since as %dd' -
              (try wp_auto)
              wp_apply hSeconds as %fsec -
              with_from hHWLV vRS HRSl fs (Hfs ▸ types.idStr_ascii _)
              iunfold prometheus.observerSpec at Hmet
              wp_apply Hmet
              run_dec
              imodintro
              wp_pures
              iframe HRs; unfold http.handlerDone; ileft; iexists _, _; iexact Hw
            · -- `ErrStopped`: not a `writerToResponse`; `500`
              ihave #Hpraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
              · iPkgInit
              ihave #Hrinit := go_etcd_io.raft.v3.isInitialized_access $$ Hpraft
              unfold go_etcd_io.raft.v3.isInitialized
              icases Hrinit with ⟨%e1, %e2, %e3, %e4, %e5, %_, %_, %_, %_, %_, #Hrinit⟩
              iNamed Hrinit
              iunfold errStopped at Hps
              icases Hps with ⟨#Hps, %Hpsn⟩
              iunfold EtcdGrove.errorsNewVar at ErrStoppedNew
              icases ErrStoppedNew with ⟨%xs, #Hxs, #HxsM⟩
              icombine Hps Hxs gives %Heq
              subst Heq
              ihave #He := errorString_errStrOk xs _ $$ HxsM
              simp only [interface.mkOk] at *
              wp_auto
              wp_apply hAs xs writerErr_ptr (zero_val _) hAsT (ErrorStringLeaf.leaf _)
                ErrorStringNotWriter.notIn $$ [$writerErr] as writerErr
              sprintf_err (GoInterface.ok ⟨go.GoType.PointerType errors.errorString.ty, #xs⟩)
              zap_log
              wp_apply hError (raftHttpNet Rh) _ a R γk $$ [$Hw Hhd] as Hw
              · resp_ok
              with_from hCWLV vRFl HRFll fs (Hfs ▸ types.idStr_ascii _)
              cnt_inc
              run_dec
              imodintro
              wp_pures
              iframe HRs; unfold http.handlerDone; ileft; iexists _, _; iexact Hw
            · -- a context error: none, `TODO()`'s context is never done
              iunfold ctxErr at Hpc
              icases Hpc with ⟨-, #Hf, -, -⟩
              simp only [bgCd]
              iexfalso
              iexact Hf
      · -- a panic, before any write: the writer given back uncommitted
        cases hp : p.isPanic
        · wp_auto
          iframe HRs; unfold http.handlerDone; iright
          isplitr
          · ipureintro; rfl
          iexact Hw
        · obtain ⟨q, rfl⟩ : ∃ q, p = PanicV q := by cases p <;> simp_all
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
        · resp_ok
        with_from hCWLV vRFl HRFll go!"UNKNOWN_SNAPSHOT_SENDER" (by unfold asciiStr; decide)
        cnt_inc
        iframe HRs; unfold http.handlerDone; ileft; iexists _, _; iexact Hw
      · iunfold EtcdGrove.errorsNewVar at HCM
        icases HCM with ⟨%x, #Hx, #HErr⟩
        icombine He Hx gives %Heq
        subst Heq
        wp_auto
        wp_apply HErr
        wp_apply hError (raftHttpNet Rh) _ a R γk $$ [$Hw Hhd] as Hw
        · resp_ok
        with_from hCWLV vRFl HRFll go!"UNKNOWN_SNAPSHOT_SENDER" (by unfold asciiStr; decide)
        cnt_inc
        iframe HRs; unfold http.handlerDone; ileft; iexists _, _; iexact Hw
  -- not a `POST`: `w.Header().Set("Allow", "POST")`, `405`
  wp_apply hRespHeader _ wi [] rfl $$ [$Hhd] as %hm' ⟨Hhm', Hhcl⟩
  wp_apply hHeaderSet hm' [] $$ [$Hhm'] as Hhm'
  ihave Hhd := Hhcl $$ Hhm'
  have Hver : verHdrOk (http.hdrSet [] go!"Allow" go!"POST") :=
    verHdrOk_set _ _ _ (by decide) verHdrOk_nil
  wp_apply hError (raftHttpNet Rh) _ a R γk $$ [$Hw Hhd] as Hw
  · resp_ok
  with_from hCWLV vRFl HRFll go!"UNKNOWN_SNAPSHOT_SENDER" (by unfold asciiStr; decide)
  cnt_inc
  iframe HRs; unfold http.handlerDone; ileft; iexists _, _; iexact Hw

end proof

end EtcdGrove
end Perennial
