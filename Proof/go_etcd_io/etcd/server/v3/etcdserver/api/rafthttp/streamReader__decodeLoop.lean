/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/streamReader__decodeLoop.lean`.
Lean-first; the reader's lemmas: `rafthttp/Reader.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader__decodeLoop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader__close
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newMsgAppV2Decoder
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peerStatus__isActive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.isLinkHeartbeatMessage
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__String
public import Spec.google_golang_org.protobuf.proto.SizeMessage
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Bool

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
/-- The loop continues past the frame `(w, bs)`, the tokens moved past it (`Hrd`). -/
local macro "dl_next" : tactic => `(tactic| (
  wp_for_post
  iframe HΦ
  iexists _, fr ++ [(w, bs)], s'
  simp only [named, chainBytes_append, chainBytes_cons, chainBytes_nil, List.append_nil,
    List.length_append, List.length_singleton]
  iframe
  ipureintro; exact Hc.snoc Hf))

set_option hygiene false in
/-- The loop continues past the frame `(w, bs)` without withdrawing its deposit (a heartbeat, a
message dropped while paused): the tokens moved past it. -/
local macro "dl_skip" : tactic => `(tactic| (
  ihave Hrd := streamRd_skip γw fr.length $$ Hrd
  dl_next))

set_option hygiene false in
/-- A dropped message's logs (`select`'s `default`: the receive channel full), its failure counted. -/
local macro "dl_dropped" : tactic => `(tactic| (
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  repeat' (first
    | (wp_apply hGetType.1 ml _ _ _ st $$ [Hm] as Hm; iframe)
    | (wp_apply hGetFrom.1 ml _ _ _ st $$ [Hm] as Hm; iframe)
    | (wp_apply hGetTo.1 ml _ _ _ st $$ [Hm] as Hm; iframe)
    | (ihave #HT := hTypeString st.msg.Type'
       iunfold fmt.stringMethodSpec at HT
       wp_apply HT as %_)
    | (wp_apply hIDString as %ids %Hids)
    | (wp_apply hIDStringPtr _ DFrac.discard _ $$ [] as %_ -; iframe #)
    | (wp_apply hIsActive ps $$ [] as %_ -; iframe #)
    | (wp_apply hZString as %_ -)
    | (wp_apply hZBool as %_ -)
    | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
       iintro %_ ⟨-, -⟩)
    | (wp_apply hWarn lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | (wp_if_destruct; (try (exfalso; exact Hlgnn rfl)))
    | wp_auto)))

set_option hygiene false in
/-- A dropped message's failure counted (`recvFailures`); the loop continues. -/
local macro "dl_count_fail" : tactic => `(tactic| (
  wp_apply wp_slice_literal (V := GoString) [ids]
  isplitr
  · ipureintro; rfl
  iintro %lsl2 ⟨Hlsl2, -⟩
  (try wp_auto)
  wp_apply hWLV vRF _ [go!"From"] [ids] _ $$ [Hlsl2] as %c2 ⟨%ci2, %Hci2, #Hcnt2, -⟩
  · iframe; iframe #
    ipureintro
    refine ⟨HRFl, by simp, fun v hv => ?_⟩
    simp only [List.mem_singleton] at hv
    subst hv; exact utf8Valid_of_ascii _ Hids
  subst Hci2
  iunfold prometheus.counterSpec at Hcnt2
  icases Hcnt2 with ⟨#HInc, -⟩
  wp_apply HInc
  dl_next))

set_option hygiene false in
/-- The non-blocking send of the message (with its bundle, `netRecv`) on the channel `C` (a bag
`Hb` of names `G`): sent, or dropped (logged, a failure counted); the loop continues. -/
local macro "dl_send" C:term "," G:term : tactic => `(tactic| (
  haveI : go.NotInterface go.uint64 := ⟨by unfold go.uint64; trivial⟩
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.nonblockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, $C, $G, ml
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply is_bag_is_chan $$ Hbag
      unfold nonblockingSendAu
      isplit
      · ihave Hpay : netRecv Rh.γn lid γd ml $$ [Hm HO]
        · iunfold netRecv
          iexists st0, st
          iframe Hm HO HP
          isplitr
          · ipureintro
            have hw : wireOf st0 = wireOf st := Hst0.1.trans Hw.symm
            simp only [wireOf, MsgWire.mk.injEq] at hw
            exact ⟨⟨hw.1.symm, hw.2.1.symm, hw.2.2.1.symm, hw.2.2.2.symm⟩, Hst0.2.1, Hres⟩
          iunfold netSnapRecv
          iintro %hs
          exact absurd hs Hst0.2.2.1
        iapply bag_nonblocking_send_au $$ Ho2 Hbag Hpay
        inext
        (try wp_auto)
        dl_next
      · itrivial
    · iapply BigAndL.bigAndL_nil.2; itrivial
  · dl_dropped
    all_goals dl_count_fail))

set_option hygiene false in
/-- After the decoder is made (`HdecO`, the stream of type `T`): the stopped check, `closer`
set, the loop. -/
local macro "dl_rest" T:term : tactic => `(tactic| (
  ihave #Hctx2 := Hctx
  iunfold context.isContext at Hctx2
  iunfold context.isContextDef at Hctx2
  iNamed Hctx2
  wp_apply HDone as %dch %γdn #Hdone
  wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)] _ $$ [] [-] []
  rotate_left
  · iNamedAccu
  · -- default: the body handed to `closer`
    iintro HP -
    iNamed HP
    iunfold srLockInv at Hinv
    icases Hinv with ⟨%p0, %c0, Hp0, Hc0, -⟩
    wp_auto
    wp_apply +noauto sync.Mutex.wp_Unlock $$ [Hlocked Hp0 Hc0]
    · iframe Hmu Hlocked
      inext
      iunfold srLockInv
      iexists _, _
      iframe
      iright; iexact Hcl
    wp_auto_lc 3
    ihave HI : (∃ (decv : GoInterface) (fr : List (MsgWire × List w8)) (s : (StreamTy.codec $T pid lid).S),
        "dec" ∷ dec_ptr ↦ decv ∗ "HdecO" ∷ decOwn lid pid $T decv rc s ∗
        "Hrr" ∷ http.respReader (raftHttpNet Rh) rc R γk (W64 200) (chainBytes fr) ∗
        "%Hc" ∷ ⌜Chain (StreamTy.codec $T pid lid) (StreamTy.codec $T pid lid).init fr s⌝ ∗
        "Hrd" ∷ streamRd γw fr.length ∗ "cr" ∷ cr_ptr ↦ cr ∗
        "Hlc1" ∷ £ 1 ∗ "Hlc2" ∷ £ 1 ∗ "Hlc3" ∷ £ 1) $$ [dec HdecO Hrr Hrd cr Hlc1 Hlc2 Hlc3]
    · iexists _, [], _
      simp only [named, chainBytes_nil, List.length_nil]
      iframe
      ipureintro; exact Chain.nil _
    wp_for HI
    irename Hlc1 => Ho1
    irename Hlc2 => Ho2
    irename Hlc3 => Ho3
    (try simp only [_root_.decide_true, ↓reduceIte])
    (try wp_auto)
    ihave ⟨HdecO, %Hei⟩ := decOwn_ok _ _ _ _ _ _ $$ HdecO
    obtain ⟨ei, rfl⟩ := Hei
    (try wp_auto)
    ihave #Hrf := respReader_readFullAt (raftHttpNet Rh) (hReadFull _) rc R γk (W64 200)
    wp_apply +noauto (wp_stream_decode hMsgDec hV2Dec Rh.γn.N γw $T lid pid _ ei rfl rc _ _ fr s Hc)
        $$ [HdecO Hrr] as %ml %err ⟨#Herr, %rs', %s', Hrr, HdecO, Hok⟩
    · iframe; iframe #
      iintro !> %bs HB
      iapply stream_known Rh R γk γw $T lid pid bs Hown $$ Hreg HB
    wp_auto_lc 3
    cases err with
    | ok e =>
      -- the decode failed: the body closed, the error returned
      wp_auto
      wp_apply sync.Mutex.wp_Lock _ (srLockInv cr) $$ [] as ⟨Hlocked, Hinv⟩
      · iexact Hmu
      iunfold srLockInv at Hinv
      icases Hinv with ⟨%p0, %c0, Hp0, Hc0, Hcor⟩
      (try wp_auto)
      wp_apply hClose Rh lid pid γd cr c0 $$ [Hc0 Hcor] as Hc0
      · iframe; iframe #
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hp0 Hc0]
      · iframe Hmu Hlocked
        inext
        iunfold srLockInv
        iexists _, _
        iframe
        ileft; ipureintro; rfl
      wp_for_post
      iapply HΦ
      iexact Herr
    | nil =>
      ihave ⟨%w, %bs, %st, %Hfr, #HB, Hm⟩ := Hok $$ %rfl
      obtain ⟨Hf, rfl, Hw, Hres⟩ := Hfr
      ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Hpkg
      icases Hri with ⟨-, -, -, -, -, -, -, ⟨%vRB, #HRB, %HRBl⟩, ⟨%vRF, #HRF, %HRFl⟩, -⟩
      wp_auto
      -- `receivedBytes.WithLabelValues(types.ID(m.GetFrom()).String()).Add(float64(proto.Size(m)))`
      wp_apply hSize ml _ _ _ st $$ [Hm] as %n ⟨Hm, %Hn⟩
      · iframe
      wp_apply hGetFrom.1 ml _ _ _ st $$ [Hm] as Hm
      · iframe
      haveI : go.NotInterface go.uint64 := ⟨by unfold go.uint64; trivial⟩
      (try wp_auto)
      wp_apply hIDString as %fs1 %Hfs1
      wp_apply wp_slice_literal (V := GoString) [fs1]
      isplitr
      · ipureintro; rfl
      iintro %lsl ⟨Hlsl, -⟩
      (try wp_auto)
      wp_apply hWLV vRB _ [go!"From"] [fs1] _ $$ [Hlsl] as %c ⟨%ci, %Hci, #Hcnt, -⟩
      · iframe; iframe #
        ipureintro
        refine ⟨HRBl, by simp, fun v hv => ?_⟩
        simp only [List.mem_singleton] at hv
        subst hv; exact utf8Valid_of_ascii _ Hfs1
      subst Hci
      iunfold prometheus.counterSpec at Hcnt
      icases Hcnt with ⟨-, #HAdd⟩
      ihave #HA := HAdd $$ %n %Hn
      wp_apply HA
      -- `paused`
      wp_apply sync.Mutex.wp_Lock _ (srLockInv cr) $$ [] as ⟨Hlocked, Hinv⟩
      · iexact Hmu
      iunfold srLockInv at Hinv
      icases Hinv with ⟨%p0, %c0, Hp0, Hc0, Hcor⟩
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hp0 Hc0 Hcor]
      · iframe Hmu Hlocked
        inext
        iunfold srLockInv
        iexists _, _
        iframe
      wp_if_destruct
      rotate_left
      · -- paused: the message dropped
        dl_skip
      wp_apply hIsHB ml _ _ _ st $$ [Hm] as Hm
      · iframe
      wp_if_destruct
      · -- a link heartbeat: dropped
        dl_skip
      -- the frame's facts: a message to `lid` with its deposit
      ihave #Hss := stream_known Rh R γk γw $T lid pid _ Hown $$ Hreg HB
      ihave #Hdep := streamSent_frame _ Rh.γn.N γw lid fr s s' w bs Hc Hf $$ Hss
      iunfold frameDep at Hdep
      icases Hdep with (%Hhb | ⟨%st0, %Hst0, #HP, #Hdeposit⟩)
      · exfalso
        apply Hif
        rw [← Hw] at Hhb
        exact Hhb
      imod stream_withdraw Rh.γn.N γw fr.length st0 ⊤ (by simp) $$ Hdeposit Hrd Ho1 with ⟨HO, Hrd⟩
      (try wp_auto)
      wp_apply hGetType.1 ml _ _ _ st $$ [Hm] as Hm
      · iframe
      wp_if_destruct
      · (try wp_auto)
        ihave #Hbag := Hpbag
        dl_send pcv, γp
      · (try wp_auto)
        ihave #Hbag := Hrbag
        dl_send rcv, γr
  · -- the reader stopped: the body closed, `io.EOF` or the close's error returned
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
      · iframe Hmu Hlocked
        inext
        iexact Hinv
      cases rc with
      | nil => exact absurd rfl Hrcnn
      | ok ri =>
        (try wp_auto)
        wp_apply hCloseAny (GoInterface.ok ri) ri rfl $$ [] as %cerr #Hcerr
        · iexact Hcl
        cases cerr with
        | ok ce =>
          wp_auto
          iapply HΦ
          iexact Hcerr
        | nil =>
          ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
          · iPkgInit
          ihave #Heof := io.eof_of_init $$ Hio
          iunfold errors.newVar at Heof
          icases Heof with ⟨%xe, #He, #HeM⟩
          wp_auto
          iapply HΦ
          iapply errorString_errStrOk $$ HeM
    · simp only [named]
      iframe))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem rafthttp.streamReader.decodeLoop.wp_proof
    (hClose : rafthttp.streamReader.close.spec (GF := GF) (hG := hG))
    (hNewDec : rafthttp.newMsgAppV2Decoder.spec (GF := GF) (hG := hG))
    (hMsgDec : rafthttp.messageDecoder.decode.spec (GF := GF) (hG := hG))
    (hV2Dec : rafthttp.msgAppV2Decoder.decode.spec (GF := GF) (hG := hG))
    (hReadFull : ∀ H : http.HttpNet GF, http.ReadFull_resp_spec H)
    (hCloseAny : http.RespCloseAny_spec (GF := GF))
    (hIsActive : rafthttp.peerStatus.isActive.spec (GF := GF) (hG := hG))
    (hIsHB : rafthttp.isLinkHeartbeatMessage.spec (GF := GF) (hG := hG))
    (hTypeString : raftpb.MessageType.String.spec (GF := GF) (hG := hG))
    (hSize : proto.SizeMessage.spec (GF := GF) (hG := hG))
    (hGetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (hGetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (hGetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (hIDString : types.ID.String.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hWLV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZBool : zap.Bool.spec (GF := GF) (hG := hG)) :
    rafthttp.streamReader.decodeLoop.spec (GF := GF) (hG := hG) := by
  intro Rh lid pid γd cr ty rc R γk γw Hown
  wp_start as ⟨#Hf, Hrr, #Hcl, %Hrcnn, #Hreg, Hrd⟩
  ihave #Hf' := Hf
  iunfold srFixed at Hf'
  icases Hf' with ⟨%lg, %tr, %ps, %rcv, %pcv, %γr, %γp, %ctx, %cd, #Hlg, %Hlgnn, #Hpid, #Htr,
    #Hlid, #Hps, #Hpsok, #Hrcv, #Hrbag, #Hpcv, #Hpbag, #Hmu, #Hctxf, #Hctx⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ (srLockInv cr) $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  (try wp_auto)
  cases ty with
  | msgAppV2 =>
    simp only [StreamTy.str, _root_.decide_true]
    (try wp_auto)
    wp_apply hNewDec _ lid pid as %d Hd
    (try wp_auto)
    ihave HdecO : decOwn lid pid .msgAppV2
        (interface.mkOk (go.GoType.PointerType rafthttp.msgAppV2Decoder.ty) #d) rc
        (StreamTy.msgAppV2.codec pid lid).init $$ [Hd]
    · simp only [decOwn]
      iexists d
      iframe
      ipureintro; rfl
    dl_rest StreamTy.msgAppV2
  | message =>
    simp only [StreamTy.str]
    (try wp_auto)
    wp_alloc d as Hd
    iStructNamedSuffix Hd "_d"
    ipersist r_d
    iclear __d
    (try wp_auto)
    ihave HdecO : decOwn lid pid .message
        (interface.mkOk (go.GoType.PointerType rafthttp.messageDecoder.ty) #d) rc
        (StreamTy.message.codec pid lid).init $$ []
    · simp only [decOwn]
      iexists d
      iframe #
      ipureintro; rfl
    dl_rest StreamTy.message

end proof

end EtcdGrove
end Perennial
