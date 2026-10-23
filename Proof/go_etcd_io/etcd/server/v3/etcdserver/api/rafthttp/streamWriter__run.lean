/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/streamWriter__run.lean`.
Lean-first; the writer's steps: `rafthttp/WriterRun.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamWriter__run
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamWriter__close
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamWriter__closeUnlocked
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newMsgAppV2Encoder
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamType__String_ptr
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peerStatus__activate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peerStatus__deactivate
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.WriterRun
public import Spec.google_golang_org.protobuf.proto.SizePb
public import Spec.google_golang_org.protobuf.proto.ClonePb
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Spec.time.NewTicker
public import Spec.time.Ticker__Stop

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
/-- A log call (`if cw.lg != nil { cw.lg.Warn(...) }` and the like): its fields' strings, the
call. -/
local macro "zap_log" : tactic => `(tactic| (
  repeat' (first
    | (wp_apply hTString _ _ _ $$ [t] as %_ t; iframe)
    | (wp_apply hIDStringPtr _ DFrac.discard _ $$ [] as %_ -; iframe #)
    | (wp_apply hZString as %_ -)
    | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
       iintro %_ ⟨-, -⟩)
    | (wp_apply hWarn lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | (wp_apply hInfo lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | wp_auto)))

set_option hygiene false in
/-- `if cw.lg != nil { log }`. -/
local macro "lg_log" : tactic => `(tactic| (
  wp_if_destruct
  · exact absurd rfl Hlgnn
  zap_log
  (try wp_auto)))

set_option hygiene false in
/-- `if cw.lg != nil { log }`, then two later credits from what follows (the loop's next round). -/
local macro "lg_log_lc" : tactic => `(tactic| (
  wp_if_destruct
  · exact absurd rfl Hlgnn
  zap_log
  wp_auto_lc 2))

set_option hygiene false in
/-- The invariant again, not working (the connection closed): the loop continues. -/
local macro "post_idle" : tactic => `(tactic| (
  wp_for_post
  iframe HΦ
  iexists _, _, _, _, _, _, _, _, false, _
  simp only [named]
  iframe heartbeatc msgc t enc flusher batched unflushed cw tickc defer HR Hdone Hlc1 Hlc2 Hrun
  isplitr
  · ipureintro
    have h := Hbat
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try intro _) <;> first | word | (exfalso; simp_all; done)
  ileft
  ipureintro; refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl))

set_option hygiene false in
/-- The stop case after `cw.close()`: the logs, `close(cw.done)`, the return (the deferred
`tickc.Stop()`). -/
local macro "run_stop" : tactic => `(tactic| (
  subst Hb
  (try wp_auto)
  (try lg_log)
  (try lg_log)
  iunfold swDoneRight at Hdone
  icases Hdone with ⟨%dc', %γd', #Hdc', Hdb⟩
  icombine Hdc Hdc' gives %Hdceq
  subst Hdceq
  (wp_apply (wp_broadcast_chan_close _ γd' iprop(True)) $$ [Hdb] as -; (iframe; imodintro; itrivial))
  wp_for_post
  (wp_apply hTickStop tk; iexact Htk)
  iapply HΦ
  itrivial))

set_option hygiene false in
/-- `sentFailures.WithLabelValues(cw.peerID.String()).Inc()`. -/
local macro "count_failure" : tactic => `(tactic| (
  wp_apply hIDStringPtr _ DFrac.discard pid $$ [] as %ps2 ⟨-, %Hps2⟩
  · iframe #
  wp_apply wp_slice_literal (V := GoString) [ps2]
  isplitr
  · ipureintro; rfl
  iintro %lsl2 ⟨Hlsl2, -⟩
  (try wp_auto)
  wp_apply hWLV vSF _ [go!"To"] [ps2] _ $$ [Hlsl2] as %c2 ⟨%ci2, %Hci2, #Hcnt2, -⟩
  · iframe; iframe #
    ipureintro
    refine ⟨HSFl, by simp, fun v hv => ?_⟩
    simp only [List.mem_singleton] at hv
    subst hv; exact utf8Valid_of_ascii _ (Hps2 ▸ types.idStr_ascii _)
  subst Hci2
  iunfold prometheus.counterSpec at Hcnt2
  icases Hcnt2 with ⟨#HInc, -⟩
  wp_apply HInc
  (try wp_auto)))

set_option hygiene false in
/-- The invariant again, working (with `Hlive'`, the live connection): the loop continues. -/
local macro "post_working" : tactic => `(tactic| (
  wp_for_post
  iframe HΦ
  iexists _, _, _, _, _, _, _, _, true, _
  simp only [named]
  iframe heartbeatc msgc t enc flusher batched unflushed cw tickc defer HR Hdone Hlc1 Hlc2 Hrun
  isplitr
  · ipureintro
    have h := Hbat
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try intro _) <;> word
  iright
  iframe Hlive'
  ipureintro; refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl))

set_option hygiene false in
/-- The live connection after a frame of `st` (`Hf`, `Hfs'`, `Hc'`): `Hlive'`. -/
local macro "msg_live" : tactic => `(tactic| (
  ihave Hlive' : swLive Rh ty lid pid fs (GoInterface.ok ei) (GoInterface.ok wi) cl $$ [HencO HWr Hclr]
  · iunfold swLive
    iexists wi, a, R, γk, γw, fr ++ [(wireOf st, bs)], s'
    rw [chainBytes_append]
    simp only [chainBytes_cons, chainBytes_nil, List.append_nil]
    iframe HencO HWr Hclr Hfs' Hreg
    ipureintro
    exact ⟨Hc', HR3⟩))

set_option hygiene false in
/-- A batch's end: flushed, its bytes counted, the counters reset. -/
local macro "msg_flush" : tactic => `(tactic| (
  (wp_apply hFlush (raftHttpNet Rh) _ wi a R γk _ _ rfl $$ [HWr] as HWr; iexact HWr)
  (try wp_auto)
  wp_apply hIDStringPtr _ DFrac.discard pid $$ [] as %ps1 ⟨-, %Hps1⟩
  · iframe #
  wp_apply wp_slice_literal (V := GoString) [ps1]
  isplitr
  · ipureintro; rfl
  iintro %lsl ⟨Hlsl, -⟩
  (try wp_auto)
  wp_apply hWLV vSB _ [go!"To"] [ps1] _ $$ [Hlsl] as %c ⟨%ci, %Hci, #Hcnt, -⟩
  · iframe; iframe #
    ipureintro
    refine ⟨HSBl, by simp, fun v hv => ?_⟩
    simp only [List.mem_singleton] at hv
    subst hv; exact utf8Valid_of_ascii _ (Hps1 ▸ types.idStr_ascii _)
  subst Hci
  iunfold prometheus.counterSpec at Hcnt
  icases Hcnt with ⟨-, #HAdd⟩
  have Hun0 : 0 ≤ sint.Z (unf + n) := by have := Hbat; word
  ihave #HA := HAdd $$ %(unf + n) %Hun0
  msg_live
  wp_apply HA
  post_working))

set_option hygiene false in
/-- The message case (working): the message's one-shot part deposited as the connection's next
frame's, the message encoded; then flushed (the channel empty, or a batch's end) or batched; or on
an error the connection closed and the peer reported unreachable. -/
local macro "run_msg" : tactic => `(tactic| (
  (try wp_auto)
  ihave Hrun : swRunOwn Rh ty lid pid cw _ true cl $$ [Hmc Hwkp Hclp]
  · iunfold swRunOwn
    iexists γm
    iframe; iframe #
  iunfold swMsg at Hm
  icases Hm with ⟨%st, #Hm, #HP, HO, %Hst⟩
  iunfold swLive at Hlive
  icases Hlive with ⟨%wi, %a, %R, %γk, %γw, %fr, %s, %Hfl, HencO, Hrw, %Hc, #Hfs, #Hreg, %HR3, Hclr⟩
  ihave ⟨HencO, %Hei⟩ := encOwn_ok _ _ _ _ _ _ _ $$ HencO
  obtain ⟨ei, rfl⟩ := Hei
  imod (stream_deposit Rh.γn.N γw fr.length st ⊤) $$ HO with #Hdeposit
  ihave #Hdep : frameDep Rh.γn.N γw pid fr.length (wireOf st) $$ []
  · iunfold frameDep
    iright
    iexists st
    iframe #
    ipureintro
    exact ⟨rfl, Hst.2.1, Hst.2.2.1, Hst.2.2.2.1⟩
  ihave #Hperm := stream_perm Rh ty lid pid a R γk γw fr s st Hc HR3.1 $$ Hreg Hfs Hdep
  ihave #Hwr := respWriter_writerAt (raftHttpNet Rh) (hWrite _) wi a R γk
  (try wp_auto)
  wp_apply (wp_stream_encode hMsgEnc hV2Enc ty lid pid fs _ ei rfl wi s _ _ (chainBytes fr) ml st
      ⟨Hst.1, Hst.2.2.2.2.1⟩) $$ [HencO Hrw]
    as %err ⟨#Herr, %h', %s', HWr, HencO, %Hok⟩
  · iframe; iframe #
  subst Hfl
  cases err with
  | nil =>
    obtain ⟨bs, Hf, rfl⟩ := Hok rfl
    ihave #Hfs' : ([∗list] i ↦ f ∈ fr ++ [(wireOf st, bs)], frameDep Rh.γn.N γw pid i f.1) $$ []
    · iapply (BigSepL.bigSepL_snoc (Φ := fun i (f : MsgWire × List w8) => frameDep Rh.γn.N γw pid i f.1)).2
      iframe #
    have Hc' := Hc.snoc Hf
    wp_auto
    have wpS := hSize pbMessage ml st
    simp only [pbMessage_ty, pbMessage_ro] at wpS
    wp_apply wpS $$ [] as %n ⟨%Hn, -⟩
    · iexact Hm
    (try wp_auto)
    wp_func_call
    wp_call
    (try wp_auto)
    wp_apply +noauto wp_Len mcl γm $$ [] as %ln %Hln
    · iapply is_bag_is_chan $$ Hbag
    have Hnb : sint.Z n < 2 ^ 50 := by have := Hst.2.2.2.2.2; unfold swMsgBound at this; omega
    have Hn0 : 0 ≤ sint.Z n := by omega
    wp_auto_lc 2
    wp_if_destruct
    · (try wp_auto)
      msg_flush
    · (try wp_auto)
      wp_if_destruct
      · msg_flush
      · msg_live
        (try wp_auto)
        post_working
  | ok e2 =>
    wp_auto
    iunfold http.errStrOk at Herr
    icases Herr with (%Hn | ⟨%e3, %He3, #HE, -⟩)
    · cases Hn
    cases He3
    wp_apply hTString _ _ _ $$ [t] as %ts t
    · iframe
    (try wp_auto)
    wp_apply HE as %es
    (try wp_auto)
    wp_apply hDeactivate ps _ es $$ []
    · iframe #
    (try wp_auto)
    wp_apply +noauto hClose Rh ty lid pid Rr cw _ true cl (connBack Rh wi a R γk) $$ [Hrun HR Hclr HWr]
      as %b ⟨%Hb, HR, %mc', Hrun⟩
    · iframe #
      simp only [↓reduceIte]
      iframe
      iunfold connBack
      iexists _, _
      iexact HWr
    wp_auto_lc 2
    lg_log
    wp_apply hGetTo.1 ml DFrac.discard DFrac.discard false st $$ [] as -
    · iexact Hm
    (try wp_auto)
    subst Hri
    (try wp_auto)
    wp_apply HRU $$ [HR] as HR
    · iexact HR
    (try wp_auto)
    count_failure
    post_idle))

set_option hygiene false in
/-- The heartbeat case (working): the link heartbeat encoded as the connection's next frame (no
deposit: the reader drops it); flushed, or on an error the connection closed. -/
local macro "run_hb" : tactic => `(tactic| (
  (try wp_auto)
  have wpC := hClone pbMessage (globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.linkHeartbeatMessage)
    go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.hbSt
  simp only [pbMessage_ty, pbMessage_ro, pbMessage_dec, pbMessage_eqv] at wpC
  wp_apply wpC $$ [] as %l' ⟨%m', Hl', %Heqv⟩
  · iexact Hhb
  (try wp_auto)
  ihave Hl'' := msgPtsC_to_msgOwn l' _ _ _ m' $$ Hl'
  imod Hl'' with Hl'
  ihave Hl'' := msgOwn_persist l' _ m' $$ Hl'
  imod Hl'' with Hl'
  iunfold swLive at Hlive
  icases Hlive with ⟨%wi, %a, %R, %γk, %γw, %fr, %s, %Hfl, HencO, Hrw, %Hc, #Hfs, #Hreg, %HR3, Hclr⟩
  ihave ⟨HencO, %Hei⟩ := encOwn_ok _ _ _ _ _ _ _ $$ HencO
  obtain ⟨ei, rfl⟩ := Hei
  (try wp_auto)
  have Hw' : wireOf m' = hbWire := Heqv.1.symm
  have Hhb' : isHB (wireOf m').msg := by rw [Hw']; exact ⟨rfl, rfl, rfl⟩
  have Hmar : MsgMarshals m' := Heqv.2 rfl
  ihave #Hdep : frameDep Rh.γn.N γw pid fr.length (wireOf m') $$ []
  · iunfold frameDep; ileft; ipureintro; exact Hhb'
  ihave #Hperm := stream_perm Rh ty lid pid a R γk γw fr s m' Hc HR3.1 $$ Hreg Hfs Hdep
  ihave #Hwr := respWriter_writerAt (raftHttpNet Rh) (hWrite _) wi a R γk
  wp_apply (wp_stream_encode hMsgEnc hV2Enc ty lid pid fs _ ei rfl wi s _ _ (chainBytes fr) l' m'
      ⟨Hmar, fun _ => ⟨Hmar, Or.inl ⟨Hhb', Hw'⟩⟩⟩) $$ [HencO Hrw Hl']
    as %err ⟨#Herr, %h', %s', HWr, HencO, %Hok⟩
  · iframe; iframe #
  subst Hfl
  cases err with
  | nil =>
    obtain ⟨bs, Hf, rfl⟩ := Hok rfl
    wp_auto
    (wp_apply hFlush (raftHttpNet Rh) _ wi a R γk _ _ rfl $$ [HWr] as HWr; iexact HWr)
    (try wp_auto)
    wp_apply hIDStringPtr _ DFrac.discard pid $$ [] as %ps1 ⟨-, %Hps1⟩
    · iframe #
    wp_apply wp_slice_literal (V := GoString) [ps1]
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    (try wp_auto)
    wp_apply hWLV vSB _ [go!"To"] [ps1] _ $$ [Hlsl] as %c ⟨%ci, %Hci, #Hcnt, -⟩
    · iframe; iframe #
      ipureintro
      refine ⟨HSBl, by simp, fun v hv => ?_⟩
      simp only [List.mem_singleton] at hv
      subst hv; exact utf8Valid_of_ascii _ (Hps1 ▸ types.idStr_ascii _)
    subst Hci
    iunfold prometheus.counterSpec at Hcnt
    icases Hcnt with ⟨-, #HAdd⟩
    have Hn0 : 0 ≤ sint.Z (unf + nHB) := by have := Hbat; have := HnHB; word
    ihave #HA := HAdd $$ %(unf + nHB) %Hn0
    ihave #Hfs' : ([∗list] i ↦ f ∈ fr ++ [(wireOf m', bs)], frameDep Rh.γn.N γw pid i f.1) $$ []
    · iapply (BigSepL.bigSepL_snoc (Φ := fun i (f : MsgWire × List w8) => frameDep Rh.γn.N γw pid i f.1)).2
      iframe #
    have Hc' := Hc.snoc Hf
    ihave Hlive' : swLive Rh ty lid pid fs (GoInterface.ok ei) (GoInterface.ok wi) cl $$ [HencO HWr Hclr]
    · iunfold swLive
      iexists wi, a, R, γk, γw, fr ++ [(wireOf m', bs)], s'
      rw [chainBytes_append]
      simp only [chainBytes_cons, chainBytes_nil, List.append_nil]
      iframe HencO HWr Hclr Hfs' Hreg
      ipureintro
      exact ⟨Hc', HR3⟩
    wp_apply +noauto HA
    wp_auto_lc 2
    post_working
  | ok e2 =>
    wp_auto
    iunfold http.errStrOk at Herr
    icases Herr with (%Hn | ⟨%e3, %He3, #HE, -⟩)
    · cases Hn
    cases He3
    wp_apply hTString _ _ _ $$ [t] as %ts t
    · iframe
    (try wp_auto)
    wp_apply HE as %es
    (try wp_auto)
    wp_apply hDeactivate ps _ es $$ []
    · iframe #
    (try wp_auto)
    count_failure
    wp_apply +noauto hClose Rh ty lid pid Rr cw _ true cl (connBack Rh wi a R γk) $$ [Hrun HR Hclr HWr]
      as %b ⟨%Hb, HR, %mc', Hrun⟩
    · iframe #
      simp only [↓reduceIte]
      iframe
      iunfold connBack
      iexists _, _
      iexact HWr
    wp_auto_lc 2
    lg_log
    post_idle))

set_option hygiene false in
/-- The connection case after the new encoder (`HencO`): the logs, the flusher, `activate`, the
closer, working, `mu` released, the channels; the invariant again, working on the new connection. -/
local macro "run_conn_tail" : tactic => `(tactic| (
  (try lg_log)
  (wp_apply hActivate ps; iframe #)
  (try wp_auto)
  ihave ⟨Hrun, Hinv⟩ := swRunOwn_split _ _ _ _ _ _ _ _ _ $$ [Hmc Hwk Hcl]
  · iframe; iframe #
  (wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hinv]; (iframe; iframe #))
  subst Hb
  (try wp_auto)
  (try lg_log)
  (try lg_log)
  iunfold swRunOwn at Hrun
  icases Hrun with ⟨%γr, Hmc, Hwk, Hcl, #Hbagr2⟩
  wp_auto_lc 2
  wp_for_post
  iframe HΦ
  iexists _, _, _, _, _, _, _, _, true, _
  simp only [named]
  iframe heartbeatc msgc t enc flusher batched unflushed cw tickc defer HR Hdone Hlc1 Hlc2
  isplitl [Hmc Hwk Hcl]
  · iunfold swRunOwn
    iexists γr
    iframe; iframe #
  isplitr
  · ipureintro
    have h := Hbat
    refine ⟨h.1, h.2.1, ?_, ?_, ?_⟩ <;> (try intro _) <;> word
  iright
  isplitr
  · ipureintro; refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl
  iunfold swLive
  iexists wi, a, R, γk, γw, [], _
  iframe HencO Hclr
  simp only [chainBytes_nil]
  iframe Hrw
  iframe #
  isplitr
  · ipureintro; exact Chain.nil _
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  ipureintro; exact HR3))

set_option hygiene false in
/-- The connection case (`conn := <-cw.connc`), the old connection's closing in `HC`: `mu` taken,
the old connection closed (`closeUnlocked`), the new one's encoder, flusher and closer, working,
`mu` released, the channels set. -/
local macro "run_conn" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock _ (swLockInv Rh ty lid pid cw) $$ [] as ⟨Hlocked, Hinv⟩
  · iexact Hmu
  ihave ⟨%γm1, Hmc, Hwk, Hcl, #Hbag1⟩ := swRunOwn_combine _ _ _ _ _ _ _ _ $$ Hrun Hinv
  (try wp_auto)
  (wp_apply hCloseUnlocked Rh ty lid pid Rr cw _ γm1 _ cl _ $$ [Hmc Hwk Hcl HC HR]
     as %b ⟨%Hb, HR, %mc', %γm', Hmc, Hwk, Hcl, #Hbag'⟩; (iframe; iframe #))
  iunfold outConnOk at Hconn
  icases Hconn with ⟨%wi, %clc, %a, %R, %γk, %γw, #Hct, #Hcw, #Hcf, #Hccl, #Hclid, #Hcpid, Hrw,
    #Hreg, %HR3, Hclr⟩
  (try wp_auto)
  cases ty with
  | msgAppV2 =>
    simp only [StreamTy.str, _root_.decide_true]
    (try wp_auto)
    (wp_apply hNewEnc wi fs as %e Henc; (ipureintro; exact Hfsnn))
    (try wp_auto)
    ihave HencO : encOwn lid pid fs .msgAppV2
        (interface.mkOk (go.GoType.PointerType rafthttp.msgAppV2Encoder.ty) #e) wi
        (StreamTy.msgAppV2.codec lid pid).init $$ [Henc]
    · simp only [encOwn]
      iexists e
      iframe
      ipureintro; rfl
    run_conn_tail
  | message =>
    simp only [StreamTy.str]
    (try wp_auto)
    wp_alloc e as He
    iStructNamed He
    ipersist w
    (try wp_auto)
    ihave HencO : encOwn lid pid fs .message
        (interface.mkOk (go.GoType.PointerType rafthttp.messageEncoder.ty) #e) wi
        (StreamTy.message.codec lid pid).init $$ []
    · simp only [encOwn]
      iexists e
      iframe #
      ipureintro; rfl
    run_conn_tail))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem rafthttp.streamWriter.run.wp_proof
    (hClose : rafthttp.streamWriter.close.spec (GF := GF) (hG := hG))
    (hCloseUnlocked : rafthttp.streamWriter.closeUnlocked.spec (GF := GF) (hG := hG))
    (hNewEnc : rafthttp.newMsgAppV2Encoder.spec (GF := GF) (hG := hG))
    (hMsgEnc : rafthttp.messageEncoder.encode.spec (GF := GF) (hG := hG))
    (hV2Enc : rafthttp.msgAppV2Encoder.encode.spec (GF := GF) (hG := hG))
    (hWrite : ∀ H : http.HttpNet GF, http.respWrite_spec H)
    (hFlush : ∀ H : http.HttpNet GF, http.Flush_spec H)
    (hTString : rafthttp.streamType.String_ptr.spec (GF := GF) (hG := hG))
    (hActivate : rafthttp.peerStatus.activate.spec (GF := GF) (hG := hG))
    (hDeactivate : rafthttp.peerStatus.deactivate.spec (GF := GF) (hG := hG))
    (hSize : proto.SizePb.spec (GF := GF) (hG := hG))
    (hClone : proto.ClonePb.spec (GF := GF) (hG := hG))
    (hGetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hWLV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hNewTicker : time.NewTicker.spec (GF := GF) (hG := hG))
    (hTickStop : time.Ticker.Stop.spec (GF := GF) (hG := hG)) :
    rafthttp.streamWriter.run.spec (GF := GF) (hG := hG) := by
  intro Rh ty lid pid Rr cw mc
  wp_start as ⟨#Hf, Hrun, Hdone, HR⟩
  ihave #Hf' := Hf
  iunfold swFixed at Hf'
  icases Hf' with ⟨%lg, %ps, %fs, %r, %γd, %cc, %sc, %dc, %γc, %γs, %γdn, #Hlg, %Hlgnn, #Hlid,
    #Hpid, #Hps, #Hpsok, #Hfs, %Hfsnn, #Hr, #Hraft, #Hmu, #Hcc, #Hcbag, #Hsc, #Hstop, #Hdc,
    #Hdunk⟩
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, #Hhb, -, -, -, -, -, -, -, ⟨%vSB, #HSB, %HSBl⟩, ⟨%vSF, #HSF, %HSFl⟩, -, -,
    #HCRT, ⟨%nHB, #HHBS, %HnHB⟩, -⟩
  iunfold netRaftOk at Hraft
  icases Hraft with ⟨%ri, %Hri, -, -, #HRU, -⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply +noauto hNewTicker _ $$ [] as %tk #Htk
  · ipureintro; decide
  wp_auto_lc 2
  -- the start's log
  wp_if_destruct
  · exact absurd rfl Hlgnn
  wp_apply hIDStringPtr _ DFrac.discard lid $$ [$Hlid] as %ls -
  wp_apply hZString as %f1 -
  wp_apply hIDStringPtr _ DFrac.discard pid $$ [$Hpid] as %ps' -
  wp_apply hZString as %f2 -
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  wp_apply hInfo lg _ _ $$ []
  · iframe #; ipureintro; exact Hlgnn
  (try wp_auto)
  ihave #Htk' := Htk
  iunfold time.isTicker at Htk'
  icases Htk' with ⟨%Htknn, %tch, %γt, #HtC, #Htbag⟩
  -- the loop's invariant: not working, both channels nil; or working on a live connection
  ihave HI : (∃ (hbc mcl : GoChan) (tv : GoString) (encv flv : GoInterface) (bat unf : w64)
      (mcw : GoChan) (wk : Bool) (cl : GoInterface),
      "heartbeatc" ∷ heartbeatc_ptr ↦ hbc ∗ "msgc" ∷ msgc_ptr ↦ mcl ∗ "t" ∷ t_ptr ↦ tv ∗
      "enc" ∷ enc_ptr ↦ encv ∗ "flusher" ∷ flusher_ptr ↦ flv ∗ "batched" ∷ batched_ptr ↦ bat ∗
      "unflushed" ∷ unflushed_ptr ↦ unf ∗ "cw" ∷ cw_ptr ↦ cw ∗ "tickc" ∷ tickc_ptr ↦ tk ∗
      "defer" ∷ defer ↦ _ ∗
      "Hrun" ∷ swRunOwn Rh ty lid pid cw mcw wk cl ∗ "HR" ∷ Rr ∗ "Hdone" ∷ swDoneRight cw ∗
      "Hlc1" ∷ £ 1 ∗ "Hlc2" ∷ £ 1 ∗
      "%Hbat" ∷ ⌜0 ≤ sint.Z bat ∧ sint.Z bat ≤ 2049 ∧ 0 ≤ sint.Z unf ∧ sint.Z unf < 2 ^ 62 ∧
        (wk = true → sint.Z unf ≤ (sint.Z bat + 1) * 2 ^ 50)⌝ ∗ "Hst" ∷ (⌜wk = false ∧ hbc = chan.nil ∧ mcl = chan.nil⌝ ∨
        ⌜wk = true ∧ hbc = tch ∧ mcl = mcw⌝ ∗ swLive Rh ty lid pid fs encv flv cl)) $$
      [heartbeatc msgc t enc flusher batched unflushed cw tickc defer Hrun HR Hdone Hlc1 Hlc2]
  · iexists _, _, _, _, _, _, _, mc, false, GoInterface.nil
    simp only [named]
    iframe
    isplitr
    · ipureintro
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try intro _) <;> first | decide | (simp at *) | word
    ileft
    ipureintro
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl
  wp_for HI
  icases Hst with (⟨%Hwk, %Hhbc, %Hmcl⟩ | ⟨⟨%Hwk, %Hhbc, %Hmcl⟩, Hlive⟩)
  · -- not working: the heartbeat and message cases are on nil channels
    subst Hwk Hhbc Hmcl
    wp_apply_core chan.wp_select_blocking_nil
    iapply BigAndL.bigAndL_cons.2; isplit
    · iright; iapply chan.nilClausePre_recv time.Time _ _ rfl
    iapply BigAndL.bigAndL_cons.2; isplit
    · iright; iapply chan.nilClausePre_recv Loc _ _ rfl
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, cc, γc
      isplitr; · ipureintro; rfl
      isplitr; · iapply is_bag_is_chan $$ Hcbag
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hcbag
      inext
      iintro %conn Hconn
      ihave HC : (if false then iprop(closeRight cl iprop(True) ∗ iprop(True)) else iprop(True)) $$ []
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      run_conn
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γs
      isplitr; · ipureintro; rfl
      isplitr; · iapply ownBroadcastChan_is_chan $$ Hstop
      iapply broadcast_chan_receive $$ Hstop
      iintro -
      (try wp_auto)
      wp_apply hClose Rh ty lid pid Rr cw mcw false cl iprop(True) $$ [$Hrun $HR]
        as %b ⟨%Hb, HR, %mc', Hrun⟩
      · iframe #
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
      run_stop
    iapply BigAndL.bigAndL_nil.2; itrivial
  · -- working
    subst Hwk Hhbc Hmcl
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2; isplit
    · simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, _, γt
      isplitr; · ipureintro; rfl
      isplitr; · iapply is_bag_is_chan $$ Htbag
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htbag
      inext
      iintro %tv' -
      run_hb
    iapply BigAndL.bigAndL_cons.2; isplit
    · simp only [chan.blockingClausePre]
      iunfold swRunOwn at Hrun
      icases Hrun with ⟨%γm, Hmc, Hwkp, Hclp, #Hbag⟩
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, _, γm
      isplitr; · ipureintro; rfl
      isplitr; · iapply is_bag_is_chan $$ Hbag
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
      inext
      iintro %ml Hm
      run_msg
    iapply BigAndL.bigAndL_cons.2; isplit
    · simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, cc, γc
      isplitr; · ipureintro; rfl
      isplitr; · iapply is_bag_is_chan $$ Hcbag
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hcbag
      inext
      iintro %conn Hconn
      icases swLive_closing _ _ _ _ _ _ _ _ $$ Hlive with ⟨%Q, HQ⟩
      ihave HC : (if true then iprop(closeRight cl Q ∗ Q) else iprop(True)) $$ [HQ]
      · simp only [↓reduceIte]; iexact HQ
      run_conn
    iapply BigAndL.bigAndL_cons.2; isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γs
      isplitr; · ipureintro; rfl
      isplitr; · iapply ownBroadcastChan_is_chan $$ Hstop
      iapply broadcast_chan_receive $$ Hstop
      iintro -
      (try wp_auto)
      icases swLive_closing _ _ _ _ _ _ _ _ $$ Hlive with ⟨%Q, HQ⟩
      wp_apply hClose Rh ty lid pid Rr cw _ true cl Q $$ [$Hrun $HR HQ]
        as %b ⟨%Hb, HR, %mc', Hrun⟩
      · iframe #
        simp only [↓reduceIte]
        iexact HQ
      run_stop
    iapply BigAndL.bigAndL_nil.2; itrivial

end proof

end EtcdGrove
end Perennial
