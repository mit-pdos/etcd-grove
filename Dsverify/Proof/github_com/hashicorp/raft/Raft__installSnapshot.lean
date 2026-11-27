/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__installSnapshot.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).installSnapshot` (stage 3, snap's riskiest step): the pending install
through the sink's `Close` (`snapProof.install_commit`), the FSM goroutine's restore (`fsmRestoreP`),
`setLastApplied` (`snapProof.install_applied_au`), the keep/discard step and the compaction.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__installSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastApplied
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastApplied
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastLog
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastLog
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setState
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLastContact
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLatestConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCommittedConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__compactLogs
public import Dsverify.Spec.github_com.hashicorp.raft.DecodeConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__processConfigurationLogEntry
public import Dsverify.Spec.github_com.hashicorp.raft.RPC__Respond
public import Dsverify.Spec.github_com.hashicorp.raft.getSnapshotVersion
public import Dsverify.Spec.github_com.hashicorp.raft.newCountingReader
public import Dsverify.Spec.github_com.hashicorp.raft.countingReader__Read
public import Dsverify.Spec.github_com.hashicorp.raft.startSnapshotRestoreMonitor
public import Dsverify.Spec.github_com.hashicorp.raft.snapshotRestoreMonitor__StopAndWait
public import Dsverify.Proof.github_com.hashicorp.raft.InstallBase
public import Dsverify.Proof.github_com.hashicorp.raft.SnapFut
public import Spec.io.Copy

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem github_com.hashicorp.raft.Raft.installSnapshot.wp_proof
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_getLastApplied : github_com.hashicorp.raft.raftState.getLastApplied.spec (GF := GF) (hG := hG))
    (wp_setLastApplied : github_com.hashicorp.raft.raftState.setLastApplied.spec (GF := GF) (hG := hG))
    (wp_setLastSnapshot : github_com.hashicorp.raft.raftState.setLastSnapshot.spec (GF := GF) (hG := hG))
    (wp_getLastLog : github_com.hashicorp.raft.raftState.getLastLog.spec (GF := GF) (hG := hG))
    (wp_setLastLog : github_com.hashicorp.raft.raftState.setLastLog.spec (GF := GF) (hG := hG))
    (wp_setState : github_com.hashicorp.raft.Raft.setState.spec (GF := GF) (hG := hG))
    (wp_setCurrentTerm : github_com.hashicorp.raft.Raft.setCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_setLeader : github_com.hashicorp.raft.Raft.setLeader.spec (GF := GF) (hG := hG))
    (wp_setLastContact : github_com.hashicorp.raft.Raft.setLastContact.spec (GF := GF) (hG := hG))
    (wp_setLatestConfiguration :
      github_com.hashicorp.raft.Raft.setLatestConfiguration.spec (GF := GF) (hG := hG))
    (wp_setCommittedConfiguration :
      github_com.hashicorp.raft.Raft.setCommittedConfiguration.spec (GF := GF) (hG := hG))
    (wp_compactLogs : github_com.hashicorp.raft.Raft.compactLogs.spec (GF := GF) (hG := hG))
    (wp_DecodeConfiguration : github_com.hashicorp.raft.DecodeConfiguration.spec (GF := GF) (hG := hG))
    (wp_processConfigurationLogEntry :
      github_com.hashicorp.raft.Raft.processConfigurationLogEntry.spec (GF := GF) (hG := hG))
    (wp_Respond : github_com.hashicorp.raft.RPC.Respond.spec (GF := GF) (hG := hG))
    (wp_getSnapshotVersion : github_com.hashicorp.raft.getSnapshotVersion.spec (GF := GF) (hG := hG))
    (wp_newCountingReader : github_com.hashicorp.raft.newCountingReader.spec (GF := GF) (hG := hG))
    (wp_cr_Read : github_com.hashicorp.raft.countingReader.Read.spec (GF := GF) (hG := hG))
    (wp_startMonitor :
      github_com.hashicorp.raft.startSnapshotRestoreMonitor.spec (GF := GF) (hG := hG))
    (wp_StopAndWait :
      github_com.hashicorp.raft.snapshotRestoreMonitor.StopAndWait.spec (GF := GF) (hG := hG))
    (wp_Error : github_com.hashicorp.raft.deferError.Error.spec (GF := GF) (hG := hG))
    (wp_Copy : io.Copy.spec (GF := GF) (hG := hG))
    (wp_Copy_Discard : io.Copy_Discard.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.installSnapshot.spec (GF := GF) (hG := hG) :=
  fun r γ rc i rpc req s st tid => by
  wp_start as ⟨#Hr, Hm, HrpcP, %Hcmd, Htok⟩
  unfold mainOwnAt
  icases Hm with ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %c, Hs, Hdv, HS, %Hvm, Hll, Hst,
    Hstl, Hlp, Hvreg, Happ, %Ha, Hprod, Hpnd, Hcomp, %Hca, Hcfgs, #Hcfg, #Hccfg, %Hcf, #Hcmt, #Hlch,
    #Hlchan, Hlown, %Hcap⟩
  unfold isRpcP
  icases HrpcP with ⟨%p, %rq, %snd, %T, %x, %stx, %b, %rd, %γc, %Hrv, Hp, Hreq, Hstream, #Hbag⟩
  obtain ⟨Hrv1, Hrv2⟩ := Hrv
  have Hpr : p = req := by
    rw [Hrv1, interface_mkOk_inj] at Hcmd
    exact go.IntoValInj.intoVal_inj (V := Loc) Hcmd.2
  subst Hpr
  unfold isReq
  icases Hreq with ⟨%Hnums, Hhdr, #Hlead, -, ⟨%ss, #HcfgB, #Hscfg⟩, #HlT, #Hae⟩
  unfold hdrOk
  icases Hhdr with ⟨%Hpv3, #Hid, #Haddr⟩
  obtain ⟨HTe, Hxe, Hste, Hver, Hsize, Hsnd, Hx1⟩ := Hnums
  unfold snapStream
  icases Hstream with ⟨%R, %eof, #HRd, HR, #Heof, %HnWT, HsP, %Hb63⟩
  ihave ⟨%fx, -, #HisFSM, -⟩ := isRaft_fsm r γ rc i $$ Hr
  ihave #HsP := isFSM_snapP_persistent _ γ i _ _ _ x b $$ [$HisFSM $HsP]
  ihave ⟨#HI, #Hvi⟩ := isRaft_proto r γ rc i $$ Hr
  ihave #Htc := isRaft_termCell r γ rc i $$ Hr
  ihave #HstC := isRaft_stateCell r γ rc i $$ Hr
  imod snapProof.stateCell_val r rc st $$ [$HstC $Hst] with ⟨Hst, %Hstv⟩
  ipersist Hp
  iStructNamed Hp
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply wp_getCurrentTerm.1 r γ i s $$ [$HI $Htc $Hs] as Hs
  irename «$r0» => Hrsp
  generalize «$r0_ptr» = rsp at *
  imod snapProof.termLb_of_srv γ r i s $$ [$HI $Htc $Hs] with ⟨Hs, #Htlb0⟩
  imod srvOwn_facts γ ⊤ (by simp) i s $$ [$HI $Hs] with ⟨Hs, -, %Hsf⟩
  have Hst62 : s.term < 2 ^ 62 := Hsf.2.2.2.2.2.1
  ipersist r
  ipersist req
  ipersist resp
  -- the version check: version 1
  rw [Hver]
  wp_auto
  ihave #Heof0 := snapProof.eof_ne_nil eof $$ [$Heof]
  · iPkgInit
  icases Heof0 with %Heofnn
  ihave #HRs := snapProof.streamReader_of_ok rd R eof Heofnn $$ HRd
  ihave ⟨%dw, #Hdw⟩ : (∃ w : GoInterface, globalAddr io.Discard ↦□ w) $$ []
  · ihave Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
    · iPkgInit
    ihave Hi := io.isInit_access $$ Hio
    icases Hi with ⟨⟨%w, #Hw⟩, -⟩
    iexists w; iexact Hw
  -- an older term
  wp_apply wp_getCurrentTerm.1 r γ i s $$ [$HI $Htc $Hs] as Hs
  wp_if_destruct
  · rw [Hrv2]
    wp_apply wp_Copy_Discard dw rd.ty rd.v R b eof HnWT Hb63 $$ [$Hdw $Heof $HR $HRs] as %n0 %e0 ⟨%k0, %Hk0, HR⟩
    wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [rpc Hrsp] as rpc
    · iframe rpc Hbag
      unfold rpcRespAnyP
      iright
      iexists rsp
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iexists _
      iframe Hrsp
      iapply snapProof.isResp_intro γ _ rfl
      iapply termOk_of_termLb γ i _ s.term (by word) $$ [$Hvi $Htlb0]
    iapply HΦ
    iexists s, st
    iframe Htok
    isplitl
    · iexists a, sst, cfg, ccfg, cidx, li, lch, γl, bs, c
      iframe # ∗
      ipureintro; exact ⟨Hvm, Ha, Hca, Hcf, Hcap⟩
    ileft; ipureintro; right; exact ⟨rfl, rfl, rfl⟩
  -- a newer term: become a follower in it
  have HT : s.term ≤ T := by
    rw [← HTe]; have : uint.Z (W64 (s.term : Int)) = s.term := by word
    simp only [uint.nat]; word
  ihave #HcmtT := cmtIdx_mono γ s.term T s.log s.log _ HT rfl $$ Hcmt
  ihave %Hnl : ⌜T = s.term → st ≠ stLeader⌝ $$ [Hstl]
  · by_cases hT : T = s.term
    · icases Hstl with (%Hnl | ⟨#Hli, -⟩)
      · ipureintro; intro _; exact Hnl
      · rw [← hT]
        ihave %Heq := leaderIs_agree γ T snd i $$ [$HlT $Hli]
        exact absurd Heq Hsnd
    · ipureintro; intro h; exact absurd h hT
  ihave #HokT := termOk_of_aeValid γ T x stx [] x $$ Hae
  wp_join iprop(∃ (st1 : w32) (sst1 : StableAbs) (rv : InstallSnapshotResponse),
      srvOwn γ i { s with term := T } ∗ ghostVar rc.names.state (1 : Qp).half st1 ∗
      ⌜(st1 = stFollower ∨ (st1 = st ∧ T = s.term)) ∧ st1 ≠ stLeader⌝ ∗
      rc.ownS sst1 ∗ ⌜voteMatches sst1 { s with term := T }⌝ ∗ rsp ↦ rv ∗
      ⌜rv.RPCHeader' = zeroValDef ∧ rv.Success' = false⌝ ∗ termOk γ (uint.nat rv.Term') ∗
      termLb γ i T ∗ rtok tid) at next with [Hs Hst HS Hrsp Htok]
    as ⟨%st1, %sst1, %rv, Hs, Hst, %Hst1, HS, %Hvm1, Hrsp, %Hrv, #Hrvt, #HtlbT, Htok⟩
  · wp_apply wp_getCurrentTerm.1 r γ i s $$ [$HI $Htc $Hs] as Hs
    wp_if_destruct
    · -- a newer term
      rw [show (Follower : val) = #stFollower from rfl]
      wp_apply wp_setState r γ rc i _ stFollower s $$ [$Hr $Hst $Htok] as ⟨Hst, -, Htok⟩
      · isplitr; · ipureintro; left; rfl
        iapply snapProof.obsArg_state γ i s stFollower (by decide)
      ihave Hupd := snapProof.setTerm_step γ i s T HT $$ [$HI $Hs $HokT]
      wp_apply wp_setCurrentTerm r γ rc i sst rq.Term'
        iprop(srvOwn γ i { s with term := T } ∗ termLb γ i T) $$ [$Hr $HS Hupd] as ⟨HS, Hs, #HtlbT⟩
      · rw [HTe]; iexact Hupd
      wp_join_done
      iexists stFollower, _, { RPCHeader' := zeroValDef, Term' := rq.Term', Success' := false }
      iframe
      rw [HTe]
      iframe HtlbT
      isplitr
      · ipureintro; exact ⟨Or.inl rfl, by decide⟩
      isplitr
      · ipureintro; exact snapProof.voteMatches_term sst s rq.Term' T Hvm
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iapply termOk_of_termLb γ i T T (Nat.le_refl _) $$ [$Hvi $HtlbT]
    · have HTs : T = s.term := by
        rw [← HTe]; have : uint.Z (W64 (s.term : Int)) = s.term := by word
        simp only [uint.nat]; word
      wp_join_done
      iexists st, sst, _
      have hs : { s with term := T } = s := by rw [HTs]
      rw [hs]
      iframe
      rw [HTs]
      iframe Htlb0
      isplitr
      · ipureintro; exact ⟨Or.inr ⟨rfl, rfl⟩, Hnl HTs⟩
      isplitr
      · ipureintro; exact Hvm
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iapply termOk_of_termLb γ i _ s.term (by word) $$ [$Hvi $Htlb0]
  -- save the leader
  iStructNamed RPCHeader
  ihave ⟨%xtr, %rpcCh, #Htr, #Hrpcf, #Htrans⟩ := isRaft_transport r γ rc i $$ Hr
  unfold isTransport
  icases Htrans with ⟨-, -, -, -, #Hdec, -⟩
  wp_auto
  wp_join with [Htok]
  · wp_apply Hdec $$ Haddr
    iintro Haddr'
    wp_auto
    wp_apply wp_bytes_to_string $$ Hid as Hid'
    wp_apply wp_setLeader r γ rc i _ _ $$ [$Hr $Htok] as Htok
    wp_join_done
  · wp_apply Hdec $$ Hlead
    iintro Hlead'
    wp_auto
    wp_apply wp_bytes_to_string $$ Hid as Hid'
    wp_apply wp_setLeader r γ rc i _ _ $$ [$Hr $Htok] as Htok
    wp_join_done
  -- the rollback guard: the FSM is at or past the snapshot
  ihave #HappC := isRaft_appliedCell r γ rc i $$ Hr
  wp_apply wp_getLastApplied r rc a $$ [$HappC $Happ] as %la ⟨%Hla, Happ⟩
  wp_if_destruct
  · wp_apply wp_setLastContact r γ rc i $$ [$Hr]
    rw [Hrv2]
    wp_apply wp_Copy_Discard dw rd.ty rd.v R b eof HnWT Hb63 $$ [$Hdw $Heof $HR $HRs] as %n0 %e0 ⟨%k0, %Hk0, HR⟩
    wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [rpc Hrsp] as rpc
    · iframe rpc Hbag
      unfold rpcRespAnyP
      iright
      iexists rsp
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iexists _
      iframe Hrsp
      iapply snapProof.isResp_intro γ { rv with Success' := true } Hrv.1 $$ Hrvt
    iapply HΦ
    iexists { s with term := T }, st1
    iframe Htok
    isplitl
    · iexists a, sst1, cfg, ccfg, cidx, li, lch, γl, bs, c
      iframe # ∗
      isplitr
      · ipureintro; exact Hvm1
      isplitr
      · ileft; ipureintro; exact Hst1.2
      ipureintro; exact ⟨Ha, Hca, Hcf, Hcap⟩
    ileft; ipureintro
    rcases Hst1.1 with h | ⟨h1, h2⟩
    · left; exact h
    · right; exact ⟨h1, h2, rfl⟩
  have Hxa : a < x := by
    rw [← Hxe]; subst Hla
    simp only [uint.nat]
    word
  -- the configuration (version 1)
  wp_apply wp_DecodeConfiguration _ ss DFrac.discard $$ [$HcfgB] as %rcfg ⟨-, Hrcfg⟩
  imod ownSlice_persist $$ Hrcfg with #Hrcfg
  ihave %Hss : ⌜srvsOk γ ss⌝ $$ []
  · unfold snapCfg; icases Hscfg with ⟨%h, -, -⟩; ipureintro; exact h.2.2
  ihave #HcfgR : cfgVal γ rcfg ss $$ []
  · unfold cfgVal; iframe #; ipureintro; exact Hss
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨#Hpv, -⟩
  wp_auto
  wp_apply wp_getSnapshotVersion
  -- the sink, with the install's commit
  ihave ⟨%ssx, %eof', #Hssf, #HSS, -⟩ := isRaft_snapshotStore r γ rc i $$ Hr
  ihave #Hsc := isRaft_snapCell r γ rc i $$ Hr
  imod aeValid_install_CIdx γ ⊤ (by simp) T x stx Hx1 $$ [$HI $Hae] with ⟨%ex, #HCx, %Hex⟩
  ihave #Hfol : snapFollow γ i x stx $$ []
  · unfold snapFollow
    iexists T, snd
    iframe #
    ipureintro; exact ⟨Hsnd, Hx1⟩
  unfold isSnapStore
  icases HSS with ⟨#HCreate, -, -⟩
  wp_auto
  wp_bind
  iapply HCreate
  iintro %k %sid Hcont
  imod Hcont $$ %(fun bs => iprop(⌜bs = b⌝ ∗ monoNatAuthOwn rc.names.applied (1 : Qp).half a ∗
      ghostVar rc.names.pend (1 : Qp).half (none : Option (Nat × Nat × GoString))))
    %(fun _ => iprop(ghostVar rc.names.pend (1 : Qp).half (some (x, stx, sid)))) [] with
    ⟨%own, #Hsink, Hown⟩
  · iintro %bs %_ ⟨%Hbs, Happ, Hpnd⟩
    subst bs
    iapply snapProof.install_commit γ rc i x stx a sid (W64 1) rq.LastLogIndex' rq.LastLogTerm'
      rq.ConfigurationIndex' rcfg b ex Hxe Hste rfl ss Hb63 Hxa Hx1 Hex
    iframe # ∗
  wp_auto
  -- copy the stream into the sink through a counting reader, with a transfer monitor
  rw [Hrv2]
  wp_apply wp_newCountingReader as %cr #Hcr
  wp_apply wp_startMonitor as %mon #Hmon
  have HnWTc : go.typeSetContains (go.GoType.PointerType countingReader.ty) io.WriterTo.ty = false := by
    go_type_set
  ihave #HRc := snapProof.streamReader_counting wp_cr_Read cr rd R eof Heofnn $$ [$Hpkg $Hcr $HRd]
  ihave #HWs := snapProof.streamWriter_sink k sid own _ _ $$ Hsink
  ihave #Hsink' := Hsink
  unfold isSink
  icases Hsink' with ⟨%HnRF, -, #HClose, #HClose2, #HCancel, #HID⟩
  rw [show GoInterface.ok k = interface.mkOk k.ty k.v from rfl] at *
  wp_apply (wp_Copy k.ty (go.GoType.PointerType countingReader.ty) k.v #cr R
    (fun ws => own (some ws)) b [] eof HnWTc HnRF Hb63) $$ [$Heof $HR $Hown $HRc $HWs]
    as %nw %cerr ⟨%kr, %kw, %Hk, HR, Hown⟩
  wp_apply wp_StopAndWait mon $$ [$Hmon]
  obtain ⟨Hkwr, Hkrb, Hnw, Hcok⟩ := Hk
  cases cerr with
  | ok ce =>
    -- the copy failed: cancel the sink, respond with the error
    try wp_auto
    wp_apply HCancel $$ %(some ([] ++ b.take kw)) Hown as Hown
    rw [Hrv2]
    wp_apply wp_Copy_Discard dw rd.ty rd.v R (b.drop kr) eof HnWT (by simp; omega)
      $$ [$Hdw $Heof $HR $HRs] as %n0 %e0 ⟨%k0, %Hk0, HR⟩
    wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [rpc] as rpc
    · iframe rpc Hbag
      unfold rpcRespAnyP
      ileft; ipureintro; simp
    iapply HΦ
    iexists { s with term := T }, st1
    iframe Htok
    isplitl
    · iexists a, sst1, cfg, ccfg, cidx, li, lch, γl, bs, c
      iframe # ∗
      isplitr
      · ipureintro; exact Hvm1
      isplitr
      · ileft; ipureintro; exact Hst1.2
      ipureintro; exact ⟨Ha, Hca, Hcf, Hcap⟩
    ileft; ipureintro
    rcases Hst1.1 with h | ⟨h1, h2⟩
    · left; exact h
    · right; exact ⟨h1, h2, rfl⟩
  | nil =>
  obtain ⟨Hkr, Hkw⟩ := Hcok rfl
  subst Hkr Hkw
  have HnwS : nw = rq.Size' := by
    have h1 : sint.Z nw = b.length := Hnw
    have h2 : uint.nat rq.Size' = b.length := Hsize
    apply word.unsigned_inj
    have : (b.length : Int) < 2 ^ 63 := by omega
    word
  wp_auto
  rw [decide_eq_true HnwS]
  wp_auto
  -- close the sink: the install's commit (the pending record)
  simp only [List.nil_append, List.take_length]
  wp_apply HClose $$ %b Hown [Happ Hpnd] as Hown Hpnd
  · iframe; ipureintro; rfl
  wp_apply HID
  -- the restore future
  ihave #Hsd := isRaft_shutdownCh r γ rc i $$ Hr
  unfold deadField deadChan
  icases Hsd with ⟨%sch, #Hsch, %γs, #Hsbag⟩
  irename «$r0» => Hfut
  generalize «$r0_ptr» = f at *
  iStructNamed Hfut
  try simp only [zeroValDef] at *
  iStructNamed deferError
  ipersist ID
  wp_auto
  wp_apply (lc := 3) snapFut.wp_rf_init f (restoreQ rc x stx sid) null $$ [$errCh]
    as ⟨%ech, %γe, %Hne, HerrCh, #Hspsc, HeP, HeC⟩
  ipersist HerrCh
  ipersist ShutdownCh
  ihave #Hchans := isRaft_fsmCh r γ rc i $$ Hr
  icases Hchans with ⟨%fch, #Hfch, #Hfsp⟩
  imod snapProof.fsmProd_restore_send γ rc i a x
      (interface.mkOk (go.GoType.PointerType restoreFuture.ty) #f) Hxa
    $$ [Hprod Hpnd HeP responded] with ⟨%sent, Hp, HP, Hk⟩
  · iframe Hprod
    iintro %k0 %Hk0
    unfold fsmRestoreP
    iexists f, sid, stx
    iframe Hpnd ID
    isplitr
    · ipureintro; exact ⟨rfl, by omega⟩
    isplitr
    · iexists ex; iframe HCx; ipureintro; exact Hex
    unfold deferResp
    iexists ech
    iframe HerrCh
    iright
    iexists γe
    iframe
    iframe #
    ipureintro; exact Hne
  wp_auto
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · dsimp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, fch,
      rc.names.fsmCh.chanName, interface.mkOk (go.GoType.PointerType restoreFuture.ty) #f
    isplitr
    · ipureintro
      exact ⟨rfl, rfl⟩
    ihave #Hch : isChan fch rc.names.fsmCh.chanName GoInterface $$ [Hfsp]
    · unfold isSpsc; icases Hfsp with ⟨$, -⟩
    iframe Hch
    iapply spsc_send_au $$ Hfsp [$Hlc1 $Hlc2 $Hlc3] [$Hp $HP]
    inext
    iintro Hp
    ihave Hprod := Hk $$ Hp
    wp_auto
    -- the restore's answer: nil, with the pending record's half back
    wp_apply snapFut.wp_rf_Error wp_Error f (restoreQ rc x stx sid) $$ [HeC err] as %rerr Hrq
    · unfold deferWait
      iexists ech, γe
      iframe HerrCh Hspsc HeC err
      isplitr
      · ipureintro; exact Hne
      iexists sch; iframe ShutdownCh; iright; unfold deadChan; iexists γs; iexact Hsbag
    unfold restoreQ
    icases Hrq with ⟨%Hrerr, Hpnd⟩
    subst Hrerr
    wp_auto
    -- setLastApplied(x): the pending record ends
    wp_bind
    iapply (wp_setLastApplied r rc rq.LastLogIndex') $$ [$Hpkg $HappC]
    rw [Hxe]
    iapply (snapProof.install_applied_au γ rc i x stx sid _)
    iframe Hsc Hpnd
    iintro Hpnd Happ
    wp_auto
    ihave #HlbX := snapProof.applLb_get rc _ x $$ Happ
    wp_apply wp_setLastSnapshot r γ rc i rq.LastLogIndex' rq.LastLogTerm' $$ [$Hr]
    · iright; iexists ex
      rw [Hxe, Hste]
      iframe HCx HlbX
      isplitr
      · ipureintro; exact Hex
      iright; iexact Hfol
    ihave #Hconf := isRaft_conf r γ rc i $$ Hr
    unfold raftConf
    icases Hconf with ⟨%cc0, -, -, #HlcI⟩
    wp_apply wp_setLatestConfiguration false r γ ccfg cfg cidx li rcfg rq.ConfigurationIndex' ss
      DFrac.discard null $$ [$Hcfgs $Hrcfg] as ⟨Hcfgs, -, -⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]
      iframe HlcI; ipureintro; exact Or.inr Hss
    wp_apply wp_setCommittedConfiguration r ccfg rcfg cidx rq.ConfigurationIndex' rcfg rq.ConfigurationIndex'
      $$ [$Hcfgs] as Hcfgs
    -- not a MonotonicLogStore: keep or discard
    ihave ⟨%lsx, #Hlsf, #Hls, %HnM⟩ := isRaft_logStore r γ rc i $$ Hr
    wp_auto
    simp only [HnM]
    wp_auto
    ihave #HlogC := isRaft_logCell r γ rc i $$ Hr
    unfold isLogStore
    icases Hls with ⟨-, -, #HGetLog, -, -, #HDel⟩
    wp_bind
    iapply HGetLog $$ %rq.LastLogIndex' %last_ptr %_ %tid %_ last Htok
    rw [Hxe]
    iapply (snapProof.logCell_getLog γ rc i { s with term := T } c x (by omega) _)
    iframe HI HlogC Hs Hlp Hcomp
    iintro %LA %Hm Hs Hlp Hcomp %gerr Hpost Htok
    have HPM := snapProof.getLog_prevMatch s.log LA.m x stx Hx1 Hm.1 Hm.2
    imod snapProof.compLb_raise rc c x (by omega) $$ Hcomp with ⟨Hcomp, #HcLb⟩
    unfold getLogPost
    -- keep (the log holds the snapshot's last entry) or discard
    wp_join iprop(∃ (s' : SState) (cfg' ccfg' : Configuration) (cidx' li' : w64),
        srvOwn γ i s' ∗ durView γ i (1 : Qp).half s'.dur.1 ∗
        ghostVar rc.names.lastLog (1 : Qp).half (s'.log.length, lastTerm s'.log) ∗
        ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗ rtok tid ∗ (∃ lv : Log, last_ptr ↦ lv) ∗
        monoNatAuthOwn rc.names.comp 1 x ∗
        r.[Raft, go!"configurations"] ↦ configurations.mk ccfg' cidx' cfg' li' ∗
        cfgAtIs γ s'.log (uint.nat li') cfg' ∗ cfgAtIs γ s'.log (uint.nat cidx') ccfg' ∗
        cmtIdx γ s'.term s'.log (uint.nat cidx') ∗
        ⌜uint.nat li' = lastCfgIdx s'.log ∧ (cidx' = li' ∨
          (uint.nat cidx' = lastCfgIdx (s'.log.take (uint.nat li' - 1)) ∧ x < uint.nat li'))⌝ ∗
        ⌜s'.term = T ∧ s'.cidx = s.cidx ∧ x ≤ s'.dur.1 ∧ s'.vterm = s.vterm ∧ s'.vcand = s.vcand⌝)
      at next with [Hs Hdv Hll Hlp Htok Hpost Hcomp Hcfgs]
      as ⟨%s', %cfg', %ccfg', %cidx', %li', Hs, Hdv, Hll, Hlp, Htok, -, Hcomp, Hcfgs, #Hli', #Hci', #Hcm',
        %Hcf', %Hs'⟩
    · cases hl : LA.m.lookup x with
      | none =>
        icases Hpost with ⟨%Hge, -, %lv, last⟩
        have HNPM : ¬ prevMatch s.log x stx := HPM.2 (Or.inl hl)
        obtain ⟨gx, rfl⟩ : ∃ gx, gerr = GoInterface.ok gx := by
          cases gerr with
          | nil => exact absurd rfl Hge
          | ok gx => exact ⟨gx, rfl⟩
        wp_auto
        wp_apply (wp_getLastLog.1 r γ rc i _ _) $$ [$Hr $Hll] as %li %lt ⟨%Hlilt, Hll⟩
        have Hli62 : uint.nat li < 2 ^ 62 := by rw [Hlilt.1]; exact Hsf.2.2.2.2.2.2.1
        wp_bind
        iapply HDel $$ %(W64 1) %li %_ []
        · ipureintro; omega
        rw [show uint.nat (W64 1) = 1 from rfl]
        iapply (snapProof.logCell_discard γ rc i { s with term := T } x stx snd Hsnd Hx1 HNPM
          (uint.nat li) Hlilt.1 _)
        iframe HI HlogC Hs Hdv Hae HlT Hlp HcLb
        iintro %L' %d Hs Hdv #Hdl %Hfacts Hlp
        obtain ⟨hL1, hL2, hL3⟩ := Hfacts
        imod snapProof.install_cfgs γ ⊤ (by simp) i { s with term := T, log := L', dur := d } x
          (uint.nat rq.ConfigurationIndex') ss rcfg (by dsimp only; omega) $$ [$HI $Hs $Hscfg $Hrcfg]
          with ⟨Hs, #Hcci, #Hcmci, %Hci⟩
        wp_auto
        wp_apply wp_setLastLog r γ rc i _ rq.LastLogIndex' rq.LastLogTerm' $$ [$Hr $Hll] as Hll
        wp_join_done
        iexists { s with term := T, log := L', dur := d }, rcfg, rcfg, rq.ConfigurationIndex',
          rq.ConfigurationIndex'
        rw [Hxe, Hste]
        dsimp only at Hci ⊢
        have htk : L'.take x = L' := List.take_of_length_le (by omega)
        rw [htk] at Hci
        rw [hL1, hL2, hL3]
        iframe Hs Hdv Hll Hlp Htok Hcomp Hcfgs Hcci Hcmci
        isplitl
        · iexists _; iexact last
        ipureintro; exact ⟨⟨Hci.1.symm, Or.inl rfl⟩, rfl, rfl, Nat.le_refl _, rfl, rfl⟩
      | some e =>
        icases Hpost with ⟨%Hge, %lv, last, #Hlogis⟩
        subst Hge
        unfold logIs
        icases Hlogis with ⟨%Hlv, -, -⟩
        wp_auto
        by_cases hte : e.term = stx
        · -- keep: the log holds the snapshot's last entry
          have Heqt : lv.Term' = rq.LastLogTerm' := by
            have h : uint.nat lv.Term' = uint.nat rq.LastLogTerm' := by rw [Hlv.2.1, hte, Hste]
            word
          rw [decide_eq_true Heqt]
          wp_auto
          have hpm := HPM.1 e hl hte
          imod learnCommitFollower γ ⊤ (by simp) i { s with term := T } x stx [] x x
            ⟨hpm, ⟨Nat.le_refl _, fun j h => absurd h (Nat.not_lt_zero _)⟩, by simp, by simp; omega⟩
            $$ [$HI $Hs $Hdv $Hae] with ⟨%d, Hs, Hdv, #Hdl, %Hd⟩
          rw [Nat.min_self] at *
          imod durLb_lt γ ⊤ (by simp) i x $$ [$HI $Hvi $Hdl] with %Hx62
          have Hxd : x ≤ d.1 := by rw [Hd]; omega
          -- (stage 4) the snapshot's configuration is the log's latest at or below `x`
          imod snapProof.install_cfgs γ ⊤ (by simp) i { s with term := T, dur := d } x
            (uint.nat rq.ConfigurationIndex') ss rcfg Hxd $$ [$HI $Hs $Hscfg $Hrcfg]
            with ⟨Hs, #Hcci, #Hcmci, %Hci⟩
          imod srvOwn_facts γ ⊤ (by simp) i { s with term := T, dur := d } $$ [$HI $Hs]
            with ⟨Hs, -, %Hsf2⟩
          ihave %Hcv := isRaft_cv r γ rc i $$ Hr
          wp_apply (wp_getLastLog.1 r γ rc i _ _) $$ [$Hr $Hll] as %lli %llt ⟨%Hlilt, Hll⟩
          ipersist lastLogIdx
          -- the scan of the kept entries `(x, |log|]` (fix `cc3148d`): their configurations
          have hx1 : rq.LastLogIndex' + W64 1 = W64 ((x + 1 : Nat) : Int) := by
            apply word.unsigned_inj; rw [← Hxe] at Hx62 ⊢; word
          ihave HIk : (∃ (k : Nat) (cfg' ccfg' : Configuration) (cidx' li' : w64),
              "index" ∷ index_ptr ↦ W64 k ∗
              "Hcfgs" ∷ r.[Raft, go!"configurations"] ↦ configurations.mk ccfg' cidx' cfg' li' ∗
              "Hs" ∷ srvOwn γ i { s with term := T, dur := d } ∗
              "Hlp" ∷ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗
              "Hcomp" ∷ monoNatAuthOwn rc.names.comp 1 x ∗ "Htok" ∷ rtok tid ∗
              "#Hli'" ∷ cfgAtIs γ s.log (uint.nat li') cfg' ∗
              "#Hci'" ∷ cfgAtIs γ s.log (uint.nat cidx') ccfg' ∗
              "#Hcm'" ∷ cmtIdx γ T s.log (uint.nat cidx') ∗
              "%Hk" ∷ ⌜x + 1 ≤ k ∧ k ≤ s.log.length + 1 ∧
                uint.nat li' = lastCfgIdx (s.log.take (k - 1)) ∧
                (cidx' = li' ∨ (uint.nat cidx' = lastCfgIdx (s.log.take (uint.nat li' - 1)) ∧
                  x < uint.nat li'))⌝ : IProp GF) $$ [index Hcfgs Hs Hlp Hcomp Htok]
          · iexists x + 1, rcfg, rcfg, rq.ConfigurationIndex', rq.ConfigurationIndex'
            rw [hx1]
            iframe index Hcfgs Hs Hlp Hcomp Htok Hcci Hcmci
            ipureintro
            dsimp only at Hci
            refine ⟨Nat.le_refl _, by omega, ?_, Or.inl rfl⟩
            rw [Nat.add_sub_cancel]; exact Hci.1.symm
          wp_for HIk
          split
          · rename_i Hc
            have hkn : k ≤ s.log.length := by
              have h1 : uint.nat lli = s.log.length := Hlilt.1
              simp only [decide_eq_true_eq] at Hc
              have hl62 : s.log.length < 2 ^ 62 := Hsf.2.2.2.2.2.2.1
              have h2 : k < 2 ^ 63 := by omega
              rw [← h1]; word
            obtain ⟨ek, hek⟩ := proto.ent_isSome s.log k (by omega) hkn
            wp_auto
            wp_bind
            iapply HGetLog $$ %(W64 k) %entry_ptr %_ %tid %_ entry Htok
            rw [show uint.nat (W64 (k : Int)) = k by word]
            iapply (snapProof.logCell_getLog γ rc i { s with term := T, dur := d } x k (by omega) _)
            iframe HI HlogC Hs Hlp Hcomp
            iintro %LA %Hm Hs Hlp Hcomp %gerr Hpost Htok
            have hLA : LA.m.lookup k = some ek := by rw [Hm.2 hkn]; exact hek
            rw [show LA.m !! k = some ek from hLA]
            icases Hpost with ⟨%Hge, %lvk, Hent, #Hlogk⟩
            subst Hge
            icases Hlogk with ⟨%Hlvk, #Hdatk, -⟩
            wp_auto
            have hkind := Hsf2.2.2.2.2.2.2.2.2 k ek hek
            have hty : uint.nat lvk.Type' = ek.kind := Hlvk.2.2
            have hT23 : lvk.Type' ≠ W8 2 ∧ lvk.Type' ≠ W8 3 := by
              constructor <;> intro h <;> rw [h] at hty <;>
                simp only [kCommand, kNoop, kBarrier, kConfig] at hkind <;> word
            have hidx : uint.nat lvk.Index' = k := Hlvk.1
            have htk := snapProof.take_ent s.log k ek hek
            by_cases hck : ek.kind = kConfig
            · -- a configuration entry: it becomes the latest, the previous latest the committed one
              have hv := Hsf2.2.2.2.2.2.2.2.1 k ek hek hck
              rw [Hcv] at hv
              obtain ⟨ssk, hdk, hssk⟩ := cfgDec_valid γ.srvs ek.data hv.1
              imod cfgPrevCommitted γ ⊤ (by simp) i { s with term := T, dur := d } k ek hek hck
                $$ [$HI $Hs] with ⟨Hs, #Hpcm⟩
              wp_apply wp_processConfigurationLogEntry false r γ entry_ptr lvk (DFrac.own 1) ccfg' cfg'
                cidx' li' null $$ [$Hent $Hcfgs] as ⟨Hent, Hpc⟩
              · isplitr
                · ipureintro; exact hT23
                iright
                isplitr
                · iexists ssk; rw [← hdk]; iframe Hdatk; ipureintro; exact hssk
                simp only [Bool.false_eq_true, ↓reduceIte]; iexact HlcI
              icases Hpc with (⟨%Hn5, -⟩ | ⟨%cn, %ssn, %Hc5, Hcfgs, #Hdatn, Hcn, -⟩)
              · exfalso; apply Hn5
                have h5 : uint.nat lvk.Type' = 5 := by rw [hty, hck]; rfl
                word
              ihave %Hdeq := ownSlice_agree _ _ _ _ _ $$ Hdatk Hdatn
              wp_for_post_core
              imod ownSlice_persist $$ Hcn with #Hcn
              try wp_auto
              iframe
              iexists k + 1, cn, cfg', li', lvk.Index'
              have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
              rw [hctr]
              iframe index Hcfgs Hs Hlp Hcomp Htok Hli'
              isplitr
              · unfold cfgAtIs; iright; iexists ssn, ek; unfold cfgVal; iframe Hcn
                isplitr
                · ipureintro; exact Hc5.2
                ipureintro; rw [hidx]; exact ⟨by omega, hek, hck, Hdeq⟩
              isplitr
              · rw [Hk.2.2.1]; iexact Hpcm
              ipureintro
              refine ⟨by omega, by omega, ?_, Or.inr ⟨?_, by omega⟩⟩
              · rw [hidx, Nat.add_sub_cancel, htk, proto.lastCfgIdx_append_cfg _ _ hck]
                simp only [List.length_take]; omega
              · rw [hidx]; exact Hk.2.2.1
            · -- any other entry changes nothing
              wp_apply wp_processConfigurationLogEntry false r γ entry_ptr lvk (DFrac.own 1) ccfg' cfg'
                cidx' li' null $$ [$Hent $Hcfgs] as ⟨Hent, Hpc⟩
              · isplitr
                · ipureintro; exact hT23
                ileft; ipureintro; intro h; apply hck; rw [← hty, h]; rfl
              icases Hpc with (⟨%Hn5, Hcfgs⟩ | ⟨%cn, %ssn, %Hc5, -⟩)
              rotate_left
              · exfalso; apply hck; rw [← hty, Hc5.1]; rfl
              wp_for_post
              iframe
              iexists k + 1, cfg', ccfg', cidx', li'
              have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
              rw [hctr]
              iframe index Hcfgs Hs Hlp Hcomp Htok Hli' Hci' Hcm'
              ipureintro
              refine ⟨by omega, by omega, ?_, Hk.2.2.2⟩
              rw [Nat.add_sub_cancel, htk, proto.lastCfgIdx_append_noCfg _ _ (by simpa using hck)]
              exact Hk.2.2.1
          rename_i Hc
          have hkn : k = s.log.length + 1 := by
            have h1 : uint.nat lli = s.log.length := Hlilt.1
            simp only [decide_eq_true_eq] at Hc
            have hl62 : s.log.length < 2 ^ 62 := Hsf.2.2.2.2.2.2.1
            have h2 : k < 2 ^ 63 := by omega
            rw [← h1]; word
          wp_auto
          wp_apply wp_compactLogs r γ rc i rq.LastLogIndex' tid $$ [$Hr $Htok] as %cerr ⟨%Hce, Htok⟩
          · rw [Hxe]; iframe HcLb; ipureintro; exact Hx62
          subst Hce
          wp_auto
          wp_join_done
          iexists { s with term := T, dur := d }, cfg', ccfg', cidx', li'
          iframe Hs Hdv Hll Hlp Htok Hcomp Hcfgs Hli' Hci' Hcm'
          isplitl
          · iexists _; iexact last
          ipureintro
          have htn : s.log.take (k - 1) = s.log := by
            rw [hkn, Nat.add_sub_cancel]; exact List.take_length
          refine ⟨⟨?_, Hk.2.2.2⟩, rfl, rfl, ?_, rfl, rfl⟩
          · rw [Hk.2.2.1, htn]
          · dsimp only; omega
        · have HNPM : ¬ prevMatch s.log x stx := HPM.2 (Or.inr ⟨e, hl, hte⟩)
          have Hneqt : lv.Term' ≠ rq.LastLogTerm' := by
            intro h; apply hte; rw [← Hlv.2.1, ← Hste, h]
          rw [decide_eq_false Hneqt]
          wp_auto
          wp_apply (wp_getLastLog.1 r γ rc i _ _) $$ [$Hr $Hll] as %li %lt ⟨%Hlilt, Hll⟩
          have Hli62 : uint.nat li < 2 ^ 62 := by rw [Hlilt.1]; exact Hsf.2.2.2.2.2.2.1
          wp_bind
          iapply HDel $$ %(W64 1) %li %_ []
          · ipureintro; omega
          rw [show uint.nat (W64 1) = 1 from rfl]
          iapply (snapProof.logCell_discard γ rc i { s with term := T } x stx snd Hsnd Hx1 HNPM
            (uint.nat li) Hlilt.1 _)
          iframe HI HlogC Hs Hdv Hae HlT Hlp HcLb
          iintro %L' %d Hs Hdv #Hdl %Hfacts Hlp
          obtain ⟨hL1, hL2, hL3⟩ := Hfacts
          imod snapProof.install_cfgs γ ⊤ (by simp) i { s with term := T, log := L', dur := d } x
            (uint.nat rq.ConfigurationIndex') ss rcfg (by dsimp only; omega) $$ [$HI $Hs $Hscfg $Hrcfg]
            with ⟨Hs, #Hcci, #Hcmci, %Hci⟩
          wp_auto
          wp_apply wp_setLastLog r γ rc i _ rq.LastLogIndex' rq.LastLogTerm' $$ [$Hr $Hll] as Hll
          wp_join_done
          iexists { s with term := T, log := L', dur := d }, rcfg, rcfg, rq.ConfigurationIndex',
            rq.ConfigurationIndex'
          rw [Hxe, Hste]
          dsimp only at Hci ⊢
          have htk : L'.take x = L' := List.take_of_length_le (by omega)
          rw [htk] at Hci
          rw [hL1, hL2, hL3]
          iframe Hs Hdv Hll Hlp Htok Hcomp Hcfgs Hcci Hcmci
          isplitl
          · iexists _; iexact last
          ipureintro; exact ⟨⟨Hci.1.symm, Or.inl rfl⟩, rfl, rfl, Nat.le_refl _, rfl, rfl⟩
    obtain ⟨Hs'T, Hs'c, Hs'd, Hs'vt, Hs'vc⟩ := Hs'
    wp_apply wp_setLastContact r γ rc i $$ [$Hr]
    rw [Hrv2]
    wp_apply wp_Copy_Discard dw rd.ty rd.v R (b.drop b.length) eof HnWT (by simp)
      $$ [$Hdw $Heof $HR $HRs] as %n0 %e0 ⟨%k0, %Hk0, HR⟩
    wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [rpc Hrsp] as rpc
    · iframe rpc Hbag
      unfold rpcRespAnyP
      iright
      iexists rsp
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iexists _
      iframe Hrsp
      iapply snapProof.isResp_intro γ { rv with Success' := true } Hrv.1 $$ Hrvt
    iapply HΦ
    iexists s', st1
    iframe Htok
    isplitl
    · iexists x, sst1, cfg', ccfg', cidx', li', lch, γl, bs, x
      iframe # ∗
      isplitr
      · ipureintro
        unfold voteMatches at Hvm1 ⊢
        rw [Hs'vt, Hs'vc]; exact Hvm1
      isplitr
      · ileft; ipureintro; exact Hst1.2
      ipureintro; exact ⟨⟨Hs'd, by omega⟩, Nat.le_refl _, Hcf', Hcap⟩
    rcases Hst1.1 with h | ⟨h1, h2⟩
    · ileft; ipureintro; left; exact h
    · rcases Hstv with h3 | h3 | h3
      · ileft; ipureintro; left; rw [h1, h3]
      · iright
        isplitr
        · ipureintro; exact ⟨h1, h3, by rw [Hs'T, h2]⟩
        iexists snd
        rw [← h2]
        iframe HlT
        ipureintro; exact Hsnd
      · exact absurd (h1.trans h3) Hst1.2
  iapply BigAndL.bigAndL_cons.2
  isplit
  · dsimp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sch, γs
    isplitr
    · ipureintro; rfl
    ihave #Hsc0 := is_bag_is_chan _ _ _ $$ Hsbag
    iframe Hsc0
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hsbag
    inext
    iintro %v HF
    iexfalso; iexact HF
  · iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end Perennial
