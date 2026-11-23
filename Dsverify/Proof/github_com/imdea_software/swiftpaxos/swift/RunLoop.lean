/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RunLoop.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.run()` (swift.go): the connection phase (`ConnectToPeers` once the table is `tableOk`,
`ComputeClosestPeers`, the latencies' float loop writing `cs.maxLatency`, `go
WaitForClientConnections()`), then the `select` loop over its ten channels, each arm calling
its callees' specs (`swift.RunArms`) over the loop invariant of `swift.RunLoopH`
(RunLoopSpecs.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunLoopSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyChan

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

set_option goose.wp.extras true

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [swift.Assumptions] [replica.Assumptions]
  [replica.defs.Assumptions] [rpc.Assumptions] in
/-- `IsNilDepOfCmdId(a.CmdId, a.Dep)` on an `MOptAcks` entry, as the model's `dep = [id]`. -/
theorem swift.nilDep_iff (D : List sp.CmdId) (c : swift.CommandId) (y : sp.CmdId)
    (h : toCmdId c = y) : (D.map ofCmdId = [c]) ↔ D = [y] := by
  subst h
  constructor
  · intro e
    have := congrArg (List.map toCmdId) e
    simpa [List.map_map, Function.comp_def] using this
  · intro e; subst e; simp

/-- The witness of the `MFastAck` built from an `MOptAcks` entry. -/
theorem swift.runAckW_of_opt (γ : sp.Names) (γc γm : GName) (r b : w32) (al : List sp.Ack)
    (a : sp.Ack) (ha : a ∈ al) :
    ⌜sp.wireOk r b⌝ ∗ sp.ackOk γ (sp.rid r) (sp.bal b) a ∗
      (⌜∀ a ∈ al, a.dep ≠ [a.id]⌝ ∨ ∃ N fr l, sp.cfg γc γm N fr l ∗ ⌜sp.rid r ≠ sp.leaderOf N (sp.bal b)⌝) ⊢
      swift.runAckW γ γc γm (swift.fastOfAck r b a) := by
  iintro ⟨%Hw, #Ha, Hnl⟩
  unfold swift.runAckW
  simp only [swift.fastOfAck]
  iright
  iexists a
  isplitr
  · ipureintro; exact ⟨rfl, Hw⟩
  isplitr
  · iexact Ha
  icases Hnl with (%H | Hc)
  · ileft; ipureintro; exact H a ha
  · iright; iexact Hc

/-- The representation of the `MFastAck` built from an `MOptAcks` entry. -/
theorem swift.fastAckRepr_of_opt (a : swift.Ack) (A : sp.Ack) (r b : w32) (dsl : GoSlice)
    (hd : dsl = if A.dep = [A.id] then slice.nil else a.Dep') :
    swift.ackRepr a A ⊢
      swift.fastAckRepr (swift.MFastAck.mk r b a.CmdId' dsl a.Checksum' a.Seqnum')
        (swift.fastOfAck r b A) := by
  unfold swift.ackRepr swift.fastAckRepr
  simp only [swift.fastOfAck]
  iintro ⟨%Ha, #Hd, #Hc⟩
  isplitr
  · ipureintro; exact ⟨trivial, trivial, Ha.1, Ha.2⟩
  isplitr
  · by_cases h : A.dep = [A.id]
    · simp only [h, ↓reduceIte] at hd ⊢
      subst hd
      simp only [List.map_nil]
      iapply (ownSlice_nil (V := swift.CommandId) DFrac.discard)
    · simp only [h, ↓reduceIte] at hd ⊢
      subst hd
      iexact Hd
  · iexact Hc

set_option hygiene false in
/-- N2-loop: the end of a `select` arm: the step's `drainRechecks` (`RunArms.drain`), then the
loop's next iteration (inside an inner loop, its next iteration). -/
macro "runPost" : tactic => `(tactic| first
  | wp_for_post
  | ((try wp_auto); wp_apply ar.drain $$ [HI] as HI; iexact HI; (try wp_auto); wp_for_post))

set_option maxHeartbeats 4000000 in
theorem swift.Replica.run.wp_proof (X : Type)
    (I : Loc → sp.Names → GName → GName → X → IProp netDistGF) (H : swift.RunLoopH X I)
    (htab : swift.tableAllocH)
    (wp_conn : replica.Replica.ConnectToPeers.spec (hG := hG))
    (wp_closest : replica.Replica.ComputeClosestPeers.spec (hG := hG))
    (wp_wait : replica.Replica.WaitForClientConnections.spec (hG := hG))
    (wp_senda : replica.Sender.SendToAll.spec (hG := hG))
    (hmnl : swift.MNewLeader.marshalH (hG := hG))
    (wp_new : swift.newFastAck.specP (hG := hG))
    (wp_copy : swift.copyFastAck.specP (hG := hG)) :
    swift.Replica.run.specI (hG := hG) := by
  intro rp γ γc γm γl N k me fr l a ip pl
  wp_start as Hpre
  iunfold swift.runPre at Hpre
  icases Hpre with ⟨%rr, %tbl, %s, %b, %rc, %qs, %γs, %γrl, %γd, %γdc1, %γdl, %dm1, %dch, %rch,
    %γdc, %γrc, %hsl, %km, %hm, %pm, %propm, %accm, %waitm, %sam, %sq, %fq, %csv, %ents, %nid, %d,
    #Hrcvr, #Hinv, #Hcfg, %Hids, #FReplica, #RShutdown, #RN, #RId, #Fsender, #Hsbag, #Fbatcher,
    #Hbh, #FSQ, #HSQq, #Fhistory, #FhistoryStart, #FoptExec, #FfastRead, #FfixedMajority, #FpoolLevel,
    #FslowAddrs, #Hsam, #FdeliverChan, #FrecheckChan, #Hmax, %Hdb, #Hpool, #Hshard, #Hcell, #Hgcs,
    Hstart, Fballot, Fcballot, Fstatus, FFQ, #HFQok, FcmdDescs, #Hdm1, Hv1, Hrd1, Hγd, Hdel,
    Frepchan, #Hrch, Fkeys, Hkm, Fhlog, Hhm, FcntL, Fseqnum, FpendingHashUpds, Hpm, FhistoryL,
    Hhsl, #Fqs, Fcs, %Hcs, Hchans, FexecL, FexecLog, HdescPool, FroutineCount, FrecStart,
    FnewLeaderAckNs, FnlBal, Fproposes, Hpropm, Fhandled, FlastSync, FacceptL, Faccepted, Haccm,
    Fwaiting, Hwaitm, Frechecks, #Hdch, Hdown, #Hrchan, Hrown, HPPO, HState, #RExec, HDreply, #RRPC, Htbl,
    Hconn, HpDeps, #Hng⟩
  -- the table: `tableOk`, the channels' bags; then `connPre`
  iapply fupd_wp
  ihave #Hspkg : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift $$ []
  · iPkgInit
  imod htab γ γc γm csv ents _ $$ [$Hspkg $Hgcs $Hpool $Hchans] with ⟨%n, #Htab, #Hbags⟩
  · ipureintro; exact Hcs.2
  imod rpc.isTable_persist $$ Htbl with #Htbl
  imodintro
  ihave Hcp := Hconn $$ Htab Htbl
  ihave #Hrpkg : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica $$ []
  · iPkgInit
  ihave #Hbpkg : isPkgInit (PROP := IProp netDistGF) pkg_id.bufio $$ []
  · iPkgInit
  ihave #Hnpkg : isPkgInit (PROP := IProp netDistGF) pkg_id.net $$ []
  · iPkgInit
  ihave #Hipkg : isPkgInit (PROP := IProp netDistGF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hepkg : isPkgInit (PROP := IProp netDistGF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hspkg : isPkgInit (PROP := IProp netDistGF) pkg_id.strings $$ []
  · iPkgInit
  wp_auto
  wp_method_call
  wp_auto
  wp_apply wp_conn rr γ γc γm γl N me a ip $$ [$Hcp] as ⟨%γw, #HisR, Hserve⟩
  · iPkgInit
  icases HPPO with ⟨%ppsl, %pp, HPPO, Hpp, %Hpp⟩
  wp_method_call
  wp_auto
  wp_apply wp_closest rr γ γc γm γw N me ppsl pp $$ [$HPPO $Hpp] as %lsl ⟨%ls, %ppsl', %pp',
    Hlsl, %Hlsl, HPPO, Hpp, %Hpp'⟩
  · iframe HisR; ipureintro; exact Hpp.2
  -- the latencies' loop: `cs.maxLatency` becomes some duration
  ihave HL : (∃ (iv : w64) (ml : w64) (fl : w64),
      "i" ∷ i_ptr ↦ iv ∗ "l" ∷ l_ptr ↦ fl ∗
      "Fcs" ∷ swift.fld rp go!"cs" ↦ { csv with maxLatency' := ml } ∗
      "Hlsl" ∷ lsl ↦* ls ∗ "%Hi" ∷ ⌜0 ≤ sint.Z iv⌝ : IProp netDistGF) $$ [i l Fcs Hlsl]
  · iexists (W64 0), csv.maxLatency', _
    iframe
    ipureintro; decide
  wp_for HL
  ihave %Hll := ownSlice_len _ _ _ $$ Hlsl
  by_cases hlt : sint.Z iv < sint.Z lsl.len
  · simp only [hlt, _root_.decide_true]
    cleanup_bool_decide
    try rw [if_pos (show True from trivial)]
    try rw [if_neg (show ¬ (decide ((#false : val) = #true) = true) by simp [Perennial.false_neq_true])]
    wp_auto
    have hi0 : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z lsl.len := ⟨Hi, hlt⟩
    try isimp only [hi0, _root_.and_self, ↓reduceIte]
    obtain ⟨x, hx⟩ : ∃ x, ls[(sint.Z iv).toNat]? = some x := by
      have h1 := Hll.1
      have e := swift.snat_eq lsl.len Hll.2
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_apply wp_load_slice_index lsl (sint.Z iv) ls _ x Hi $$ [Hlsl] as Hlsl
    · iframe Hlsl; ipureintro; exact hx
    wp_apply wp_float64_mul as %f1 _
    wp_apply wp_float64_mul as %f2 _
    try wp_auto
    wp_apply wp_ArbitraryInt as %x' _
    try wp_auto
    wp_if_destruct
    · try wp_auto
      wp_for_post
      iframe
      iexists (iv + W64 1), (x' * W64 1), x
      iframe
      ipureintro; word
    · try wp_auto
      wp_for_post
      iframe
      iexists (iv + W64 1), ml, x
      iframe
      ipureintro; word
  · simp only [hlt, _root_.decide_false]
    cleanup_bool_decide
    try rw [if_pos (show True from trivial)]
    try rw [if_neg (show ¬ (decide ((#false : val) = #true) = true) by simp [Perennial.false_neq_true])]
    try simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto_lc 2
    -- the clients' acceptor
    wp_apply wp_fork $$ [Hserve]
    · wp_method_call
      wp_auto
      wp_apply wp_wait rr γ γc γm γw N me a $$ [$HisR $Hserve]
      · iPkgInit
      itrivial
    -- the loop's invariant
    ipersist Fcs
    iapply fupd_wp
    imod start_bag (fun _ : swift.CommandId => iprop(True)) (ChanState.Buffered []) dch γdc
      (by trivial) $$ [$Hdch] [Hdown] with #Hdbag
    · iexact Hdown
    imod start_bag (fun _ : swift.CommandId => iprop(True)) (ChanState.Buffered []) rch γrc
      (by trivial) $$ [$Hrchan] [Hrown] with #Hrbag
    · iexact Hrown
    imodintro
    have hbags : swift.csBags γ γc γm csv n ⊢ swift.csBags γ γc γm { csv with maxLatency' := ml } n := by
      unfold swift.csBags; exact .rfl
    ihave #Hbags' := hbags $$ Hbags
    ihave Hlp : swift.runLoopPre rp γ γc γm γl N k me fr l pl γw { csv with maxLatency' := ml } n $$
      [Hstart Fballot Fcballot Fstatus FFQ FcmdDescs Hv1 Hrd1 Hγd Hdel Frepchan Fkeys Hkm Fhlog Hhm
        FcntL Fseqnum FpendingHashUpds Hpm FhistoryL Hhsl FexecL FexecLog HdescPool FroutineCount
        FrecStart FnewLeaderAckNs FnlBal Fproposes Hpropm Fhandled FlastSync FacceptL Faccepted Haccm
        Fwaiting Hwaitm Frechecks HPPO Hpp HState HDreply HpDeps]
    · iunfold swift.runLoopPre
      iexists rr, s, b, rc, qs, γs, γrl, γd, γdc1, γdl, dm1, dch, rch, γdc, γrc, hsl, km, hm, pm,
        propm, accm, waitm, sam, sq, fq, d
      iframe #
      iframe
      isplitr
      · ipureintro; exact Hids
      isplitr
      · ipureintro; exact Hdb
      isplitr
      · ipureintro; exact Hcs.1
      ipureintro; exact Hpp'
    ihave #Hswpkg : isPkgInit (PROP := IProp netDistGF)
      pkg_id.github_com.imdea_software.swiftpaxos.swift $$ []
    · iPkgInit
    iapply fupd_wp
    imod H.init rp γ γc γm γl N k me fr l pl γw _ n $$ [$Hswpkg $Hlp] with ⟨%x, HI⟩
    imodintro
    have ar := H.arms rp γ γc γm x
    ihave #Hrcvr2 := Hrcvr
    iunfold swift.rcvrRes at Hrcvr2
    icases Hrcvr2 with ⟨%rr', %N', %fr', %l', %me', %dm', %qs', %rcc, %γrcc, %γdl', #FReplica',
      -, -, -, -, -, -, -, -, -, #Frecover, #Hrecbag, -⟩
    ihave %Hrr : ⌜rr' = rr⌝ $$ [FReplica FReplica']
    · iapply typedPointsto_agree_wand _ _ _ _ _ $$ FReplica' FReplica
    subst Hrr
    ihave #HisR2 := HisR
    iunfold replica.isReplica at HisR2
    icases HisR2 with ⟨%lg, %cfgp, %tbl', %pc, %fr'', %nid', %ents', %γpc, %pwsl, %alsl, %latsl,
      %pws, %cwm, -, -, -, -, -, -, -, -, -, #RProposeChan, #Hpbag, -⟩
    ihave #Hbags2 := Hbags
    iunfold swift.csBags at Hbags2
    icases Hbags2 with ⟨#Bfa, -, -, #Bls, #Backs, #Bopt, -, #Bnl, -, #Bsync, -⟩
    ihave #Fcs2 := Fcs
    iStructNamedPrefix Fcs2 "CS"
    ihave HL : ("HI" ∷ I rp γ γc γm x ∗ "Hlc1" ∷ £ 1 ∗ "Hlc2" ∷ £ 1 : IProp netDistGF) $$ [HI Hlc1 Hlc2]
    · iframe
    wp_for HL
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- recover
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Hrecbag
      inext
      iintro %v #Hv
      wp_auto_lc 2
      wp_apply ar.recBal v $$ [$HI $Hv] as %b0 %ok ⟨HI, Hob⟩
      try wp_auto
      wp_if_destruct
      · runPost
        iframe
        unfold named
        iframe
      · try wp_auto
        ipersist «$r0»
        wp_method_call
        try wp_auto
        wp_apply wp_senda rr' γ γc γm γw N me γs s
          (interface.mkOk (go.GoType.PointerType swift.MNewLeader.ty) #«$r0_ptr»)
          (.newLeader me b0) csv.newLeaderRPC'
          iprop(typedPointsto «$r0_ptr» (swift.MNewLeader.mk me b0) DFrac.discard)
          $$ [$HisR $Hsbag]
        · unfold replica.toSend
          isplitl
          · isplitr
            · iapply (hmnl «$r0_ptr» me b0 trivial)
            isplitr
            · iexact «$r0»
            isplitr
            · simp only [sp.msgOk]
              iexists N, fr, l
              iframe Hcfg
              ipureintro; exact ⟨Hids.2.2.1, Hids.1⟩
            isplitr
            · unfold replica.freeOk; ileft; ipureintro; rfl
            ipureintro
            refine ⟨trivial, ?_⟩
            rw [Hcs.1.2.2.2.2.2.2.2.1]; rfl
          ipureintro; trivial
        try wp_auto
        ihave #Hob' := Hob $$ []
        · ipureintro; first | trivial | rfl | simp_all
        wp_apply ar.reinit b0 $$ [$HI $Hob'] as HI
        try wp_auto
        wp_apply ar.newLeader «$r0_ptr» me b0 $$ [$HI $«$r0»] as HI
        · simp only [sp.msgOk]
          iexists N, fr, l
          iframe Hcfg
          ipureintro; exact ⟨Hids.2.2.1, Hids.1⟩
        runPost
        iframe
        unfold named
        iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- deliver
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Hdbag
      inext
      iintro %v -
      wp_auto_lc 2
      wp_apply ar.getDesc v go!"deliver" $$ [$HI] as %d HI
      runPost
      iframe
      unfold named
      iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- recheck
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Hrbag
      inext
      iintro %v -
      wp_auto_lc 2
      wp_apply ar.getDesc v go!"recheck" $$ [$HI] as %d HI
      runPost
      iframe
      unfold named
      iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- propose
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Hpbag
      inext
      iintro %v Hv
      wp_auto_lc 2
      wp_apply ar.propose v $$ [$HI $Hv] as HI
      runPost
      iframe
      unfold named
      iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- fastAck
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Bfa
      inext
      iintro %v Hv
      iunfold sp.chanMsgP at Hv
      icases Hv with ⟨%m, Hr, #Hok, %Hc⟩
      cases m <;> simp [sp.Msg.code, sp.rpcTable] at Hc
      rename_i f0
      iunfold swift.msgRep at Hr
      iunfold swift.msgRepM at Hr
      icases Hr with ⟨%l0, %fa, %Hv, Hl, #Hrep⟩
      subst Hv
      ipersist Hl
      ihave #Hl2 := Hl
      iStructNamedPrefix Hl2 "FA"
      ihave #Hw : swift.runAckW γ γc γm f0 $$ []
      · iunfold swift.runAckW; ileft; iunfold sp.msgOk at Hok; iexact Hok
      wp_auto_lc 2
      wp_apply ar.ackHash l0 fa f0 $$ [$HI $Hl $Hrep $Hw] as HI
      wp_apply ar.leader $$ [$HI] as %ld HI
      try wp_auto
      wp_apply ar.fastDesc l0 fa f0 $$ [$HI $Hl $Hrep $Hw] as %d HI
      runPost
      iframe
      unfold named
      iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- lightSlowAck
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Bls
      inext
      iintro %v Hv
      iunfold sp.chanMsgP at Hv
      icases Hv with ⟨%m, Hr, #Hok, %Hc⟩
      cases m <;> simp [sp.Msg.code, sp.rpcTable] at Hc
      rename_i s0
      iunfold swift.msgRep at Hr
      iunfold swift.msgRepM at Hr
      icases Hr with ⟨%l0, %sa, %Hv, Hl, %Hsa⟩
      subst Hv
      ipersist Hl
      ihave #Hl2 := Hl
      iStructNamedPrefix Hl2 "SA"
      wp_auto_lc 2
      wp_apply ar.slowDesc l0 sa s0 $$ [$HI $Hl $Hok] as %d HI
      · ipureintro; exact Hsa
      runPost
      iframe
      unfold named
      iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- acks
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Backs
      inext
      iintro %v Hv
      iunfold sp.chanMsgP at Hv
      icases Hv with ⟨%m, Hr, #Hok, %Hc⟩
      cases m <;> simp [sp.Msg.code, sp.rpcTable] at Hc
      rename_i fs0 ss0
      iunfold swift.msgRep at Hr
      iunfold swift.msgRepM at Hr
      icases Hr with ⟨%l0, %fsl, %ssl, %fps, %sps, %Hv, Hl, Hfsl, Hssl, #Hfr⟩
      obtain ⟨Hv, Hfs, Hss, Hsr⟩ := Hv
      subst Hv Hfs Hss
      iunfold sp.msgOk at Hok
      icases Hok with ⟨#Hfok, #Hsok⟩
      wp_auto_lc 2
      ihave HL2 : (∃ iv : w64, "i" ∷ i_ptr ↦ iv ∗ "HI" ∷ I rp γ γc γm x ∗
          "Hfsl" ∷ fsl ↦* fps.map Prod.fst ∗ "%Hi" ∷ ⌜0 ≤ sint.Z iv⌝ : IProp netDistGF)
          $$ [i HI Hfsl]
      · iexists (W64 0); iframe; ipureintro; decide
      wp_for HL2
      ihave %Hll := ownSlice_len _ _ _ $$ Hfsl
      by_cases hlt : sint.Z iv < sint.Z fsl.len
      · simp only [hlt, _root_.decide_true]
        cleanup_bool_decide
        try rw [if_pos (show True from trivial)]
        try rw [if_neg (show ¬ (decide ((#false : val) = #true) = true) by simp [Perennial.false_neq_true])]
        wp_auto
        have hi0 : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z fsl.len := ⟨Hi, hlt⟩
        try isimp only [hi0, _root_.and_self, ↓reduceIte]
        obtain ⟨p0, hp0⟩ : ∃ p0, fps[(sint.Z iv).toNat]? = some p0 := by
          have h1 := Hll.1
          have e := swift.snat_eq fsl.len Hll.2
          simp only [List.length_map] at h1
          exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
        wp_apply wp_load_slice_index fsl (sint.Z iv) (fps.map Prod.fst) _ p0.1 Hi $$ [Hfsl] as Hfsl
        · iframe Hfsl; ipureintro; simp [hp0]
        ihave #Hrep := BigSepL.bigSepL_lookup hp0 $$ Hfr
        ihave #Hw0 := BigSepL.bigSepL_lookup (by simp [hp0] : (fps.map Prod.snd)[(sint.Z iv).toNat]? = some p0.2) $$ Hfok
        ihave #Hw : swift.runAckW γ γc γm p0.2 $$ []
        · iunfold swift.runAckW; ileft; iexact Hw0
        try wp_auto
        ipersist f
        ihave #f2 := f
        iStructNamedPrefix f2 "F"
        wp_apply ar.ackHash f_ptr p0.1 p0.2 $$ [$HI $f $Hrep $Hw] as HI
        try wp_auto
        wp_apply wp_copy _ f_ptr p0.1 $$ [$Hpool $f] as %l1 Hl1
        ipersist Hl1
        try wp_auto
        wp_apply ar.leader $$ [$HI] as %ld HI
        try wp_auto
        wp_apply ar.fastDesc l1 p0.1 p0.2 $$ [$HI $Hl1 $Hrep $Hw] as %d HI
        runPost
        iframe
        iexists (iv + W64 1)
        iframe
        ipureintro; word
      · simp only [hlt, _root_.decide_false]
        cleanup_bool_decide
        try rw [if_pos (show True from trivial)]
        try rw [if_neg (show ¬ (decide ((#false : val) = #true) = true) by simp [Perennial.false_neq_true])]
        try simp only [Bool.false_eq_true, ↓reduceIte]
        try simp only [_root_.decide_true, ↓reduceIte, if_true, ite_true, eq_self_iff_true]
        wp_auto
        ihave HL3 : (∃ (iv : w64) (sv : swift.MLightSlowAck), "i" ∷ i_ptr ↦ iv ∗ "HI" ∷ I rp γ γc γm x ∗
            "s" ∷ s_ptr ↦ sv ∗ "Hssl" ∷ ssl ↦* sps.map Prod.fst ∗ "%Hi" ∷ ⌜0 ≤ sint.Z iv⌝ : IProp netDistGF)
            $$ [i HI s Hssl]
        · iexists (W64 0), _; iframe; ipureintro; decide
        wp_for HL3
        ihave %Hll2 := ownSlice_len _ _ _ $$ Hssl
        by_cases hlt2 : sint.Z iv < sint.Z ssl.len
        · simp only [hlt2, _root_.decide_true]
          cleanup_bool_decide
          try rw [if_pos (show True from trivial)]
          try rw [if_neg (show ¬ (decide ((#false : val) = #true) = true) by simp [Perennial.false_neq_true])]
          try simp only [ite_true, ↓reduceIte]
          wp_auto
          have hi0 : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z ssl.len := ⟨Hi, hlt2⟩
          try isimp only [hi0, _root_.and_self, ↓reduceIte]
          obtain ⟨q0, hq0⟩ : ∃ q0, sps[(sint.Z iv).toNat]? = some q0 := by
            have h1 := Hll2.1
            have e := swift.snat_eq ssl.len Hll2.2
            simp only [List.length_map] at h1
            exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
          wp_apply wp_load_slice_index ssl (sint.Z iv) (sps.map Prod.fst) _ q0.1 Hi $$ [Hssl] as Hssl
          · iframe Hssl; ipureintro; simp [hq0]
          ihave #Hsw0 := BigSepL.bigSepL_lookup (by simp [hq0] : (sps.map Prod.snd)[(sint.Z iv).toNat]? = some q0.2) $$ Hsok
          have hsr := Hsr q0 (List.mem_of_getElem? hq0)
          try wp_auto
          ipersist ls
          wp_apply ar.slowDesc ls_ptr q0.1 q0.2 $$ [$HI $ls] as %d HI
          · isplitr
            · ipureintro; exact hsr
            simp only [sp.msgOk]
            iexact Hsw0
          runPost
          iframe
          iexists (iv + W64 1), q0.1
          iframe
          ipureintro; word
        · simp only [hlt2, _root_.decide_false]
          cleanup_bool_decide
          try rw [if_pos (show True from trivial)]
          try rw [if_neg (show ¬ (decide ((#false : val) = #true) = true) by simp [Perennial.false_neq_true])]
          try simp only [Bool.false_eq_true, ↓reduceIte]
          try simp only [_root_.decide_true, ↓reduceIte, if_true, ite_true, eq_self_iff_true]
          try wp_auto
          runPost
          iframe
          unfold named
          iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- optAcks
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Bopt
      inext
      iintro %v Hv
      iunfold sp.chanMsgP at Hv
      icases Hv with ⟨%m, Hr, #Hok, %Hc⟩
      cases m <;> simp [sp.Msg.code, sp.rpcTable] at Hc
      rename_i r0 b0 al0
      iunfold swift.msgRep at Hr
      iunfold swift.msgRepM at Hr
      icases Hr with ⟨%l0, %asl, %ps, %Hv, Hl, Hasl, #Har⟩
      obtain ⟨Hv, Hps⟩ := Hv
      subst Hv Hps
      iunfold sp.msgOk at Hok
      icases Hok with ⟨%Hwire, #Haok, #Hnl⟩
      ipersist Hl
      ihave #Hl2 := Hl
      iStructNamedPrefix Hl2 "OA"
      wp_auto_lc 2
      ihave HL4 : (∃ (iv : w64) (av : swift.Ack), "i" ∷ i_ptr ↦ iv ∗ "HI" ∷ I rp γ γc γm x ∗
          "ack" ∷ ack_ptr ↦ av ∗ "Hasl" ∷ asl ↦* ps.map Prod.fst ∗ "%Hi" ∷ ⌜0 ≤ sint.Z iv⌝ : IProp netDistGF)
          $$ [i HI ack Hasl]
      · iexists (W64 0), _; iframe; ipureintro; decide
      wp_for HL4
      ihave %Hll := ownSlice_len _ _ _ $$ Hasl
      by_cases hlt : sint.Z iv < sint.Z asl.len
      · simp only [hlt, _root_.decide_true]
        cleanup_bool_decide
        try rw [if_pos (show True from trivial)]
        try rw [if_neg (show ¬ (decide ((#false : val) = #true) = true) by simp [Perennial.false_neq_true])]
        try simp only [ite_true, ↓reduceIte]
        wp_auto
        have hi0 : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z asl.len := ⟨Hi, hlt⟩
        try isimp only [hi0, _root_.and_self, ↓reduceIte]
        obtain ⟨p0, hp0⟩ : ∃ p0, ps[(sint.Z iv).toNat]? = some p0 := by
          have h1 := Hll.1
          have e := swift.snat_eq asl.len Hll.2
          simp only [List.length_map] at h1
          exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
        wp_apply wp_load_slice_index asl (sint.Z iv) (ps.map Prod.fst) _ p0.1 Hi $$ [Hasl] as Hasl
        · iframe Hasl; ipureintro; simp [hp0]
        ihave #Hrep := BigSepL.bigSepL_lookup hp0 $$ Har
        ihave #Hao := BigSepL.bigSepL_lookup (by simp [hp0] : (ps.map Prod.snd)[(sint.Z iv).toNat]? = some p0.2) $$ Haok
        ihave #Hrep2 := Hrep
        iunfold swift.ackRepr at Hrep2
        icases Hrep2 with ⟨%Har0, #Hadep, #Hacs⟩
        try wp_auto
        wp_apply wp_new _ $$ [$Hpool] as %fl ⟨%fa0, Hfl⟩
        try wp_auto
        wp_apply swift.IsNilDepOfCmdId.wp $$ [$Hadep]
        try wp_auto
        isimp only at Hfl
        iintro -
        have e := swift.nilDep_iff p0.2.dep p0.1.CmdId' p0.2.id Har0.1
        ihave #Hw := swift.runAckW_of_opt γ γc γm r0 b0 (ps.map Prod.snd) p0.2
          (List.mem_map.2 ⟨p0, List.mem_of_getElem? hp0, rfl⟩) $$ [$Hao $Hnl]
        · ipureintro; exact Hwire
        by_cases hd : p0.2.dep = [p0.2.id]
        · rw [decide_eq_true (e.2 hd)]
          wp_auto
          isimp only at Hfl
          ipersist Hfl
          ihave #Hfl2 := Hfl
          iStructNamedPrefix Hfl2 "NF"
          ihave #Hrep' := swift.fastAckRepr_of_opt p0.1 p0.2 r0 b0 slice.nil (by simp [hd]) $$ Hrep
          wp_apply ar.ackHash fl _ (swift.fastOfAck r0 b0 p0.2) $$ [$HI $Hfl $Hrep' $Hw] as HI
          try wp_auto
          wp_apply ar.leader $$ [$HI] as %ld HI
          try wp_auto
          wp_apply ar.fastDesc fl _ _ $$ [$HI $Hfl $Hrep' $Hw] as %d HI
          runPost
          iframe
          iexists (iv + W64 1), p0.1
          iframe
          ipureintro; word
        · rw [decide_eq_false (fun h => hd (e.1 h))]
          wp_auto
          isimp only at Hfl
          ipersist Hfl
          ihave #Hfl2 := Hfl
          iStructNamedPrefix Hfl2 "NF"
          ihave #Hrep' := swift.fastAckRepr_of_opt p0.1 p0.2 r0 b0 p0.1.Dep' (by simp [hd]) $$ Hrep
          wp_apply ar.ackHash fl _ (swift.fastOfAck r0 b0 p0.2) $$ [$HI $Hfl $Hrep' $Hw] as HI
          try wp_auto
          wp_apply ar.leader $$ [$HI] as %ld HI
          try wp_auto
          wp_apply ar.fastDesc fl _ _ $$ [$HI $Hfl $Hrep' $Hw] as %d HI
          runPost
          iframe
          iexists (iv + W64 1), p0.1
          iframe
          ipureintro; word
      · simp only [hlt, _root_.decide_false]
        cleanup_bool_decide
        try rw [if_pos (show True from trivial)]
        try rw [if_neg (show ¬ (decide ((#false : val) = #true) = true) by simp [Perennial.false_neq_true])]
        try simp only [Bool.false_eq_true, ↓reduceIte]
        try simp only [_root_.decide_true, ↓reduceIte, if_true, ite_true, eq_self_iff_true]
        try wp_auto
        runPost
        iframe
        unfold named
        iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- newLeader
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Bnl
      inext
      iintro %v Hv
      iunfold sp.chanMsgP at Hv
      icases Hv with ⟨%m, Hr, #Hok, %Hc⟩
      cases m <;> simp [sp.Msg.code, sp.rpcTable] at Hc
      rename_i r0 b0
      iunfold swift.msgRep at Hr
      iunfold swift.msgRepM at Hr
      icases Hr with ⟨%l0, %Hv, Hl⟩
      subst Hv
      wp_auto_lc 2
      ipersist Hl
      wp_apply ar.newLeader l0 r0 b0 $$ [$HI $Hl $Hok] as HI
      runPost
      iframe
      unfold named
      iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- sync
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Bsync
      inext
      iintro %v Hv
      iunfold sp.chanMsgP at Hv
      icases Hv with ⟨%m, Hr, #Hok, %Hc⟩
      cases m <;> simp [sp.Msg.code, sp.rpcTable] at Hc
      rename_i m0 bs0
      iunfold swift.msgRep at Hr
      iunfold swift.msgRepM at Hr
      icases Hr with ⟨%l0, %x0, %Hv, Hl⟩
      obtain ⟨Hv, Hx⟩ := Hv
      subst Hv
      wp_auto_lc 2
      wp_apply ar.sync l0 m0 bs0 $$ [$HI Hl] as HI
      · iframe Hok
        iunfold swift.msgRepM
        iexists l0, x0
        iframe
        ipureintro; exact ⟨rfl, Hx⟩
      runPost
      iframe
      unfold named
      iframe
    iapply BigAndL.bigAndL_nil.2
    itrivial

/-- `run.wp_proof` over `RunLoopOk`. -/
theorem swift.Replica.run.wp_proof' (H : swift.RunLoopOk (hG := hG))
    (htab : swift.tableAllocH)
    (wp_conn : replica.Replica.ConnectToPeers.spec (hG := hG))
    (wp_closest : replica.Replica.ComputeClosestPeers.spec (hG := hG))
    (wp_wait : replica.Replica.WaitForClientConnections.spec (hG := hG))
    (wp_senda : replica.Sender.SendToAll.spec (hG := hG))
    (hmnl : swift.MNewLeader.marshalH (hG := hG))
    (wp_new : swift.newFastAck.specP (hG := hG))
    (wp_copy : swift.copyFastAck.specP (hG := hG)) :
    swift.Replica.run.specI (hG := hG) := by
  obtain ⟨X, I, H⟩ := H
  exact swift.Replica.run.wp_proof X I H htab wp_conn wp_closest wp_wait wp_senda hmnl wp_new wp_copy

end proof

end Perennial.github_com.imdea_software.swiftpaxos
