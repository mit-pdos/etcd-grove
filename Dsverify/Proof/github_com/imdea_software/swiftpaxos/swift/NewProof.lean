/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/NewProof.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`swift.New`'s body (swift/swift.go:155): `swift.New.wp_proof` over its callees' specs
(Proof/swift/NewSpecs.lean; the replica group's `replica.New`, `NewSender`, the quorum
system's; the concurrent map's `New`) and the run loop's spec `swift.Replica.run.specI` (a
hypothesis: the run loop's proof is notes/prove-swift.md §10's next step).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.LeaderM
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Println
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Fatal

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [github_com.orcaman.concurrent_map.Assumptions]
  [sync.Assumptions] [examples.swiftnet.Assumptions] [dlog.Assumptions] [hook.Assumptions]
  [time.Assumptions] [config.Assumptions] [net.rpc.Assumptions]

set_option goose.wp.extras true

/-- The embedded replica's `Println` (its quiet logger's). -/
theorem swift.wp_replicaPrintln (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG))
    (r lg : Loc) (sl : GoSlice) :
    {{ replica.fld r go!"Logger" ↦□ lg ∗ dlog.quiet (GF := netDistGF) lg }}
      (App (Val #(methods (go.GoType.PointerType replica.Replica.ty) go!"Println" #r)) (Val #sl))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hlg, #Hq⟩
  wp_auto
  wp_apply wp_Println $$ [$Hq]
  wp_end

/-- A replica node's index in `replicaAddrs` (the addresses are distinct). -/
theorem swift.replicaAddrs_idxOf (k : Nat) (a : GoString) (h : replicaAddrs[k]? = some a) :
    replicaAddrs.idxOf? a = some k := by
  rcases k with _ | _ | _ | _ | _ | k <;> simp [replicaAddrs] at h <;> subst h <;> decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem swift.New.wp_proof (facts : swift.SrvPkgFacts)
    (wp_RNew : replica.New.spec (hG := hG))
    (wp_CNew : github_com.orcaman.concurrent_map.NewV.spec (GF := netDistGF))
    (wp_maj : replica.NewMajorityOf.spec) (wp_tq : replica.NewThreeQuartersOf.spec)
    (wp_sender : replica.NewSender.spec (hG := hG))
    (wp_batcher : swift.NewBatcher.specI (hG := hG))
    (wp_rc : swift.NewReplyChan.specI (hG := hG))
    (wp_qs : replica.NewQuorumSystem.spec) (wp_ballotAt : replica.QuorumSystem.BallotAt.spec)
    (wp_AQ : replica.QuorumSystem.AQ.spec)
    (wp_initCs : swift.initCs.specR (hG := hG))
    (wp_Leader : replica.Leader.spec)
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG))
    (wp_Fatal : dlog.Logger.Fatal.spec (GF := netDistGF) (hG := hG))
    (wp_hook : hook.HookUser1.specI (hG := hG))
    (wp_run : swift.Replica.run.specI (hG := hG))
    (rcvr : swift.rcvr.spec (hG := hG)) :
    swift.New.spec (hG := hG) := by
  intro al rid addrs l N k fr pl f cfgp lg γ γc γm γl a ip
  wp_start as ⟨#Hinv, #Hcfg, #Haddrs, %Hpure, Hstart, #Hip, #Hlis, Hprotos, #Hconf, #Hlg, %Hplf,
    ⟨%d, %v0, %n0, %Hdb, Hmax, Hpool, Hshard⟩, #Hgcs, #Hrcs, #Hng⟩
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_auto
  ipersist Hshard
  ihave #Hrpkg : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica $$ []
  · iPkgInit
  ihave #Hdpkg : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica.defs $$ []
  · iPkgInit
  ihave ⟨#Hnqf, #H34⟩ := facts.rep $$ Hrpkg
  ihave #Hlat := facts.dfs $$ Hdpkg
  ihave ⟨#Hmem, %HlN⟩ := sp.cfg_memIs _ _ _ $$ Hcfg
  ihave ⟨%cf, #Hcf, %Hcfn⟩ := sp.cfg_confIs _ _ _ $$ Hcfg
  ihave %Hvalid := confIs_valid _ _ $$ Hcf
  obtain ⟨hka, hla, hip⟩ := Hpure
  have hN : N = 3 ∨ N = 5 := by rw [← Hcfn.1]; exact Hvalid.1
  subst HlN
  have hrid1 : uint.nat rid < l.length := by
    rcases Nat.lt_or_ge (uint.nat rid) l.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hla; cases hla
  have hrid : 0 ≤ sint.Z rid ∧ sint.Z rid < l.length ∧ l.length ≤ 7 := by
    have hl5 : l.length ≤ 5 := by omega
    refine ⟨?_, ?_, by omega⟩ <;> word
  wp_apply wp_RNew al rid f addrs l false true false cfgp lg γ $$ [$Haddrs $Hlat] as %rr Hrr
  · ipureintro; exact hrid
  iapply fupd_wp
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Loc) (V := sp.CmdId) with ⟨%γd, Hγd⟩
  imodintro
  wp_apply wp_CNew (W64 32768) (swift.descR γd) $$ [$Hshard] as %dm1 ⟨%γdc1, #Hdm1, Hv1, Hrd1⟩
  · ipureintro; decide
  wp_apply wp_CNew (W64 32768) swift.deliveredR $$ [$Hshard] as %dm2 ⟨%γdl, #Hdm2, Hv2, Hrd2⟩
  · ipureintro; decide
  wp_apply (wp_map_make1 (K := w64) (V := GoInterface)) as %km Hkm
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %hm Hhm
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Loc)) as %pm Hpm
  wp_apply (wp_slice_make2 (V := swift.commandStaticDesc) (W64 10010001)) as %hsl ⟨Hhsl, Hhcap⟩
  · ipureintro; decide
  wp_apply chan.wp_make2 (V := swift.CommandId) (W64 2000000) as %dch %γdc ⟨#Hdch, %Hdcap, Hdown⟩
  · ipureintro; decide
  wp_apply chan.wp_make2 (V := w32) (W64 8) as %rch %γrch ⟨#Hrch, %Hrcap, Hrown⟩
  · ipureintro; decide
  wp_func_lits
  wp_auto
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Loc)) as %propm Hpropm
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := swift.Dep)) as %pdm Hpdm
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Unit)) as %accm Haccm
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := GoSlice)) as %waitm Hwaitm
  wp_apply chan.wp_make2 (V := swift.CommandId) (W64 2000000) as %kch %γkc ⟨#Hkch, %Hkcap, Hkown⟩
  · ipureintro; decide
  wp_apply (wp_map_make1 (K := GoString) (V := Unit)) as %sam Hsam
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hrnn⟩
  iStructNamedPrefix «$r0» "F"
  wp_for
  iunfold replica.created at Hrr
  icases Hrr with ⟨%rv, %γpc, %pps, Hrv, %Hrv, HPeers, HPR, HPW, HCW, HAlive, HPPO, %Hpps,
    HEwma, HLat, HState, HRPC, HPC⟩
  obtain ⟨hlg, hN', hId, hAl, hPA, hCf, hSd, hTh, hEx, hLR, hDt, hM, hLi, hPC⟩ := Hrv
  iStructNamedPrefix Hrv "R"
  isimp only [hSd] at RShutdown
  isimp only [hN'] at RN
  isimp only [hId] at RId
  isimp only [hlg] at RLogger
  ipersist RShutdown
  ipersist RN
  ipersist RId
  ipersist RLogger
  ipersist FReplica
  have hN62 : l.length < 2 ^ 62 := by omega
  wp_auto
  wp_apply wp_maj l.length
  · ipureintro; exact hN62
  wp_apply wp_tq l.length
  · ipureintro; omega
  wp_apply wp_sender rr γ γc γm l.length $$ [$RShutdown] as %s ⟨%γs, #Hs⟩
  ipersist Fsender
  ipersist Hpool
  wp_apply wp_batcher «$r0_ptr» rr γ γc γm $$ [$FReplica $RShutdown $Hpool] as %b #Hb
  · iintro !> %x %Φ' HΦ'
    wp_pure
    wp_auto
    iexact HΦ'
  ipersist Fbatcher
  ipersist Fhistory
  iapply fupd_wp
  imod swift.cell_alloc swift.replyCellN ⊤ (swift.replyCellRes «$r0_ptr» (W32 0)) with ⟨%γrl, #Hcell, Hfill, Hclaim⟩
  imodintro
  ihave %Hhl := ownSlice_len _ _ _ $$ Hhsl
  wp_apply wp_rc «$r0_ptr» rr hsl γ γc γm γrl (W32 0) $$ [$FReplica $RShutdown $Fhistory $Hcell $Hclaim] as %rc Hrc
  · ipureintro
    simp only [List.length_replicate] at Hhl
    word
  iunfold config.plain at Hconf
  icases Hconf with ⟨%cv, %pi, #Hcv, #Hpi, %Hcvp⟩
  obtain ⟨hcf0, hpx0, hq0, hld0, hor0, hpi1, hpi2, hpi3⟩ := Hcvp
  ihave #Hcv' := Hcv
  iStructNamedPrefix Hcv' "C"
  rw [hq0]
  wp_auto
  have hdiv : BitVec.sdiv (W64 (l.length : Int)) (W64 2) + W64 1 = W64 ((l.length : Int) / 2 + 1) := by
    rcases hN with h | h <;> rw [h] <;> decide
  rw [hdiv]
  wp_apply wp_qs rr DFrac.discard l.length go!"Quorum file is not provided" $$ [$Hnqf $RN] as %qs ⟨-, #Hqs⟩
  · ipureintro; omega
  ipersist Fqs
  wp_apply wp_ballotAt qs l.length (W64 0) $$ [$Hqs]
  · ipureintro; decide
  ihave #H34' := H34
  iunfold errors.newVar at H34'
  icases H34' with ⟨%x34, #H34g, -⟩
  wp_auto
  wp_apply wp_AQ qs l.length (W32 0) $$ [$Hqs] as %fq #Hfq
  · ipureintro; decide
  -- round 23 (D18 G2): `FQ = qs.AQ(0)` is a fast quorum of ballot 0 (`fqOk`, for the epoch)
  ihave #HFQok : swift.fqOk (interface.mkOk replica.Quorum.ty #fq) l.length 0 $$ [Hfq]
  · iapply swift.aq_fqOk l.length 0 (by omega) fq; iexact Hfq
  ipersist RRPC
  ihave Htbl : rpc.tblOwn rv.RPC' (W8 9) ∅ $$ [HRPC]
  · iunfold rpc.tblOwn; iunfold rpc.isTable at HRPC; iexact HRPC
  wp_apply wp_initCs $$ [$Fcs $Htbl] as ⟨%csv, %M, Fcs, Htbl, Hchans, %Hcs⟩
  have hNr : 1 ≤ l.length ∧ l.length ≤ 7 := by omega
  wp_apply (swift.Replica.wp_leader wp_Leader «$r0_ptr» rr _ _ l.length hNr) $$ [$Fballot $FReplica $RN] as Fballot
  ipersist RLogger
  ihave #Hlg' := Hlg
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go.string #(go!"the leader is:"),
      interface.mkOk go.int32 #(BitVec.srem (W32 0) (W32 (sint.Z (W64 (l.length : Int))))),
      interface.mkOk go.string #(go!"ballot is:"), interface.mkOk go.int32 #(W32 0)]
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨-, -⟩
  wp_auto
  wp_method_call
  wp_auto
  wp_apply swift.wp_replicaPrintln wp_Println $$ [$RLogger $Hlg]
  wp_apply wp_hook
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go.string #(go!"SQ:"),
      interface.mkOk replica.Majority.ty #(W64 ((l.length : Int) / 2 + 1))]
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨-, -⟩
  wp_auto
  wp_method_call
  wp_auto
  wp_apply swift.wp_replicaPrintln wp_Println $$ [$RLogger $Hlg]
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go.string #(go!"FQ:"), interface.mkOk replica.Quorum.ty #fq]
  isplitr
  · ipureintro; rfl
  iintro %sl3 ⟨-, -⟩
  wp_auto
  wp_method_call
  wp_auto
  wp_apply swift.wp_replicaPrintln wp_Println $$ [$RLogger $Hlg]
  -- the shared state: `ballot`'s quarters (ballotL, the reply goroutine), `recover`, `delivered`
  icases (typedPointsto_half_split _ _ _).1 $$ Fballot with ⟨Fballot, Fb2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ Fb2 with ⟨Fb3, Fb4⟩
  iapply fupd_wp
  imod sync.init_Mutex (swift.ballotLInv «$r0_ptr») ⊤ _ $$ [FballotL] [Fb3] with #HbL
  · iexact FballotL
  · inext; iunfold swift.ballotLInv; iexists _; iframe Fb3; ipureintro; decide
  imod swift.cell_fill swift.replyCellN ⊤ (by simp) γrl (swift.replyCellRes «$r0_ptr» (W32 0))
    $$ [$Hcell $Hfill Fb4 FhistorySize] with #Hfilled
  · unfold swift.replyCellRes swift.replyRes; iframe Fb4; iexists _; iframe FhistorySize
    ipureintro; decide
  imod start_bag (swift.recoverOk «$r0_ptr») (ChanState.Buffered []) rch γrch (by trivial)
    $$ [$Hrch] [Hrown] with #Hrbag
  · iExactEq Hrown; simp
  -- `deliveredAny`'s invariant (fork change P2-A; replaces the readers' borrowing right)
  imod inv_alloc swift.anyN ⊤ (∃ b : Bool,
      sync.atomic.ownBool (swift.fld «$r0_ptr» go!"deliveredAny") (DFrac.own 1) b)
    $$ [FdeliveredAny] with #HanyI
  · inext; iexists false
    rw [sync.atomic.ownBool_unseal]; unfold sync.atomic.ownBoolDef
    iExactEq FdeliveredAny; rfl
  imodintro
  ihave #Hapkg : isPkgInit (PROP := IProp netDistGF) pkg_id.sync.atomic $$ []
  · iPkgInit
  ipersist Fdelivered
  ipersist Frecover
  ihave #Hres : swift.rcvrRes «$r0_ptr» γc γm $$ []
  · iunfold swift.rcvrRes
    iexists rr, l.length, fr, l, (W32 (sint.Z rid)), dm2, qs, rch, γrch, γdl
    iframe FReplica RN RId Hcfg Fdelivered Hdm2 Fqs Hqs Frecover Hrbag HbL
    isplitr
    · ipureintro; refine ⟨by omega, by omega, ?_, ?_⟩ <;> word
    iunfold swift.anyInv
    iframe Hapkg HanyI
  -- the run loop's share: the read-only fields and globals persisted, the pool
  iapply fupd_wp
  -- round 21 (sv-swb): the descriptors' share map (ShInv.lean), then the pool over it
  imod swift.shInv_alloc ⊤ with ⟨%γsh, #Hsh⟩
  imod sync.init_Pool (swift.fld «$r0_ptr» go!"descPool")
      { noCopy' := zeroValDef, local' := null, localSize' := 0, victim' := null, victimSize' := 0,
        New' := _ } iprop(True) (swift.descPoolP (swift.descDFA γsh)) ⊤ rfl $$ [FdescPool] with #Hpool'
  · isplitl [FdescPool]
    · iexact FdescPool
    unfold sync.newSpec
    iright
    wp_start
    wp_auto
    wp_alloc dl as Hdl
    wp_auto
    iapply HΦ
    isplitr []
    · unfold swift.descPoolP
      iexists _
      isplitr
      · ipureintro; rfl
      iright
      iexact Hdl
    itrivial
  ihave #HdescOk : swift.descPoolOk «$r0_ptr» $$ []
  · iunfold swift.descPoolOk; iexists γsh, _; iframe Hsh Hpool'
    ipureintro; intro h; cases h
  imodintro
  ipersist FhistoryStart
  ipersist FoptExec
  ipersist FfastRead
  ipersist FfixedMajority
  ipersist FpoolLevel
  ipersist FslowAddrs
  ipersist Hsam
  ipersist FdeliverChan
  ipersist FrecheckChan
  ipersist FSQ
  ipersist Hmax
  ipersist RAlias
  ipersist RPeerAddrList
  ipersist RPeers
  ipersist RPeerReaders
  ipersist RPeerWriters
  ipersist RAlive
  ipersist RLatencies
  ipersist REwma
  ipersist RClientWriters
  ipersist RConfig
  ipersist RLRead
  ipersist RDt
  ipersist RProposeChan
  ipersist RExec
  ipersist RDreply
  ihave %Hmok := memIs_ok _ _ $$ Hmem
  -- round 25 (D24): `SQ = NewMajorityOf(N)`'s quorum (swift.go:233)
  ihave #HSQq : replica.mset.quorumIs
      (interface.mkOk replica.Majority.ty #(W64 ((l.length : Int) / 2 + 1))) (l.length / 2 + 1)
      (fun _ => True) $$ []
  · iunfold replica.mset.quorumIs
    isplitr
    · ipureintro; omega
    ileft
    ipureintro
    refine ⟨Or.inl ?_, fun _ => trivial⟩
    rw [show (((l.length / 2 + 1 : Nat)) : Int) = (l.length : Int) / 2 + 1 by omega]
  wp_apply wp_fork $$ [-HΦ r «$res0»]
  · wp_apply (wp_run «$r0_ptr» γ γc γm γl l.length k (W32 (sint.Z rid)) fr l a ip pl) $$ [-]
    · iunfold swift.runPre
      iexists rr, rv.RPC', s, b, rc, qs, γs, γrl, γd, γdc1, γdl, dm1, dch, kch, γdc, γkc, hsl, km, hm, pm,
        propm, accm, waitm, sam, (interface.mkOk replica.Majority.ty #(W64 ((l.length : Int) / 2 + 1))),
        (interface.mkOk replica.Quorum.ty #fq), csv, M, (W8 23), d
      iframe
      iframe #
      have hme : (W32 (sint.Z rid)).toInt = sint.Z rid := by word
      have hme2 : sp.rid (W32 (sint.Z rid)) = uint.nat rid := by
        unfold sp.rid; rw [hme]; word
      isplitr
      · ipureintro
        refine ⟨by rw [hme2]; exact hrid1, ?_, by word, by omega, by omega⟩
        rw [hme2]; unfold nodeOf; rw [hla]; exact swift.replicaAddrs_idxOf k a hka
      isplitr
      · -- `MaxDescRoutines`' bound (change log C21: New.spec's C14 premise)
        ipureintro
        exact Hdb
      isplitr
      · iExactEq Hpool; rfl
      isplitr
      · ipureintro; exact ⟨Hcs.1, Hcs.2.1⟩
      isplitr
      · ipureintro; exact Hpps
      isplitr
      · iExactEq RExec; rw [hEx]
      isplitl [Htbl]
      · iunfold rpc.tblOwn at Htbl; iunfold rpc.isTable; iexact Htbl
      iintro #Htok' #Htbl'
      iunfold replica.connPre
      iexists lg, cfgp, rv.RPC', rv.ProposeChan', fr, (W8 23), M, γpc, rv.PeerAddrList', rv.Peers',
        rv.PeerReaders', rv.PeerWriters', rv.Alive', rv.Latencies', rv.Ewma', l, rv.ClientWriters',
        List.replicate l.length (W64 0), List.replicate l.length (W64 0), rv.Alias'
      rw [hPA, hCf, hM, hLi, hPC, hLR, hDt]
      iframe
      iframe #
      isplitr
      · iunfold config.plain; iexists cv, pi; iframe Hcv Hpi
        ipureintro; exact ⟨hcf0, hpx0, hq0, hld0, hor0, hpi1, hpi2, hpi3⟩
      ipureintro
      have hidx : (BitVec.toInt (W32 (sint.Z rid))).toNat = uint.nat rid := by rw [hme]; word
      refine ⟨by rw [hidx]; exact hla, ?_, hip, by rw [hme]; exact hrid.1, by rw [hme]; exact hrid.2.1,
        by omega, rfl, Hmok.2, by simp, by simp⟩
      rw [List.contains_iff_mem]
      exact List.mem_of_getElem? hka
    ipureintro; simp
  try wp_auto
  iapply HΦ
  iapply rcvr
  isplitr
  · ipureintro; exact Hrnn
  iframe Hrcs Hpkg Hres

end proof

end Perennial.github_com.imdea_software.swiftpaxos
