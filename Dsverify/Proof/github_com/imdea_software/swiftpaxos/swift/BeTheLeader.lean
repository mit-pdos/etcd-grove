/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/BeTheLeader.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.BeTheLeader(args, reply)` (swift.go) from an rpc goroutine: if the replica executed
something (`deliveredAny.Load()`, fork change P2-A: no reader bundle of `delivered`), ask the run loop for a recovery (`recover <- BallotAt(1)`) and answer with its id;
else answer with the current leader, read under `ballotL` (R6). `NextLeader` is the leader of
`BallotAt(1)` (`-1`: no quorum file). Zero ids are sent as `-2` (gob's zero).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AnyFlag
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumArithDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.BeTheLeaderDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]

end spec

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [github_com.orcaman.concurrent_map.Assumptions]
  [sync.Assumptions] [sync.atomic.Assumptions]

theorem swift.Replica.BeTheLeader.wp_proof
    (wp_Load : sync.atomic.Bool.Load.spec (GF := netDistGF) (hG := hG))
    (wp_BallotAt : replica.QuorumSystem.BallotAt.spec)
    (wp_Leader : replica.Leader.spec) :
    swift.Replica.BeTheLeader.spec := by
  intro r γc γm args reply rv
  wp_start as ⟨#Hres, Hrep⟩
  iunfold swift.rcvrRes at Hres
  icases Hres with ⟨%rr, %N, %fr, %l, %me, %dm, %qs, %rc, %γrc, %γdl, #Hrr, #HN, #Hid, #Hcfg, %HNme,
    #Hdm, #Hcm, #Hany, #Hqs, #HisQS, #Hrc, #Hbag, #Hmu⟩
  wp_auto
  wp_apply swift.wp_anyLoad wp_Load r $$ [$Hany] as %emp -
  cases emp
  rotate_left
  · -- executed something: ask for a recovery, answer with the replica's id
    wp_auto
    wp_apply wp_BallotAt $$ [$HisQS]
    · ipureintro; word
    wp_apply wp_bag_send (t := go.int32) γrc rc (W32 (-1)) (swift.recoverOk r)
      $$ [$Hbag]
    · iunfold swift.recoverOk; ileft; ipureintro; rfl
    wp_apply wp_BallotAt $$ [$HisQS]
    · ipureintro; word
    wp_apply wp_Leader
    · ipureintro; word
    simp only
    have hm1 := swift.srem_m1 N ⟨HNme.1, HNme.2.1⟩
    have hN' : 1 ≤ N ∧ N ≤ 7 := ⟨HNme.1, HNme.2.1⟩
    wp_if_destruct
    · try wp_auto
      wp_if_destruct
      · try wp_auto
        iapply HΦ
        iexists _, _
        iframe Hrep
        iexists N, fr, l
        iframe Hcfg
        ipureintro
        exact swift.btlOk_of N hN' _ _ (Or.inl rfl) (Or.inl rfl)
      · try wp_auto
        iapply HΦ
        iexists _, _
        iframe Hrep
        iexists N, fr, l
        iframe Hcfg
        ipureintro
        exact swift.btlOk_of N hN' _ _ (Or.inl rfl) (Or.inr (hm1.resolve_right Hif))
    · have hme := Hif
      have hme' : 1 ≤ sint.Z me ∧ sint.Z me < N := by
        have : sint.Z me ≠ 0 := fun h => hme (by word)
        have := HNme.2.2.1; have := HNme.2.2.2; omega
      try wp_auto
      wp_if_destruct
      · try wp_auto
        iapply HΦ
        iexists _, _
        iframe Hrep
        iexists N, fr, l
        iframe Hcfg
        ipureintro
        exact swift.btlOk_of N hN' me _ (Or.inr hme') (Or.inl rfl)
      · try wp_auto
        iapply HΦ
        iexists _, _
        iframe Hrep
        iexists N, fr, l
        iframe Hcfg
        ipureintro
        exact swift.btlOk_of N hN' me _ (Or.inr hme') (Or.inr (hm1.resolve_right Hif))
  · -- nothing executed: the current leader, read under `ballotL`
    wp_auto
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
    iunfold swift.ballotLInv at HR
    icases HR with ⟨%b, Hb, %Hb0⟩
    wp_method_call
    wp_call
    wp_auto
    wp_apply wp_Leader
    · ipureintro; word
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hb]
    · iunfold swift.ballotLInv
      iexists b
      iframe
      ipureintro; exact Hb0
    have hlb := swift.srem_nonneg b N ⟨HNme.1, HNme.2.1⟩ Hb0
    wp_apply wp_BallotAt $$ [$HisQS]
    · ipureintro; word
    wp_apply wp_Leader
    · ipureintro; word
    simp only
    have hm1 := swift.srem_m1 N ⟨HNme.1, HNme.2.1⟩
    have hN' : 1 ≤ N ∧ N ≤ 7 := ⟨HNme.1, HNme.2.1⟩
    wp_if_destruct
    · try wp_auto
      wp_if_destruct
      · try wp_auto
        iapply HΦ
        iexists _, _
        iframe Hrep
        iexists N, fr, l
        iframe Hcfg
        ipureintro
        exact swift.btlOk_of N hN' _ _ (Or.inl rfl) (Or.inl rfl)
      · try wp_auto
        iapply HΦ
        iexists _, _
        iframe Hrep
        iexists N, fr, l
        iframe Hcfg
        ipureintro
        exact swift.btlOk_of N hN' _ _ (Or.inl rfl) (Or.inr (hm1.resolve_right Hif))
    · have hme := Hif
      have hme' : 1 ≤ sint.Z (BitVec.srem b (W32 (sint.Z (W64 (N : Int))))) ∧
          sint.Z (BitVec.srem b (W32 (sint.Z (W64 (N : Int))))) < N := by
        have : sint.Z (BitVec.srem b (W32 (sint.Z (W64 (N : Int))))) ≠ 0 := fun h => hme (by word)
        omega
      try wp_auto
      wp_if_destruct
      · try wp_auto
        iapply HΦ
        iexists _, _
        iframe Hrep
        iexists N, fr, l
        iframe Hcfg
        ipureintro
        exact swift.btlOk_of N hN' _ _ (Or.inr hme') (Or.inl rfl)
      · try wp_auto
        iapply HΦ
        iexists _, _
        iframe Hrep
        iexists N, fr, l
        iframe Hcfg
        ipureintro
        exact swift.btlOk_of N hN' _ _ (Or.inr hme') (Or.inr (hm1.resolve_right Hif))

end proof

end Perennial.github_com.imdea_software.swiftpaxos
