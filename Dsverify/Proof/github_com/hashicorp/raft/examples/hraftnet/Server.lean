/-
`hraftnet.Server`'s proof (the hraft kit's server machine; notes/dsv-hraft.md, S5d), after dsverify-lab's
hr3 `run.lean` (its per-server loop body): the configuration's size from `awaitConf` (a future), the
server's package of the drawn protocol (`claim_pkg`), the codec, raft's options (`cfgOk`), the stores,
the transport over the wrapped world (`svcAt_svcK`), its receiver registered (`raftRcvLaws_svcK`), the
bootstrap if `j ≤ n0`, the FSM, `NewRaft`, the API registered (`apiRcvLaws_svcK`), then `Accept` on a
goroutine of its own and the sleep loop.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.Server
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.awaitConf
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.listen
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.ConfAddrs
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.ServerAddrs
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.Register
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.raftConfig
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.serverAddr
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.peers
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.bootConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.ValidateConfig
public import Dsverify.Spec.github_com.hashicorp.raft.NewInmemStore
public import Dsverify.Spec.github_com.hashicorp.raft.BootstrapCluster
public import Dsverify.Spec.github_com.hashicorp.raft.NewRaft
public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.New
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.New
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__Receiver
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.NewStore
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.New
public import Dsverify.Proof.github_com.hashicorp.raft.InmemStoreIface
public import Dsverify.Proof.github_com.hashicorp.raft.InmemLogIface
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.service.FsmIface
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.IsTransport
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ChoiceRcv
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ApiRcvK
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ApiRcvSvc
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.CodecLawsProof
public import Net.Spec.net.rpc.NewServer
public import Net.Spec.net.rpc.Server__Register
public import Net.Spec.net.rpc.Server__Accept
public import Perennial.Proof.time.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto
open rpctransport service

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS] [rsem : github_com.hashicorp.raft.Assumptions]
variable [bvi : go.BasicIntoValInj]
variable [net.rpc.Assumptions] [rpcpkg : rpctransport.Assumptions] [svcpkg : service.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]


/-- Server `i`'s durable prefix stays below `2^62` (`gprot.durLb_lt`, under the receipt bound). -/
theorem durBound_of (γ : GNames) (i : SID) : Inv (GF := GF) γ ∗ isSrv γ i ⊢ durBound γ i := by
  iintro ⟨#Hinv, #Hv⟩
  unfold durBound
  imodintro
  iintro %k #Hd
  iapply durLb_lt γ ⊤ (by simp) i k $$ [Hinv Hv Hd]
  iframe #

/-- The transport's peers in the wrapped world, to who knows the draw. -/
theorem peers_ok (K : HK GF) (n : Nat) (hss : kitSS K) :
    □ (chosen K.γc n ∗ [∗list] a ∈ serverAddrs, net.rpc.rpcAddr (Gg := hG.goose_globalGS) K.W a) ⊢
      [∗map] a ↦ na ∈ peersUpTo 6, (net.rpc.rpcAddr (Gg := hG.goose_globalGS) K.W na ∗
        svcAt (K.γs n) (snapP (K.γs n) (K.fcs n)) K.W a na) := by
  refine BigSepM.bigSepM_intro (fun {a na} hget => ?_)
  obtain ⟨k, hk, rfl, rfl⟩ := peersUpTo_lookup 6 a na hget
  iintro #⟨Hc, Hl⟩
  have hget2 : serverAddrs[k]? = some (serverAddrs.getD k go!"") := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      have : serverAddrs.length = 6 := rfl; omega)]
    rfl
  isplitr
  · iapply (BigSepL.bigSepL_lookup (PROP := IProp GF)
      (Φ := fun _ a => net.rpc.rpcAddr (Gg := hG.goose_globalGS) K.W a) hget2) $$ Hl
  · iapply svcAt_svcK K.γc
      (fun m => raftSvc (K.γs m) (snapP (K.γs m) (K.fcs m)) (sidOf (W64 ((k + 1 : Nat) : Int)))) n
      (K.γs n) (snapP (K.γs n) (K.fcs n)) K.W _ _ ?_ rfl $$ Hc
    have h := hss (k + 1) svcName (by omega) (by omega)
    rw [show k + 1 - 1 = k by omega, if_pos rfl] at h
    exact h

set_option goose.wp.extras true

theorem Server.wp_proof
    (wp_awaitConf : awaitConf.spec (GF := GF))
    (wp_ConfAddrs : ConfAddrs.spec (GF := GF))
    (wp_ServerAddrs : ServerAddrs.spec (GF := GF))
    (wp_Register : Register.spec (GF := GF))
    (wp_raftConfig : raftConfig.spec (GF := GF))
    (wp_ValidateConfig : github_com.hashicorp.raft.ValidateConfig.spec (GF := GF))
    (wp_NewInmemStore : github_com.hashicorp.raft.NewInmemStore.spec (GF := GF))
    (wp_SSNew : github_com.hashicorp.raft.examples.snapstore.New.spec (GF := GF))
    (wp_serverAddr : serverAddr.spec (GF := GF))
    (wp_peers : peers.spec (GF := GF))
    (wp_TNew : rpctransport.New.spec (GF := GF))
    (wp_NewServer : net.rpc.NewServer.spec_owned (GF := GF) (hG := hG))
    (wp_SRegister : net.rpc.Server.Register.spec_fresh (GF := GF) (hG := hG))
    (wp_Receiver : rpctransport.Transport.Receiver.spec (GF := GF))
    (wp_BootstrapCluster : github_com.hashicorp.raft.BootstrapCluster.spec (GF := GF))
    (wp_bootConfiguration : bootConfiguration.spec (GF := GF))
    (wp_NewStore : service.NewStore.spec (GF := GF))
    (wp_NewRaft : github_com.hashicorp.raft.NewRaft.spec (GF := GF))
    (wp_New : service.New.spec (GF := GF))
    (wp_listen : listen.spec (GF := GF))
    (wp_Accept : net.rpc.Server.Accept.spec (GF := GF) (hG := hG))
    -- the stores' interfaces
    (wp_GetUint64 : github_com.hashicorp.raft.InmemStore.GetUint64.spec (GF := GF) (hG := hG))
    (wp_SetUint64 : github_com.hashicorp.raft.InmemStore.SetUint64.spec (GF := GF) (hG := hG))
    (wp_Get : github_com.hashicorp.raft.InmemStore.Get.spec (GF := GF) (hG := hG))
    (wp_Set : github_com.hashicorp.raft.InmemStore.Set.spec (GF := GF) (hG := hG))
    (wp_LastIndex : github_com.hashicorp.raft.InmemStore.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : github_com.hashicorp.raft.InmemStore.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_GetLog : github_com.hashicorp.raft.InmemStore.GetLog.spec (GF := GF) (hG := hG))
    (wp_StoreLogs : github_com.hashicorp.raft.InmemStore.StoreLogs.spec (GF := GF) (hG := hG))
    (wp_StoreLog : github_com.hashicorp.raft.InmemStore.StoreLog.spec (GF := GF) (hG := hG))
    (wp_DeleteRange : github_com.hashicorp.raft.InmemStore.DeleteRange.spec (GF := GF) (hG := hG))
    -- the FSM's interface
    (wp_SApply : service.Store.Apply.spec (GF := GF) (hG := hG))
    (wp_SSnapshot : service.Store.Snapshot.spec (GF := GF) (hG := hG))
    (wp_SRestore : service.Store.Restore.spec (GF := GF) (hG := hG))
    (wp_SPersist : service.snapshot.Persist.spec (GF := GF) (hG := hG))
    (wp_SRelease : service.snapshot.Release.spec (GF := GF) (hG := hG))
    (wp_SStoreConfiguration : service.Store.StoreConfiguration.spec (GF := GF) (hG := hG))
    -- the transport's interface
    (wp_TConsumer : Transport.Consumer.spec (GF := GF) (hG := hG))
    (wp_TLocalAddr : Transport.LocalAddr.spec (GF := GF) (hG := hG))
    (wp_TEncodePeer : Transport.EncodePeer.spec (GF := GF) (hG := hG))
    (wp_TDecodePeer : Transport.DecodePeer.spec (GF := GF) (hG := hG))
    (wp_TSetHeartbeatHandler : Transport.SetHeartbeatHandler.spec (GF := GF) (hG := hG))
    (wp_TAppendEntriesPipeline : Transport.AppendEntriesPipeline.spec (GF := GF) (hG := hG))
    (wp_TAppendEntries : Transport.AppendEntries.spec (GF := GF) (hG := hG))
    (wp_TRequestVote : Transport.RequestVote.spec (GF := GF) (hG := hG))
    (wp_TRequestPreVote : Transport.RequestPreVote.spec (GF := GF) (hG := hG))
    (wp_TInstallSnapshot : Transport.InstallSnapshot.spec (GF := GF) (hG := hG))
    (wp_TTimeoutNow : Transport.TimeoutNow.spec (GF := GF) (hG := hG))
    -- the transport's receiver
    (wpAE : RaftRPC.AppendEntries.spec (GF := GF)) (wpIS : RaftRPC.InstallSnapshot.spec (GF := GF))
    (wpPV : RaftRPC.RequestPreVote.spec (GF := GF)) (wpRV : RaftRPC.RequestVote.spec (GF := GF))
    (wpTN : RaftRPC.TimeoutNow.spec (GF := GF))
    -- the API's receiver
    (wpAp : API.Apply.spec (GF := GF)) (wpAV : API.AddVoter.spec (GF := GF))
    (wpAN : API.AddNonvoter.spec (GF := GF)) (wpDV : API.DemoteVoter.spec (GF := GF))
    (wpRS : API.RemoveServer.spec (GF := GF)) (wpLT : API.LeadershipTransfer.spec (GF := GF))
    (wpSn : API.Snapshot.spec (GF := GF)) (wpSt : API.Status.spec (GF := GF))
    (wpRd : API.Read.spec (GF := GF)) :
    Server.spec (GF := GF) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
