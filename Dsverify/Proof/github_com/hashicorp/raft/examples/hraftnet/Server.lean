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
    (mRead : ∀ (a : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (fc : FCtx GF) (alb : GName),
      apiMeth.spec (apiP a γ rc i fc alb) a go!"Read" readArgsOwn encReadArgs readReplyOwn
        encReadReply (apiSvc γ fc go!"Read")) :
    Server.spec (GF := GF) := by
  intro hTB K j hj1 hj2
  wp_start as ⟨Hsh, Hboot, %Hb, Htt⟩
  iunfold srvShare at Hsh
  icases Hsh with ⟨#Hcps, #Hra, #Hlp, %Hss, #Hdraw, Hstok⟩
  obtain ⟨hss, hγ⟩ := Hss
  iunfold srvBoot at Hboot
  icases Hboot with ⟨#Hmu, Hun, #Henv, #Hlog⟩
  icases threadTok_split $$ Htt with ⟨%t, Ht1, -, -, -⟩
  ihave #Hrinit : isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft $$ []
  · iPkgInit
  ihave #Hioinit : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hnv := newVar_of_init RaftErr.logNotFound $$ Hrinit
  simp only [RaftErr.var] at *
  ihave #Herr := errLogNotFoundOk_of_newVar _ $$ Hnv
  ihave #Heofv := io.eof_of_init $$ Hioinit
  iunfold errors.newVar at Heofv
  icases Heofv with ⟨%eofl, #Heof, -⟩
  -- the configuration's size, from `awaitConf` on a goroutine of its own
  try wp_auto
  wp_apply chan.wp_make2 (V := w64) (W64 1) $$ [] as %ch %γch ⟨#Hch, -, Hoc⟩
  · ipureintro; decide
  iapply fupd_wp
  imod start_future (V := w64) ch γch _ (.inr rfl) $$ Hch Hoc with ⟨%γf, #Hfut, HAwait⟩
  imod future_alloc_promise (V := w64) γf ch (confOk (G := hG.goose_globalGS) K.γc) [] $$ Hfut HAwait
    with ⟨Hful, HAwait⟩
  imodintro
  try wp_auto
  wp_apply wp_ConfAddrs as %cs ⟨%L, Hcs, %HL⟩
  subst HL
  ihave %Hclen := ownSlice_len $$ Hcs
  have hcb : 0 ≤ sint.Z (W64 (j : Int) - W64 1) ∧ sint.Z (W64 (j : Int) - W64 1) < sint.Z cs.len := by
    have : confAddrs.length = 6 := rfl
    constructor <;> word
  try (rw [ite_eq_left hcb])
  have hca : confAddrs[(sint.Z (W64 (j : Int) - W64 1)).toNat]? =
      some (confAddrs.getD (j - 1) go!"") := by
    rw [show (sint.Z (W64 (j : Int) - W64 1)).toNat = j - 1 by word, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by have : confAddrs.length = 6 := rfl; omega)]
    rfl
  wp_apply (wp_load_slice_index cs _ confAddrs _ _ hcb.1) $$ [Hcs] as Hcs
  · iframe; ipureintro; exact hca
  ihave #Hcp := Hcps
  iunfold confProtos at Hcp
  ihave #Hpa := (BigSepL.bigSepL_lookup (PROP := IProp GF)
    (Φ := fun _ a => addrProto (Gg := hG.goose_globalGS) a (confProto K.γc) ackProto)
    (show confAddrs[j - 1]? = some (confAddrs.getD (j - 1) go!"") by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
        have : confAddrs.length = 6 := rfl; omega)]; rfl)) $$ Hcp
  wp_apply wp_fork $$ [Hful]
  · wp_apply (wp_awaitConf K.γc γf ch _) $$ [Hful]
    · iframe; iframe #
    itrivial
  wp_apply (lc := 1) (wp_future_await (t := go.uint64) γf ch _) $$ [HAwait]
    as %n0 %P %pre %post ⟨%Hsplit, HP, -⟩
  · iframe; iframe #
  have hP : P = confOk (G := hG.goose_globalGS) K.γc := by
    rcases pre with _ | ⟨_, pre⟩
    · simp only [List.nil_append, List.cons.injEq] at Hsplit; exact Hsplit.1.symm
    · simp at Hsplit
  subst hP
  iunfold confOk at HP
  icases HP with ⟨%n, %Hn, #Hc⟩
  obtain ⟨rfl, hn⟩ := Hn
  obtain ⟨hsrvs, hg, hcv⟩ := hγ n hn
  -- the server's package of the drawn protocol
  iapply fupd_wp
  imod claim_pkg K n j ⟨hj1, hj2⟩ $$ [Hlc1 Hstok] with Hpkg
  · iframe Hlc1 Hstok; iframe #
  imodintro
  iunfold srvPkg at Hpkg
  icases Hpkg with ⟨#Hinv, Hbun, #Hfr, #Hls⟩
  iunfold srvBundle at Hbun
  icases Hbun with ⟨#Hvot, Hown, Hdur, Htc, Hlcp, Hcc⟩
  -- the codec
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_Register $$ [Hun] as #Hcs
  · iframe Hun; iframe #
  -- raft's options
  wp_apply (wp_raftConfig (W64 (j : Int))) as %cp ⟨%c, Hcp, %Hcfg⟩
  wp_apply (wp_ValidateConfig cp c (DFrac.own 1) (sidOf (W64 (j : Int)))) $$ [Hcp] as Hcp
  · iframe Hcp; iframe #; ipureintro; exact Hcfg
  try wp_auto
  -- the stores
  wp_apply (wp_NewInmemStore hTB) $$ [] as %logs ⟨%γs1, #Hlogs, Hl1, -⟩
  · iframe #
  wp_apply (wp_NewInmemStore hTB) $$ [] as %stb ⟨%γs2, #Hstb, -, Hkv2⟩
  · iframe #
  ihave #Hsinit : isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore $$ []
  · iPkgInit
  wp_apply (wp_SSNew _) $$ [] as %snp ⟨%ownSS, #HSS, Hssown⟩
  · iframe #
  -- the transport, over the wrapped world
  wp_apply wp_serverAddr
  wp_apply wp_peers as %pm Hpm
  ihave #Hpeers := peers_ok K n hss $$ []
  · iframe #
  ihave #Htinit : isPkgInit (PROP := IProp GF)
    pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport $$ []
  · iPkgInit
  wp_apply (wp_TNew (sidOf (W64 (j : Int))) pm (DFrac.own 1) (peersUpTo 6) _ (K.γs n)
    (snapP (K.γs n) (K.fcs n)) K.W hraftCodec) $$ [Hpm] as %tr ⟨Hpm, #Htr⟩
  · iframe Hpm; iframe #
    ipureintro; exact ⟨Hb.1, hraftCodecLaws⟩
  -- the net/rpc server and the transport's receiver
  wp_apply wp_NewServer as %srv ⟨%γs, %γo, #Hsrv, Hso⟩
  wp_apply (wp_Receiver tr (K.γs n) (snapP (K.γs n) (K.fcs n)) (sidOf (W64 (j : Int))) K.W hraftCodec)
    as %rcv #Hrcv
  · iframe #
  ihave %Hrnn : ⌜rcv ≠ null⌝ $$ [Hrcv]
  · iunfold isRcv at Hrcv
    icases Hrcv with ⟨%t', #Hp, -⟩
    iapply typedPointsto_not_null $$ Hp
  ihave HRr := raftRcv _ rcv _ (raftRcvLaws_svcK _ rcv K.γc K.γs (fun m => snapP (K.γs m) (K.fcs m))
      (sidOf (W64 (j : Int))) n (raftRcvLaws_of wpAE wpIS wpPV wpRV wpTN rcv (K.γs n)
        (snapP (K.γs n) (K.fcs n)) (sidOf (W64 (j : Int))) K.W hraftCodec)) $$ []
  · isplitr; · ipureintro; exact Hrnn
    isplitr; · iexact Hcs
    isplitr
    · isplitr; · iexact Htinit
      iexact Hrcv
    iexact Hc
  wp_apply (wp_SRegister srv γs γo ∅ hraftCodec (ptrI RaftRPC.ty rcv) (raftSvcK K j) go!"RaftRPC"
      (W8 82) go!"aftRPC" rfl (by decide)) $$ [Hso HRr] as %e1 ⟨%He1, #Hreg1, Hso⟩
  · iframe Hso; iframe #
    isplitr; · ipureintro; simp [GMap.mem_iff]
    unfold raftSvcK
    iexact HRr
  subst He1
  try wp_auto
  -- the stores' and the transport's contracts
  ihave #HLS := inmem_isLogStore wp_LastIndex wp_FirstIndex wp_GetLog wp_StoreLogs wp_StoreLog
    wp_DeleteRange γs1 logs $$ Hlogs
  ihave #HST := inmem_isStableStore wp_GetUint64 wp_SetUint64 wp_Get wp_Set γs2 stb $$ Hstb
  icases Transport_isTransport wp_TConsumer wp_TLocalAddr wp_TEncodePeer wp_TDecodePeer
    wp_TSetHeartbeatHandler wp_TAppendEntriesPipeline wp_TAppendEntries wp_TRequestVote
    wp_TRequestPreVote wp_TInstallSnapshot wp_TTimeoutNow tr (K.γs n) (snapP (K.γs n) (K.fcs n))
    (sidOf (W64 (j : Int))) K.W hraftCodec $$ [Htinit Htr] with ⟨%rpcCh, #HT⟩
  · iframe #
  -- the first configuration's voters are servers `1..n`
  have hok := srvsOkIn_bootSrvs n (by unfold N0Ok at hn; omega)
  have hcvg : (K.γs n).cv (K.γs n).g.data = sidsUpTo n := by
    rw [hcv, hg]
    show cfgDec allSids (encodeServers (bootSrvs n)) = sidsUpTo n
    rw [cfgDec_encode _ _ hok, srvVoters_bootSrvs]
  have hmem : sidOf (W64 (j : Int)) ∈ (K.γs n).cv (K.γs n).g.data ↔ j ≤ n := by
    rw [hcvg]
    constructor
    · intro h
      unfold sidsUpTo at h
      simp only [List.mem_map, List.mem_range] at h
      obtain ⟨k, hk, hke⟩ := h
      have := sidOf_inj (k + 1) j (by unfold N0Ok at hn; omega) (by omega) hke
      omega
    · intro h; exact sidOf_mem_sidsUpTo j n ⟨hj1, h⟩
  have hn6 : n ≤ 6 := by unfold N0Ok at hn; omega
  have hle : ∀ (a b : Nat), a ≤ 6 → b ≤ 6 →
      (uint.Z (W64 (a : Int)) ≤ uint.Z (W64 (b : Int)) ↔ a ≤ b) := by
    intro a b ha hb
    have e1 : uint.Z (W64 (a : Int)) = a := by word
    have e2 : uint.Z (W64 (b : Int)) = b := by word
    rw [e1, e2]; omega
  -- servers `1..n` bootstrap the first configuration; the others start empty
  ipersist conf
  ipersist logs
  ipersist stable
  ipersist snaps
  ipersist trans
  ipersist n0
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ sst : StableAbs, cp ↦ c ∗
      inmemLogs γs1 (LogAbs.empty.store 1
        (initSrv (K.γs n).cv (K.γs n).g (sidOf (W64 (j : Int)))).log) ∗
      kvView γs2 sst ∗ ownSS none ∗ rtok t ∗
      ⌜sst.ints.lookup (go!"CurrentTerm" : List w8) =
          (if sidOf (W64 (j : Int)) ∈ (K.γs n).cv (K.γs n).g.data then some (W64 1) else none) ∧
        sst.ints.lookup (go!"LastVoteTerm" : List w8) = none⌝)))
    $$ [Hcp Hl1 Hkv2 Hssown Ht1] [-]
  · wp_if_destruct
    · have hin : sidOf (W64 (j : Int)) ∈ (K.γs n).cv (K.γs n).g.data := hmem.2 ((hle j n hj2 hn6).1 Hif)
      try wp_auto
      wp_apply (wp_bootConfiguration n (by unfold N0Ok at hn; omega)) as %cfgv Hcfgv
      wp_apply (wp_BootstrapCluster cp c ⟨_, #logs⟩ ⟨_, #stb⟩ ⟨_, #snp⟩ _ cfgv (bootSrvs n)
        (DFrac.own 1) (K.γs n) (sidOf (W64 (j : Int))) (inmemLogs γs1) (kvView γs2) ownSS _ ⟨∅, ∅⟩ t)
        $$ [$Hcp $HLS $HST $HSS $Hcfgv $Hl1 $Hkv2 $Hssown $Ht1] as ⟨Hcp, -, Hl1, Hkv2, Hssown, Ht1⟩
      · ipureintro
        refine ⟨Hcfg, ⟨?_, ?_, ?_⟩, rfl⟩
        · show srvsOkIn (K.γs n).srvs (bootSrvs n); rw [hsrvs]; exact hok
        · rw [hsrvs]; exact allSids_nodup
        · rw [hsrvs]; simp [allSids, sidsUpTo]
      try wp_auto
      isplitr; · itrivial
      iexists _
      iframe
      have hinit : (initSrv (K.γs n).cv (K.γs n).g (sidOf (W64 (j : Int)))).log =
          [genesisOf (bootSrvs n)] := by
        unfold initSrv; rw [if_pos hin, hg]
      rw [hinit, if_pos hin]
      iframe
      ipureintro
      constructor <;> simp
    · have hnin : sidOf (W64 (j : Int)) ∉ (K.γs n).cv (K.γs n).g.data := fun h =>
        Hif ((hle j n hj2 hn6).2 (hmem.1 h))
      isplitr; · itrivial
      iexists _
      iframe
      have hinit : (initSrv (K.γs n).cv (K.γs n).g (sidOf (W64 (j : Int)))).log = [] := by
        unfold initSrv; rw [if_neg hnin]
      rw [hinit, if_neg hnin, show LogAbs.empty.store 1 [] = LogAbs.empty from rfl]
      iframe
      ipureintro
      constructor <;> rfl
  iintro %v ⟨%hv, %sst, Hcp, Hl1, Hkv2, Hssown, Ht1, %Hsst⟩
  subst hv
  try wp_auto
  -- the FSM and raft
  ihave #Hdb := durBound_of (K.γs n) (sidOf (W64 (j : Int))) $$ []
  · iframe #
  ihave #Hsvinit : isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service $$ []
  · iPkgInit
  wp_apply (wp_NewStore (K.γs n) (K.fcs n) (sidOf (W64 (j : Int)))) as %fsm ⟨%alb, #HisSt, Hfo⟩
  · iframe #
  ihave #HFSM := store_isFSM wp_SApply wp_SSnapshot wp_SRestore wp_SPersist wp_SRelease
    wp_SStoreConfiguration (K.γs n) (K.fcs n) alb (sidOf (W64 (j : Int))) fsm $$ []
  · iframe #
  wp_apply (wp_NewRaft hTB cp c _ ⟨_, #logs⟩ ⟨_, #stb⟩ ⟨_, #snp⟩ _ rpcCh (K.γs n) (sidOf (W64 (j : Int)))
      (inmemLogs γs1) (kvView γs2) ownSS _ (snapP (K.γs n) (K.fcs n)) (fsmOwn alb)
      (respP (K.γs n) (K.fcs n) alb) sst t)
    $$ [$Hcp $HFSM $HLS $HST $HSS $Heof $HT $Hl1 $Hkv2 $Hssown $Hinv $Hvot
      $Hown $Htc $Hlcp $Hcc $Hdur $Hfo $Ht1] as %r ⟨⟨%names, #Hraft⟩, Hcp, Ht1⟩
  · ipureintro
    refine ⟨Hcfg, store_fsmNotBatching fsm, ?_, ?_, Hsst, ?_, ⟨bootSrvs n, ?_, hg⟩⟩
    · go_type_set
    · go_type_set
    · rw [hcv, hsrvs]
    · show srvsOkIn (K.γs n).srvs (bootSrvs n); rw [hsrvs]; exact hok
  try wp_auto
  -- the API
  wp_apply (wp_New r fsm _ _ (K.γs n) (RCtx.mk (inmemLogs γs1) ownSS (snapP (K.γs n) (K.fcs n))
      (kvView γs2) (fsmOwn alb) (respP (K.γs n) (K.fcs n) alb) names) (sidOf (W64 (j : Int)))
      (K.fcs n) alb) as %api ⟨#Hapi, %Hann⟩
  · iframe #; ipureintro; rfl
  ihave HRa := apiRcv _ api _ (apiRcvLaws_svcK _ api K n (apiRcvLaws_of wpAp wpAV wpAN wpDV wpRS wpLT
      wpSn api (K.γs n) (RCtx.mk (inmemLogs γs1) ownSS (snapP (K.γs n) (K.fcs n))
      (kvView γs2) (fsmOwn alb) (respP (K.γs n) (K.fcs n) alb) names) (sidOf (W64 (j : Int)))
      (K.fcs n) alb (mRead _ _ _ _ _ _) wpSt)) $$ []
  · isplitr; · ipureintro; exact Hann
    isplitr; · iexact Hcs
    isplitr
    · isplitr; · iexact Hsvinit
      iexact Hapi
    iexact Hc
  wp_apply (wp_SRegister srv γs γo _ hraftCodec (ptrI service.API.ty api) (apiSvcK K) go!"API"
      (W8 65) go!"PI" rfl (by decide)) $$ [Hso HRa] as %e2 ⟨%He2, #Hreg2, Hso⟩
  · iframe Hso; iframe #
    isplitr; · ipureintro; simp [GMap.mem_iff]
    unfold apiSvcK
    iexact HRa
  subst He2
  try wp_auto
  -- serve: `listen` at the server's address, `Accept` on a goroutine of its own
  wp_apply wp_ServerAddrs as %ss ⟨%L2, Hss2, %HL2⟩
  subst HL2
  ihave %Hslen := ownSlice_len $$ Hss2
  have hsb : 0 ≤ sint.Z (W64 (j : Int) - W64 1) ∧ sint.Z (W64 (j : Int) - W64 1) < sint.Z ss.len := by
    have : serverAddrs.length = 6 := rfl
    constructor <;> word
  try (rw [ite_eq_left hsb])
  have hsa : serverAddrs[(sint.Z (W64 (j : Int) - W64 1)).toNat]? =
      some (serverAddrs.getD (j - 1) go!"") := by
    rw [show (sint.Z (W64 (j : Int) - W64 1)).toNat = j - 1 by word, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by have : serverAddrs.length = 6 := rfl; omega)]
    rfl
  wp_apply (wp_load_slice_index ss _ serverAddrs _ _ hsb.1) $$ [Hss2] as Hss2
  · iframe; ipureintro; exact hsa
  have haok : addrOk (serverAddrs.getD (j - 1) go!"") = true := by
    have : j - 1 < 6 := by omega
    generalize hk : j - 1 = k at this
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  wp_apply (wp_listen (serverAddrs.getD (j - 1) go!"")) as %lv ⟨%l, #Hli, Hnl, #Hla⟩
  · isplitr; · ipureintro; exact haok
    imodintro
    imod (net.rpc.rpcLisP_lis _ _ _ _) $$ Hlp with ⟨Ht, Hk⟩
    imodintro
    isplitl [Ht]
    · iapply (lisToks_addrOk _ haok).1 $$ Ht
    · iintro Ht
      iapply Hk
      iapply (lisToks_addrOk _ haok).2 $$ Ht
  iapply fupd_wp
  imod (lisInv_alloc ⊤ _ l (serverAddrs.getD (j - 1) go!"") true) $$ Hnl with #Hlinv
  imodintro
  ihave #Hon := netLisAt_on _ l _ $$ Hla
  wp_apply wp_fork $$ []
  · wp_apply (wp_Accept srv γs hraftCodec K.W (serverAddrs.getD (j - 1) go!"") lv l) $$ []
    · iframe #
      isplitr; · ipureintro; exact Hb.2
      isplitr; · iapply net.rpc.isServerO_any $$ Hsrv
      imodintro
      iintro %a ⟨%hok, %hacc⟩
      have ha : a = serverAddrs.getD (j - 1) go!"" := ((lisAccepts_addrOk haok).1 hacc).symm
      subst ha
      isplitr
      · unfold net.rpc.rpcAddr
        iapply net.rpc.rpcLisP_addrOk _ _ _ _ haok $$ Hlp
      · unfold net.rpc.srvServes
        iintro !> %svc %S %HS
        have h := hss j svc hj1 hj2
        rw [HS] at h
        by_cases hr : svc = svcName
        · rw [if_pos hr] at h
          cases h
          subst hr
          iframe Hreg1
          unfold raftSvcK
          iapply svcK_errOk $$ []
          iintro !> %m
          iapply raftSvc_errOk
        · rw [if_neg hr] at h
          by_cases ha : svc = go!"API"
          · rw [if_pos ha] at h
            cases h
            subst ha
            iframe Hreg2
            unfold apiSvcK
            iapply svcKE_errOk K.γc apiArgsOk _ n $$ [Hc]
            iframe Hc
            iapply apiSvc_errOk
          · rw [if_neg ha] at h
            cases h
    itrivial
  wp_for
  wp_apply time.wp_Sleep
  wp_for_post
  iframe

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
