/-
Package `replica`: `server.go` (`Server.Run`, `Server.NetworkInit`, `Server.StartProposers`,
`raxos.New`).

Changed against the lab: the proxy's entry points (`NewProxy`, `Proxy.NetworkInit`, `Proxy.Run`)
are premises (`NewProxy.spec`, ...; package `proxy` proves them, `Proxy/`); the recorder's address
is the wildcard `recLis k` and its protocols `netProtos`' `recLisP` (`Replica/Serve.lean`); the
peers' names come from the `strconv.Atoi` hypothesis (`hyp.AtoiSpec`, proved), their dials from the gRPC
hypotheses (`Dial`'s error case excluded by `WithInsecure`'s credentials, the lab's `dialPost`);
the batch store's allocation gives its `sync.Map` field's points-to over the deployment's
vocabulary (`StoreInst.lean`) and `isStore_alloc_proof` (`MapHyp qv.map`).
-/
module

public import Dsverify.Proof.raxos.Replica.Serve
public import Dsverify.Proof.raxos.Proposer.Run
public import Dsverify.Proof.raxos.Proxy.Store
public import Dsverify.Proof.raxos.LibDeps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace Perennial.raxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src
open hyp.sync (MapVocab MapHyp)

/-- A valid configuration has at most 5 replicas. -/
theorem QConf.n_le5 {c : QConf} (h : c.ok) : c.n ≤ 5 := by
  rcases h.1 with h | h <;> omega

/-- The configured replicas: replica `j + 1` at position `j`. -/
theorem peersCfg_get [GooseExts] (n j : Nat) (h : j < n) :
    (peersCfg n)[j]? = some ⟨decStr (j + 1), ipOf (j + 1), decStr (7606 + (j + 1)),
      decStr (7626 + (j + 1))⟩ := by
  simp [peersCfg, h, Nat.add_comm]

theorem peersCfg_length [GooseExts] (n : Nat) : (peersCfg n).length = n := by
  simp [peersCfg]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]

attribute [local instance] hyp.qpCodec

variable [gh : hyp.grpc.GrpcHyp qv.grpc] [hr : hyp.RandHyp GF] [ha : hyp.AtoiSpec GF]
variable [QpPrintfDeps GF] [QpNetDeps GF]

-- the generated `sync.Map`/`ClientBatchStore` instances are `sorry` (`StoreInst.lean`)
attribute [-instance] Perennial.raxos.replica.src.ClientBatchStore.typed_pointsto'ClientBatchStore
  Perennial.raxos.replica.src.ClientBatchStore.into_val_typed'ClientBatchStore
  Perennial.raxos.replica.src.ClientBatchStore.access_load'ClientBatchStore'clientBatches
  Perennial.raxos.replica.src.ClientBatchStore.access_store'ClientBatchStore'clientBatches
  Perennial.sync.Map.typed_pointsto'Map Perennial.sync.Map.into_val_typed'Map
  Perennial.internal.sync.HashTrieMap.typed_pointsto'HashTrieMap
  Perennial.internal.sync.HashTrieMap.into_val_typed'HashTrieMap

set_option goose.wp.extras true

theorem wp_Server_Run (hRun : Proxy.Run.spec (GF := GF) (hG := hG)) :
    Server.Run.spec (GF := GF) (hG := hG) := by
  intro γ c k s
  wp_start as Hs
  unfold serverProp srvProxy
  icases Hs with ⟨%pr, #Hpr, Hown, #Hsh⟩
  wp_auto
  wp_apply hRun γ c k pr $$ [$Hown $Hsh]
  iapply HΦ; itrivial

theorem netProtos_recLis (γ : QNames) (k : Nat) (hk : 1 ≤ k ∧ k ≤ 5) :
    netProtos (GF := GF) γ ⊢ recLisP qv.grpc (world γ) k := by
  iintro #Hnet
  iunfold netProtos at Hnet
  icases Hnet with ⟨-, -, -, -, -, -, Hg⟩
  iapply (BigSepL.bigSepL_lookup (Φ := fun _ (r : Nat) => recLisP qv.grpc (world γ) r)
    (i := k - 1) (x := k)
    (by obtain ⟨h1, h5⟩ := hk
        rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega)
          with rfl | rfl | rfl | rfl | rfl <;> rfl)) $$ Hg

theorem netProtos_grpc (γ : QNames) (k : Nat) (hk : 1 ≤ k ∧ k ≤ 5) :
    netProtos (GF := GF) γ ⊢ hyp.grpc.grpcAddr qv.grpc (world γ) (recAddr k) := by
  iintro #Hnet
  ihave #H := netProtos_recLis γ k hk $$ Hnet
  iapply recLisP_grpcAddr _ _ k hk $$ H

theorem wp_Server_NetworkInit (hNI : Proxy.NetworkInit.spec (GF := GF) (hG := hG)) :
    Server.NetworkInit.spec (GF := GF) (hG := hG) := by
  intro γ c k s
  wp_start as Hs
  unfold serverNew srvProxy srvProposers srvRecorder
  icases Hs with ⟨⟨%pr, #Hpr, Hown, #Hsh⟩, ⟨#Hc, Hpi⟩, ⟨%re, %c0, #Hre, Hconn, #Haddr, #Hrec,
    Hptok⟩⟩
  ihave #Hc' := Hc
  iunfold srvConsts at Hc'
  icases Hc' with ⟨%cv, %toProp, %fromProp, %toFetch, %fromFetch, %toDec, %γ1, %γ2, %γ4, %γ5, %γ6,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hnet, -, %Hk⟩
  have Hk5 : 1 ≤ k ∧ k ≤ 5 := ⟨Hk.2.1, Nat.le_trans Hk.2.2 (QConf.n_le5 Hk.1)⟩
  wp_auto
  ihave #Hlis := netProtos_recLis γ k Hk5 $$ Hnet
  wp_apply hNI γ c k pr $$ [$Hsh $Hptok]
  wp_apply wp_Recorder_NetworkInit γ k re c0 $$ [$Hconn $Haddr $Hrec $Hlis]
  iapply HΦ
  unfold serverNet srvProxy srvProposers
  iframe
  iframe #

/-- The peers built so far: `peersP`'s body for the first `ps.length` replicas. -/
def peersAcc (γ : QNames) (ps : List peer) : IProp GF :=
  iprop([∗list] j ↦ p ∈ ps, ⌜sint.Z p.name' = j + 1⌝ ∗
      ∃ (l cc : Loc), ⌜p.client' = interface.mkOk (go.GoType.PointerType consensusClient.ty) #l⌝ ∗
        l ↦□ (consensusClient.mk
          (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #cc)) ∗
        qv.grpc.isClientConn cc (world γ) (recAddr (j + 1)))

instance peersAcc_persistent (γ : QNames) (ps : List peer) :
    Persistent (peersAcc (GF := GF) γ ps) := by unfold peersAcc; infer_instance

theorem recAddr_peer (j : Nat) :
    ipOf (j + 1) ++ go!":" ++ decStr (7626 + (j + 1)) = recAddr (j + 1) := by
  unfold ipOf recAddr portAddr; simp only [List.append_assoc]; rfl

theorem wp_setupgRPC (γ : QNames) (c : QConf) (k : Nat) (s : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ srvConsts γ c k s }}
      (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"setupgRPC")) (Val #()))
    {{ (peers : GoSlice), RET #peers; ∃ ps, peers ↦* ps ∗ ⌜ps.length = c.n⌝ ∗ peersAcc γ ps }} := by
  wp_start as #Hc
  iunfold srvConsts at Hc
  icases Hc with ⟨%cv, %toProp, %fromProp, %toFetch, %fromFetch, %toDec, %γ1, %γ2, %γ4, %γ5, %γ6,
    -, #Hcfg, #Hcv, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hcons, #Hsmr, #Hnet,
    -, %Hk⟩
  have Hn5 := QConf.n_le5 Hk.1
  iunfold cfgVal at Hcv
  icases Hcv with ⟨#Hpeers, -⟩
  ihave %Hplen := ownSlice_len $$ Hpeers
  rw [peersCfg_length] at Hplen
  wp_auto
  wp_apply (wp_slice_make2 (V := peer) _) as %sl ⟨Hsl, Hcap⟩
  · ipureintro; word
  iStructNamedPrefix Hcfg "C"
  wp_auto
  ihave HI : (∃ (i : w64) (psl : GoSlice) (ps : List peer)
      (pv : raxos.configuration.ReplicaInstance),
      "i" ∷ i_ptr ↦ i ∗ "peeri" ∷ peeri_ptr ↦ pv ∗ "peers" ∷ peers_ptr ↦ psl ∗
      "Hsl" ∷ psl ↦* ps ∗ "Hcap" ∷ ownSliceCap peer psl (DFrac.own 1) ∗
      "#Hacc" ∷ peersAcc γ ps ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ c.n ∧ ps.length = sint.nat i⌝ : IProp GF)
      $$ [i peeri peers Hsl Hcap]
  · iexists _, _, [], _
    rw [show List.replicate 0 (zero_val peer) = ([] : List peer) from rfl]
    iframe
    isplitl []
    · unfold peersAcc; iapply BigSepL.bigSepL_nil.2; iempintro
    · ipureintro; simp; word
  wp_for HI
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z cv.Peers'.len := ⟨Hi.1, by simpa [goose_wp_simp_extra] using Hif⟩
    have Hj : sint.nat i < c.n := by word
    have Hj' : sint.nat i < (peersCfg c.n).length := by rw [peersCfg_length]; exact Hj
    list_elem (peersCfg c.n) (sint.nat i) as pc
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z i) (peersCfg c.n) _ pc Hi.1 $$ [] as -
    · iframe #; ipureintro; exact Hpc_lookup
    have Hpc : pc = ⟨decStr (sint.nat i + 1), ipOf (sint.nat i + 1),
        decStr (7606 + (sint.nat i + 1)), decStr (7626 + (sint.nat i + 1))⟩ := by
      rw [peersCfg_get _ _ Hj] at Hpc_lookup; exact (Option.some.inj Hpc_lookup).symm
    subst Hpc
    dsimp only
    rw [recAddr_peer]
    wp_apply gh.WithInsecure as %o %Ho
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType
      google_golang_org.grpc.DialOption.ty)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface)
      (t := google_golang_org.grpc.DialOption.ty) [o]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %ol ⟨Hol, -⟩
    have Hk' : 1 ≤ sint.nat i + 1 ∧ sint.nat i + 1 ≤ 5 :=
      ⟨Nat.le_add_left 1 _, Nat.succ_le_of_lt (Nat.lt_of_lt_of_le Hj Hn5)⟩
    ihave #Hg := netProtos_grpc γ (sint.nat i + 1) Hk' $$ Hnet
    wp_apply gh.Dial (world γ) (recAddr (sint.nat i + 1)) _ _ _
      $$ [$Hg $Hol] as %cc %err ⟨-, %He, #Hcc⟩
    · isplitr
      · ipureintro; exact ⟨7626 + (sint.nat i + 1), by omega, by omega, rfl⟩
      ipureintro
      exact ⟨List.cons_ne_nil _ _, fun o' ho' => by
        rw [List.mem_singleton] at ho'; subst ho'; exact Ho⟩
    rw [He]
    wp_auto
    have Hds := decStr_small (sint.nat i + 1) Hk'
    wp_apply ha.Atoi (decStr (sint.nat i + 1)) Hds.1
    rw [Hds.2]
    wp_func_call
    wp_call
    wp_auto
    wp_alloc lcl as Hlcl
    ipersist Hlcl
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType peer.ty))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := peer) (t := peer.ty) [_]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    wp_apply wp_slice_append (V := peer) _ _ _ _ _ $$ [$Hsl $Hcap $Hl1] as %psl' ⟨Hsl, Hcap, -⟩
    wp_for_post
    iframe
    iexists _, psl', _, _
    iframe
    isplitl []
    · unfold peersAcc
      iapply (BigSepL.bigSepL_snoc (Φ := fun j (p : peer) => iprop(⌜sint.Z p.name' = j + 1⌝ ∗
        ∃ (l cc : Loc), ⌜p.client' = interface.mkOk (go.GoType.PointerType consensusClient.ty) #l⌝ ∗
          l ↦□ (consensusClient.mk
            (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #cc)) ∗
          qv.grpc.isClientConn cc (world γ) (recAddr (j + 1))))).2
      iframe #
      isplitr
      · ipureintro; dsimp only; rw [Hi.2.2]; word
      isplitr
      · ipureintro; rfl
      rw [Hi.2.2]; iexact Hcc
    · ipureintro; simp only [List.length_append, List.length_singleton]; refine ⟨by word, by word, by word⟩
  · iapply HΦ
    iexists ps; iframe; iframe #
    ipureintro; rw [Hi.2.2]; word

theorem wp_createProposers
    (γ : QNames) (c : QConf) (k : Nat) (s : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ srvProposers γ c k s }}
      (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"createProposers")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hs
  unfold srvProposers
  icases Hs with ⟨#Hc, Hpi⟩
  wp_auto
  wp_apply wp_setupgRPC γ c k s $$ [$Hc] as %peers ⟨%pls, Hpl, %Hpll, #Hacc⟩
  ipersist Hpl
  ihave #Hpeers : peersP γ c.n peers $$ []
  · unfold peersP; iexists pls; iframe #
    isplitr
    · ipureintro; exact Hpll
    iunfold peersAcc at Hacc; iexact Hacc
  iunfold srvConsts at Hc
  icases Hc with ⟨%cv, %toProp, %fromProp, %toFetch, %fromFetch, %toDec, %γ1, %γ2, %γ4, %γ5, %γ6,
    #Hname, -, -, #Hnum, #HtoP, #HbtoP, #HfromP, #HbfromP, #HtoF, #HbtoF, #HfromF, #HbfromF,
    #HtoD, #HbtoD, #HdebugOn, #HdebugLevel, #HserverMode, #HisAsync, #HasyncTimeOut,
    #HtimeEpochSize, #Hcons, #Hsmr, -, #Hconf, %Hk⟩
  have Hp5 : c.pipe ≤ 5 := Hk.1.2.2.2.1
  icases Hpi with ⟨%psl, Hpis, Hpsl, Hpcap⟩
  ihave HI : (∃ (i : w64) (psl : GoSlice) (ps : List Loc), "i" ∷ i_ptr ↦ i ∗
      "Hpis" ∷ s.[Server, go!"ProposerInstances"] ↦ psl ∗ "Hpsl" ∷ psl ↦* ps ∗
      "Hpcap" ∷ ownSliceCap Loc psl (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ c.pipe + 8 ∧ ps.length = sint.nat i⌝ : IProp GF)
      $$ [i Hpis Hpsl Hpcap]
  · iexists _, _, _; iframe; ipureintro; simp; word
  wp_for HI
  wp_if_destruct
  · have hNP := prop.wp_NewProposer (GF := GF) (hG := hG) γ c k i peers toProp fromProp toFetch
      fromFetch toDec γ1 γ2 γ4 γ5 γ6
    simp only [callV, List.foldl_cons, List.foldl_nil] at hNP
    wp_apply hNP $$ [$HbtoP $HbfromP $HbtoF $HbfromF $HbtoD $Hcons $Hsmr $Hpeers $Hconf]
      as %p Hp
    · ipureintro; exact Hk
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType
      (go.GoType.PointerType Proposer.ty))))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType Proposer.ty) [p]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    wp_apply wp_slice_append (V := Loc) _ _ _ _ _ $$ [$Hpsl $Hpcap $Hl1] as %psl' ⟨Hpsl, Hpcap, -⟩
    ihave %Hlen := ownSlice_len $$ Hpsl
    have Hb : 0 ≤ sint.Z (psl'.len - W64 1) ∧ sint.Z (psl'.len - W64 1) < sint.Z psl'.len := by
      simp only [List.length_append, List.length_singleton] at Hlen; constructor <;> word
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index psl' _ (ps ++ [p]) _ p Hb.1 $$ [Hpsl] as Hpsl
    · iframe; ipureintro
      simp only [List.length_append, List.length_singleton] at Hlen
      have : (sint.Z (psl'.len - W64 1)).toNat = ps.length := by word
      rw [this]; simp
    wp_apply prop.wp_runProposer γ c k p $$ [$Hp]
    wp_for_post
    iframe
    iexists _, psl', _
    iframe
    ipureintro; simp only [List.length_append, List.length_singleton]; word
  · iapply HΦ; itrivial

theorem wp_Server_StartProposers :
    Server.StartProposers.spec (GF := GF) (hG := hG) := by
  intro γ c k s
  wp_start as Hs
  unfold serverNet
  icases Hs with ⟨Hpx, Hps⟩
  wp_auto
  wp_apply wp_createProposers γ c k s $$ [$Hps]
  iapply HΦ
  unfold serverProp; iframe

theorem wp_NewRecorder (γ : QNames) (c : QConf) (k : Nat)
    (cv : raxos.configuration.InstanceConfig) (cb : Loc) (γs : GName) (ch : Loc) (γc : ChanNames)
    (hk : c.ok ∧ 1 ≤ k ∧ k ≤ c.n) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ cfgVal c.n cv ∗ isStore γ γs cb ∗
        isChanBag γc ch (decisionP γ) ∗ recHalf γ k ∅ ∗ inv consN (consInv γ) }}
      (callV (@! raxos.replica.src.NewRecorder) [ #cv, #cb, #ch, #(W64 k), #false, #(W64 0)])
    {{ (re : Loc), RET #re; re.[Recorder, go!"connection"] ↦ null ∗
        re.[Recorder, go!"address"] ↦□ recLis k ∗
        isRecorder γ k re }} := by
  simp only [callV, List.foldl_cons, List.foldl_nil]
  wp_start as ⟨Hcv, #Hst, #Hch, Hhalf, #Hinv⟩
  unfold cfgVal
  icases Hcv with ⟨#Hpeers, #Hclients⟩
  wp_auto
  wp_apply (wp_slice_make2 (V := RecorderSlot) _) as %sl ⟨Hsl, Hcap⟩
  · ipureintro; word
  irename «$v9» => Hmu
  generalize «$v9_ptr» = mu at *
  rename_i re_ptr
  ihave %Hplen := ownSlice_len $$ Hpeers
  rw [peersCfg_length] at Hplen
  have Hn5 := QConf.n_le5 hk.1
  iapply wp_fupd
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i + 1 ≤ k⌝ : IProp GF)
    $$ [i]
  · iexists _; iframe; ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z cv.Peers'.len := ⟨Hi.1, by word⟩
    have Hj : sint.nat i < c.n := by word
    have Hj' : sint.nat i < (peersCfg c.n).length := by rw [peersCfg_length]; exact Hj
    list_elem (peersCfg c.n) (sint.nat i) as pc
    have Hpc : pc = ⟨decStr (sint.nat i + 1), ipOf (sint.nat i + 1),
        decStr (7606 + (sint.nat i + 1)), decStr (7626 + (sint.nat i + 1))⟩ := by
      rw [peersCfg_get _ _ Hj] at Hpc_lookup; exact (Option.some.inj Hpc_lookup).symm
    subst Hpc
    simp only [Hb, _root_.and_self, ↓reduceIte]
    icases ownSlice_elem_acc (sint.Z i) _ cv.Peers' _ (peersCfg c.n) Hi.1 Hpc_lookup $$ Hpeers
      with ⟨#He, -⟩
    iStructNamedPrefix He "E"
    wp_auto
    have Hk' : 1 ≤ sint.nat i + 1 ∧ sint.nat i + 1 ≤ 5 := by omega
    have Hds := decStr_small (sint.nat i + 1) Hk'
    wp_apply ha.Atoi (decStr (sint.nat i + 1)) Hds.1
    rw [Hds.2]
    wp_if_destruct
    · simp only [Hb, _root_.and_self, ↓reduceIte]
      wp_auto
      wp_for_post
      iStructNamed re
      ipersist address
      ipersist clientBatches
      ipersist recorderToProxyChan
      ipersist name
      ipersist instanceMutex
      imod sync.init_Mutex (recInv γ k re_ptr) ⊤ mu $$ Hmu [slots Hsl Hcap Hhalf] with #Hmux
      · inext
        unfold recInv
        iexists sl, [], ∅
        rw [show List.replicate 0 (zero_val RecorderSlot) = ([] : List RecorderSlot) from rfl]
        iframe
        isplitl []
        · imodintro; iintro %j %s0 %Hj; simp at Hj
        · ipureintro; intro i _; rfl
      imodintro
      iapply HΦ
      iframe
      have Hkk : sint.nat i + 1 = k := by word
      rw [Hkk]
      rw [show recLis k = go!"0.0.0.0:" ++ decStr (7626 + k) from rfl]
      iframe #
      unfold isRecorder
      iexists cb, γs, ch, γc, mu
      iframe #
      ipureintro; omega
    · wp_for_post
      iframe
      iexists _; iframe; ipureintro
      have : k ≠ sint.nat i + 1 := by intro h; apply Hif; rw [h]
      constructor <;> word
  · exfalso; word

/-- A new bag channel of capacity `10000`. -/
theorem wp_make_bag {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
    {t : go.GoType} [IntoValTyped (GF := GF) V t] (P : V → IProp GF) :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make2 [go.GoType.ChannelType go.ChanDir.sendrecv t]))
        (Val #(W64 10000)))
    {{ (ch : Loc), RET #ch; ∃ γc, isChanBag γc ch P }} := by
  iintro %Φ - HΦ
  iapply wp_fupd
  wp_apply (chan.wp_make2 (V := V) (W64 10000)) as %ch %γc ⟨#Hch, -, Hoc⟩
  · ipureintro; word
  imod start_bag P _ ch γc (by simp) $$ Hch Hoc with #Hbag
  imodintro
  iapply HΦ
  iexists γc; iexact Hbag

theorem wp_New [hMV : MapHyp qv.map] (hNP : NewProxy.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) := by
  intro γ c k cfg cv logPath
  simp only [callV, List.foldl_cons, List.foldl_nil]
  wp_start as ⟨#Hcfg, Hcv, Hres⟩
  ihave #Hcv' : cfgVal c.n cv $$ [Hcv]
  · iexact Hcv
  unfold replicaRes
  icases Hres with ⟨%Hk, #Hconf, Hptok, Hhalf, Hfront, #Hcons, #Hsmr, #Hnet, #Hnil, #Hspent⟩
  wp_auto
  wp_apply (wp_make_bag (V := ProposeRequest) (proposeReqP γ k)) as %toProp ⟨%γ1, #Hb1⟩
  wp_apply (wp_make_bag (V := ProposeResponse) (proposeRespP γ k)) as %fromProp ⟨%γ2, #Hb2⟩
  wp_apply (wp_make_bag (V := Decision) (decisionP γ)) as %fromRec ⟨%γ3, #Hb3⟩
  wp_apply (wp_make_bag (V := FetchRequest) fetchReqP) as %toFetch ⟨%γ4, #Hb4⟩
  wp_apply (wp_make_bag (V := FetchResposne) (fetchRespP γ)) as %fromFetch ⟨%γ5, #Hb5⟩
  wp_apply (wp_make_bag (V := Decision) (decisionP γ)) as %toDec ⟨%γ6, #Hb6⟩
  irename «$v11» => Hcb
  generalize «$v11_ptr» = cb at *
  iStructNamed Hcb
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.raxos.replica.src $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  icases Hdeps with ⟨-, -, -, -, -, #Hsync, -⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ clientBatches
  imod isStore_alloc_proof γ cb ⊤ Hnn $$ Hsync clientBatches with ⟨%γs, #Hst⟩
  have hNP' := hNP γ c k cv toProp fromProp fromRec toFetch
    fromFetch toDec γ1 γ2 γ3 γ4 γ5 γ6 sr_ptr cb γs logPath
  simp only [callV, List.foldl_cons, List.foldl_nil] at hNP'
  wp_apply hNP' $$ [$Hcv' $Hb1 $Hb2 $Hb3 $Hb4 $Hb5 $Hb6 $Hst $Hfront $Hcons $Hsmr $Hnet
    $Hnil $Hspent $Hconf] as %pr ⟨Hown, #Hsh⟩
  · ipureintro; exact Hk
  have hNR := wp_NewRecorder (GF := GF) (hG := hG) γ c k cv cb γs fromRec γ3 Hk
  simp only [callV, List.foldl_cons, List.foldl_nil] at hNR
  wp_apply hNR $$ [$Hcv' $Hst $Hb3 $Hhalf $Hcons] as %re ⟨Hconn, #Haddr, #Hrec⟩
  iapply wp_fupd
  wp_apply QpPrintfDeps.printf _ slice.nil [] (DFrac.own 1) as %n %e -
  · iframe #
    isplitl []
    · iapply ownSlice_nil
    · iunfold fmt.argsOk; ileft; ipureintro; simp [fmt.ArgsWf]
  iStructNamed sr
  rw [show (W64 c.pipe + W64 1 + W64 3 : w64) = W64 ((c.pipe : Int) + 4) by
    have := Hk.1.2.2.2.1; word]
  ipersist name; ipersist ProxyInstance; ipersist RecorderInstance; ipersist proxyToProposerChan
  ipersist proposerToProxyChan; ipersist proxyToProposerFetchChan; ipersist proposerToProxyFetchChan
  ipersist cfg; ipersist numProposers; ipersist serverMode; ipersist debugOn; ipersist debugLevel
  ipersist proxyToProposerDecisionChan; ipersist isAsync; ipersist asyncTimeOut
  ipersist timeEpochSize
  imodintro
  iapply HΦ
  unfold serverNew srvProxy srvProposers srvConsts srvRecorder
  isplitl [Hown]
  · iexists pr; iframe; iframe #
  isplitl [ProposerInstances]
  · isplitl []
    · iexists cv, toProp, fromProp, toFetch, fromFetch, toDec, γ1, γ2, γ4, γ5, γ6
      iframe #
      ipureintro; exact Hk
    · iexists slice.nil; iframe
      isplitl []
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
  · iexists re, null
    iframe
    iframe #
  done

end proof

end Perennial.raxos
