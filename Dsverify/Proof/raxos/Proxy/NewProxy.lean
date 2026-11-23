/-
Package `proxy`: `NewProxy`'s proof (`NewProxy.spec`): the struct literal, the genesis slot, the
configuration's loops (client addresses, writer mutexes, server address), the genesis batch in the
store, the RPC table; the state from `np_own` (`NewOwn.lean`) and `np_shared` (`NewShared.lean`).
-/
module

public import Dsverify.Proof.raxos.Proxy.NewShared
public import Dsverify.Proof.raxos.Proxy.Defs
public import Dsverify.Proof.raxos.Hyp
public import Perennial.Proof.time.Link
public import Perennial.Proof.time.Results
public import Dsverify.Proof.raxos.Hyp

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

set_option goose.wp.extras true

set_option maxHeartbeats 2000000 in
/-- `NewProxy(...)` (`NewProxy.spec`). -/
theorem newProxy_proof
    [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions] [ha : hyp.AtoiSpec GF] [hu : hyp.UtcHyp GF] [hr : hyp.RandHyp GF] :
    NewProxy.spec (GF := GF) (hG := hG) := by
  intro γ c k cv toProp fromProp fromRec toFetch fromFetch toDec γ1 γ2 γ3 γ4 γ5 γ6 srv cb γs logPath
  simp only [callV, List.foldl_cons, List.foldl_nil]
  wp_start as ⟨%Hk, #Hconf, Hcv, #Hb1, #Hb2, #Hb3, #Hb4, #Hb5, #Hb6, #Hst, Hfront, #Hcons,
    #Hsmr, #Hnet, #Hnil, #Hspent⟩
  iapply wp_fupd
  imod ghost_map_alloc_empty (K := Int) (V := Unit) with ⟨%γq, Hγq⟩
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := GoString)) as %cm Hcm
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %rm Hrm
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %wm Hwm
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %bmm Hbmm
  wp_apply (wp_map_make1 (K := w8) (V := Loc)) as %rt Hrt
  wp_apply (wp_make_bag_n (V := raxos.common.RPCPair) (incomingP γ) (W64 1000000) (by word)) as %inc ⟨%γi, #Hinc⟩
  wp_apply (wp_make_bag_n (V := raxos.common.OutgoingRPC) (outP γ) (W64 1000000) (by word)) as %outc ⟨%γo, #Houtc⟩
  wp_apply (wp_slice_make2 (V := Slot) (W64 0)) as %rl ⟨Hrl, Hrlc⟩
  · ipureintro; word
  wp_apply wp_time_Now as %t1 -
  wp_apply (wp_slice_make2 (V := GoString) (W64 0)) as %tb ⟨Htb, Htbc⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := w64) (W64 0)) as %ls ⟨Hls, Hlsc⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := w32) (W64 0)) as %ps ⟨Hps, Hpsc⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := GoSlice) (W64 0)) as %ds ⟨Hds, Hdsc⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := Loc) (W64 1000000)) as %its ⟨Hits, Hitsc⟩
  · ipureintro; word
  wp_apply (wp_make_bag_n (V := ProposeRequestIndex) (reqIdxP γq) (W64 10000) (by word)) as %pri ⟨%γpri, #Hpri⟩
  wp_apply wp_time_Now as %t2 -
  wp_apply (wp_slice_make2 (V := EpochTime) (W64 0)) as %et ⟨Het, Hetc⟩
  · ipureintro; word
  wp_apply (wp_make_bag_n (V := ClientBatchTime) (fun v => cbReqP γ v.batch') (W64 100000) (by word)) as %cbt ⟨%γcbt, #Hcbt⟩
  wp_apply wp_Init_0 as %bm ⟨%kvm, #Hbmode, #HbkeyLen, #HbKV, Hkvm⟩
  wp_apply (wp_make_bag_n (V := raxos.proto.client.ClientBatch) (cbReqP γ) (W64 100000) (by word)) as %crc ⟨%γcrc, #Hcrc⟩
  wp_apply (wp_map_make1 (K := GoString) (V := Bool)) as %ebm Hebm
  iStructNamed pr
  irename : ("_" ∷ (True : IProp GF)) => Hjunk
  iclear Hjunk
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) [go!"nil"]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %pb ⟨Hpb, -⟩
  wp_pures
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) [go!"nil"]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %db ⟨Hdb, -⟩
  iunfold cfgVal at Hcv
  icases Hcv with ⟨#Hpeers, #Hclients⟩
  ihave %Hplen := ownSlice_len $$ Hpeers
  ihave %Hclen := ownSlice_len $$ Hclients
  have Hpl : (peersCfg c.n).length = c.n := by simp [peersCfg]
  have Hcn : c.n ≤ 5 := by rcases Hk.1.1 with h | h <;> omega
  have Hcl : clientsCfg.length = 6 := rfl
  wp_pures
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType Slot.ty))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := Slot) (t := Slot.ty) [_]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  wp_apply wp_slice_append (V := Slot) _ _ _ _ _ $$ [$Hrl $Hrlc $Hsl1] as %rl' ⟨Hrl, Hrlc, -⟩
  ihave HI : (∃ (i : w64) (M : GMap w64 GoString), "i" ∷ i_ptr ↦ i ∗ "Hcm" ∷ cm ↦$ M ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ 6 ∧
        ∀ c : Nat, c < sint.nat i → M !! W64 (21 + c) = some (clientAddr c)⌝ : IProp GF)
      $$ [i Hcm]
  · iexists _, _; iframe; ipureintro
    refine ⟨by word, by word, ?_⟩
    intro c hc; simp at hc; omega
  wp_for HI
  have Hc6 : sint.Z cv.Clients'.len = 6 := by rw [Hcl] at Hclen; word
  wp_if_destruct
  · have Hif' : sint.Z i < 6 := by rw [Hc6] at Hif; simpa using Hif
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z cv.Clients'.len := ⟨Hi.1, by omega⟩
    have Hi6 : sint.nat i < 6 := by word
    have Hlk : clientsCfg[sint.nat i]? =
        some ⟨decStr (21 + sint.nat i), ipOf (1 + sint.nat i), decStr (7601 + sint.nat i)⟩ := by
      simp [clientsCfg, Hi6]
    simp only [Hb, _root_.and_self, ↓reduceIte]
    icases ownSlice_elem_acc (sint.Z i) _ cv.Clients' _ clientsCfg Hi.1 Hlk $$ Hclients
      with ⟨#He, -⟩
    iStructNamedPrefix He "E"
    wp_auto
    have Hds := np_decStr_client (sint.nat i) Hi6
    wp_apply ha.Atoi _ Hds.1
    rw [Hds.2]
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_auto
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_auto
    wp_apply wp_mapInsert $$ Hcm as Hcm
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    intro c hc
    rw [GMap.lookup_insert_eq_iff]
    split
    · rename_i h
      have hc' : c = sint.nat i := by
        have := (w64_21_inj (sint.nat i) c Hi6 (by word)).1 (by push_cast at h ⊢; exact h)
        omega
      subst hc'
      rw [np_clientAddr]
    · rename_i h
      have hci : c ≠ sint.nat i := by
        intro e; subst e; apply h; push_cast; rfl
      exact Hi.2.2 c (by word)
  have HCM6 : ∀ c : Nat, c < 6 → M !! W64 (21 + c) = some (clientAddr c) :=
    fun c hc => Hi.2.2 c (by word)
  ihave HI : (∃ (i : w64) (M : GMap w64 Loc) (γw : w64 → GName), "i" ∷ i_ptr ↦ i ∗
      "Hbmm" ∷ bmm ↦$ M ∗
      "#HM" ∷ ([∗map] p ↦ mu ∈ M, sync.isMutex mu (peerR γ k (cOf p) (γw p))) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ 6 ∧
        (∀ c : Nat, c < sint.nat i → (M !! W64 (21 + c)).isSome) ∧
        (∀ p, (M !! p).isSome → ∃ c : Nat, c < sint.nat i ∧ p = W64 (21 + c))⌝ : IProp GF)
      $$ [i Hbmm]
  · iexists _, _, (fun _ => default); iframe
    isplitl []
    · iapply BigSepM.bigSepM_empty.2; itrivial
    ipureintro
    refine ⟨by word, by word, ?_, ?_⟩
    · intro c hc; simp at hc; omega
    · intro p hp; simp at hp
  wp_for HI
  wp_if_destruct
  · have Hif' : sint.Z i < 6 := by rw [Hc6] at Hif; simpa using Hif
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z cv.Clients'.len := ⟨Hi.1, by omega⟩
    have Hi6 : sint.nat i < 6 := by word
    have Hlk : clientsCfg[sint.nat i]? =
        some ⟨decStr (21 + sint.nat i), ipOf (1 + sint.nat i), decStr (7601 + sint.nat i)⟩ := by
      simp [clientsCfg, Hi6]
    simp only [Hb, _root_.and_self, ↓reduceIte]
    icases ownSlice_elem_acc (sint.Z i) _ cv.Clients' _ clientsCfg Hi.1 Hlk $$ Hclients
      with ⟨#He, -⟩
    iStructNamedPrefix He "E"
    wp_auto
    have Hds := np_decStr_client (sint.nat i) Hi6
    wp_apply ha.Atoi _ Hds.1
    rw [Hds.2]
    irename «$r0» => Hmu
    generalize «$r0_ptr» = mu at *
    imod peerR_alloc γ k (sint.nat i) with ⟨%γp, HR⟩
    imod sync.init_Mutex (peerR γ k (sint.nat i) γp) ⊤ mu $$ Hmu [HR] with #Hmux
    · inext; iexact HR
    wp_apply wp_mapInsert $$ Hbmm as Hbmm
    wp_for_post
    iframe
    rw [show (((21 + sint.nat i : Nat)) : Int) = 21 + ((sint.nat i : Nat) : Int) by push_cast; rfl]
    have Hkey : ∀ c : Nat, c < sint.nat i → W64 (21 + (c : Int)) ≠ W64 (21 + ((sint.nat i : Nat) : Int)) := by
      intro c hc e
      have := (w64_21_inj c (sint.nat i) (by omega) Hi6).1 e
      omega
    have Hnone : M !! W64 (21 + ((sint.nat i : Nat) : Int)) = none := by
      cases h : M !! W64 (21 + ((sint.nat i : Nat) : Int)) with
      | none => rfl
      | some _ =>
        obtain ⟨c, hc, he⟩ := Hi.2.2.2 _ (by rw [h]; rfl)
        exact absurd he.symm (Hkey c hc)
    iexists _, _, (fun p => if p = W64 (21 + ((sint.nat i : Nat) : Int)) then γp else γw p)
    iframe
    isplitl []
    · iapply (BigSepM.bigSepM_insert (show PartialMap.get? M _ = none from Hnone)).2
      isplitl []
      · simp only [↓reduceIte]
        rw [show cOf (W64 (21 + ((sint.nat i : Nat) : Int))) = sint.nat i from by
          have := cOf_peer (sint.nat i) Hi6; push_cast at this ⊢; exact this]
        iexact Hmux
      iapply (BigSepM.bigSepM_mono (Φ := fun p mu => sync.isMutex (GF := GF) mu (peerR γ k (cOf p) (γw p))) ?_) $$ HM
      intro p mu hp
      obtain ⟨c, hc, he⟩ := Hi.2.2.2 p (by rw [show M !! p = some mu from hp]; rfl)
      subst he
      simp only [Hkey c hc, ↓reduceIte]
      exact .rfl
    ipureintro
    refine ⟨by word, by word, ?_, ?_⟩
    · intro c hc
      rw [GMap.lookup_insert_is_Some]
      by_cases hci : c = sint.nat i
      · left; subst hci; push_cast; rfl
      · right
        refine ⟨fun e => Hkey c (by word) ?_, Hi.2.2.1 c (by word)⟩
        · push_cast at e ⊢; exact e.symm
    · intro p hp
      rw [GMap.lookup_insert_is_Some] at hp
      rcases hp with e | ⟨-, hp⟩
      · exact ⟨sint.nat i, by word, by subst e; push_cast; rfl⟩
      · obtain ⟨c, hc, he⟩ := Hi.2.2.2 p hp
        exact ⟨c, by word, he⟩
  · have Hge : 6 ≤ sint.Z i := by
      have : ¬ (sint.Z i < 6) := by rw [Hc6] at Hif; simpa using Hif
      omega
    have HBM6 := fun (c : Nat) (hc : c < 6) => Hi.2.2.1 c (by word)
    ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i + 1 ≤ k⌝ : IProp GF)
      $$ [i]
    · iexists _; iframe; ipureintro; constructor <;> word
    wp_for HI
    wp_if_destruct
    · have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z cv.Peers'.len := ⟨Hi.1, by word⟩
      have Hj : sint.nat i < c.n := by word
      have Hpc_lookup : (peersCfg c.n)[sint.nat i]? =
          some ⟨decStr (sint.nat i + 1), ipOf (sint.nat i + 1), decStr (7606 + (sint.nat i + 1)),
            decStr (7626 + (sint.nat i + 1))⟩ := by
        simp [peersCfg, Hj]
        rw [Nat.add_comm]; repeat' constructor
      simp only [Hb, _root_.and_self, ↓reduceIte]
      icases ownSlice_elem_acc (sint.Z i) _ cv.Peers' _ (peersCfg c.n) Hi.1 Hpc_lookup $$ Hpeers
        with ⟨#He, -⟩
      iStructNamedPrefix He "E"
      wp_auto
      have Hds := np_decStr_small (sint.nat i + 1) (by omega) (by omega)
      wp_apply ha.Atoi (decStr (sint.nat i + 1)) Hds.1
      rw [Hds.2]
      wp_if_destruct
      · simp only [Hb, _root_.and_self, ↓reduceIte]
        wp_auto
        wp_for_post
        ihave #Hrep := np_repCB_nil (GF := GF)
          ⟨zeroValDef, 0, slice.nil, W64 (-1), slice.nil, go!"nil"⟩ rfl rfl rfl rfl
        wp_apply store_add_proof γ γs cb _ nilBatch $$ [$Hst $Hrep] as #HsHas
        · isplitl
          · rw [show nilBatch.id = go!"nil" from rfl]; iexact Hnil
          · ipureintro; exact np_nilBatch_ok
        wp_alloc cb0 as Hcb0
        wp_auto
        ipersist rpcTable
        wp_apply wp_RegisterRPC pr_ptr rt ∅ _ (W8 1) $$ [$rpcTable $Hrt] as %rp1 ⟨Hrt, Hrp1⟩
        wp_alloc cs0 as Hcs0
        wp_auto
        wp_apply wp_RegisterRPC pr_ptr rt _ _ (W8 2) $$ [$rpcTable $Hrt] as %rp2 ⟨Hrt, Hrp2⟩
        wp_apply wp_time_Now as %t3 -
        wp_apply hu.UTC as %t4 -
        wp_apply time.Time.wp_UnixNano as %sd -
        wp_apply hr.Seed
        have Hnr : cv.Peers'.len = W64 c.n := by rw [Hpl] at Hplen; word
        rw [Hnr]
        have Hki : sint.nat i + 1 = k := by
          have h := Hk.2.2; have h2 := Hi.2; have h3 := Hif; word
        rw [Hki]
        ipersist name; ipersist clientBatchRpc; ipersist batchSize; ipersist pipelineLength
        ipersist leaderMode; ipersist leaderTimeout; ipersist epochSize
        ipersist clientBatchStore; ipersist benchmark; ipersist executedBatches
        ipersist outgoingMessageChan; ipersist proxyToProposerFetchChan; ipersist proxyToProposerChan
        ipersist recorderToProxyChan; ipersist proxyToProposerDecisionChan; ipersist incomingChan
        ipersist clientBatchTimer; ipersist clientRequestsChan; ipersist proposerToProxyChan
        ipersist proposerToProxyFetchChan; ipersist requestPropogationTime
        ipersist proposeRequestIndex; ipersist numReplicas; ipersist batchTime
        ipersist serverAddress; ipersist incomingClientReaders; ipersist outgoingClientWriters
        ipersist buffioWriterMutexes; ipersist clientAddrList
        ipersist Hbmm; ipersist Hcm; ipersist Hrt; ipersist Hrp1
        ipersist Hls; ipersist Hps; ipersist Hds; ipersist Hdb
        imod np_sharedNet γ k pr_ptr rm wm bmm cm rt rp1 cb0 γw _ _
          (<[W8 2 := rp2]> (<[W8 1 := rp1]> ∅)) HBM6 HCM6 (by simp)
          $$ serverAddress incomingClientReaders Listener Hrm outgoingClientWriters
            clientWritersMutex Hwm buffioWriterMutexes Hbmm HM clientAddrList Hcm rpcTable Hrt Hrp1
          with #Hsn
        ihave #Hconsts : sharedConsts c k pr_ptr $$ []
        · unfold sharedConsts; iframe #
        ihave #Hchans : sharedChans γ k pr_ptr $$ []
        · unfold sharedChans
          isplitr
          · iapply np_chanField _ _ _ _ outc γo; iframe #
          isplitr
          · iapply np_chanField _ _ _ _ toFetch γ4; iframe #
          isplitr
          · iapply np_chanField _ _ _ _ toProp γ1; iframe #
          isplitr
          · iapply np_chanField _ _ _ _ fromRec γ3; iframe #
          · iapply np_chanField _ _ _ _ toDec γ6; iframe #
        ihave #Hloop : sharedLoop γ k pr_ptr $$ []
        · unfold sharedLoop
          iexists inferInstance
          isplitr
          · iapply np_chanField _ _ _ _ inc γi; iframe #
          isplitr
          · iapply np_chanField _ _ _ _ cbt γcbt; iframe #
          isplitr
          · iapply np_chanField _ _ _ _ crc γcrc; iframe #
          isplitr
          · iapply np_chanField _ _ _ _ fromProp γ2; iframe #
          isplitr
          · iapply np_chanField _ _ _ _ fromFetch γ5; iframe #
          · iexists _; iframe #
        iunfold isStore at Hst
        ihave #Hsh := np_shared γ c k pr_ptr γs cb bm ebm Hk $$ Hcons Hsmr Hnet Hnil Hspent
          Hconf Hconsts clientBatchStore Hst benchmark executedBatches Hchans Hloop Hsn
        rw [show List.replicate 0 (zero_val w64) = ([] : List w64) from rfl,
          show List.replicate 0 (zero_val w32) = ([] : List w32) from rfl,
          show List.replicate 0 (zero_val GoSlice) = ([] : List GoSlice) from rfl,
          show List.replicate 0 (zero_val GoString) = ([] : List GoString) from rfl,
          show List.replicate 0 (zero_val Slot) = ([] : List Slot) from rfl, List.nil_append]
        ihave Hdec := np_decState γ pr_ptr ls ps ds $$ lastDecidedIndexes lastDecidedProposers
          lastDecidedDecisions Hls Hps Hds Hlsc Hpsc Hdsc
        ihave Hprop := np_ownProp γ k pr_ptr γq pri γpri its t2 (W64 0) $$ proposeRequestIndex Hpri
          Hγq instanceTimeouts Hits lastTimeProposed batchTime
        ihave Hep : epochOwn pr_ptr $$ [epochTimes Het Hetc]
        · unfold epochOwn; iexists _, _; iframe
        iunfold storeHas at HsHas
        rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.string #(go!"nil"))] = 1
          from rfl]
        imod np_own γ c k pr_ptr γq γs cb bm ebm kvm rl'
          ⟨slice.mk pb (W64 1) (W64 1), slice.mk db (W64 1) (W64 1), true, true, W32 1, W64 0⟩
          (slice.mk db (W64 1) (W64 1)) tb t1 rfl rfl
          $$ Hst HsHas clientBatchStore benchmark executedBatches replicatedLog Hrl Hrlc Hdb
            committedIndex lastTimeCommitted Hbmode HbkeyLen HbKV Hkvm Hebm Hnil lastProposedIndex
            Hfront toBeProposed Htb Htbc Hdec Hep Hprop with Hown
        imodintro
        iapply HΦ
        iframe Hown Hsh
      · wp_for_post
        iframe
        iexists _; iframe; ipureintro
        have : k ≠ sint.nat i + 1 := by intro h; apply Hif; rw [h]
        constructor <;> word
    · exfalso; clear HBM6 HCM6; word

end proofs

end Perennial.raxos
