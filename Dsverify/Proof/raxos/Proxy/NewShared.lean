/-
Package `proxy`: `NewProxy`'s shared state (`proxyShared`) from the fields of the new proxy
(`np_sharedNet`, `np_shared`).
-/
module

public import Dsverify.Proof.raxos.Proxy.NewOwn

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

variable [raxos.replica.src.Assumptions]

/-- The network side: the accept routine's invariant, the writers' mutex, the tables. -/
theorem np_sharedNet (γ : QNames) (k : Nat) (pr rm wm bmm cm rt rp1 cb0 : Loc) (γw : w64 → GName)
    (BM : GMap w64 Loc) (CM : GMap w64 GoString) (RT : GMap w8 Loc)
    (hBM : ∀ c : Nat, c < 6 → (BM !! W64 (21 + c)).isSome)
    (hCM : ∀ c : Nat, c < 6 → CM !! W64 (21 + c) = some (clientAddr c))
    (hRT : RT !! W8 1 = some rp1) :
    ⊢ pr.[Proxy, go!"serverAddress"] ↦□ (go!"0.0.0.0:" ++ decStr (7606 + k)) -∗
      pr.[Proxy, go!"incomingClientReaders"] ↦□ rm -∗
      pr.[Proxy, go!"Listener"] ↦ GoInterface.nil -∗ rm ↦$ (∅ : GMap w64 Loc) -∗
      pr.[Proxy, go!"outgoingClientWriters"] ↦□ wm -∗
      pr.[Proxy, go!"clientWritersMutex"] ↦ zero_val sync.Mutex -∗ wm ↦$ (∅ : GMap w64 Loc) -∗
      pr.[Proxy, go!"buffioWriterMutexes"] ↦□ bmm -∗ bmm ↦$□ BM -∗
      ([∗map] p ↦ mu ∈ BM, sync.isMutex mu (peerR (GF := GF) γ k (cOf p) (γw p))) -∗
      pr.[Proxy, go!"clientAddrList"] ↦□ cm -∗ cm ↦$□ CM -∗
      pr.[Proxy, go!"rpcTable"] ↦□ rt -∗ rt ↦$□ RT -∗
      rp1 ↦□ (raxos.common.RPCPair.mk (W8 1)
        (interface.mkOk (go.GoType.PointerType raxos.proto.client.ClientBatch.ty) #cb0)) -∗
      |={⊤}=> sharedNet γ k pr := by
  iintro #Hsa #Hrm Hl HM #Hwm Hmu HW #Hbmm #HBM #Hmus #Hcm #HCM #Hrt #HRT #Hrp1
  imod netOwn_inv_alloc γ k pr rm GoInterface.nil ⊤ $$ Hl HM with #Hinv
  imod sync.init_Mutex (writersR γ k BM γw wm) ⊤ _ $$ Hmu [HW] with #Hwmu
  · inext; unfold writersR; iexists ∅; iframe HW
    iapply BigSepM.bigSepM_empty.2; iempintro
  imodintro
  unfold sharedNet
  iexists rm, wm, bmm, cm, rt, rp1, cb0, BM, γw, CM, RT
  iframe #
  ipureintro; exact ⟨hBM, hCM, hRT⟩

/-- A channel field. -/
theorem np_chanField {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
    (t : go.GoType) [IntoValTyped (GF := GF) V t] (pr : Loc) (f : GoString) (P : V → IProp GF)
    (ch : Loc) (g : ChanNames) :
    pr.[Proxy, f] ↦□ ch ∗ isChanBag g ch P ⊢ chanField t pr f P := by
  iintro ⟨#H1, #H2⟩
  unfold chanField
  iexists ch, g
  iframe #

/-- The new proxy's shared state. -/
theorem np_shared [hs : raxos.replica.src.Assumptions] (γ : QNames) (c : QConf) (k : Nat)
    (pr : Loc) (γs : GName) (cb bm ebm : Loc) (hk : c.ok ∧ 1 ≤ k ∧ k ≤ c.n) :
    ⊢ inv consN (consInv γ) -∗ inv smrN (smrInv γ) -∗ netProtos γ -∗
      batchReg γ go!"nil" nilBatch -∗ spentLb γ 0 -∗
      confIs γ c -∗
      sharedConsts c k pr -∗
      pr.[Proxy, go!"clientBatchStore"] ↦□ cb -∗ isStoreDef γ γs cb -∗
      pr.[Proxy, go!"benchmark"] ↦□ bm -∗ pr.[Proxy, go!"executedBatches"] ↦□ ebm -∗
      sharedChans γ k pr -∗ sharedLoop γ k pr -∗ sharedNet γ k pr -∗
      proxyShared (GF := GF) γ c k pr := by
  iintro #Hcons #Hsmr #Hnet #Hnil #Hspent #Hconf #Hconsts #Hcb #Hst #Hbm #Hebm #Hch #Hloop #Hsn
  unfold proxyShared proxySharedDef
  iexists hs, γs, cb, bm, ebm
  iframe #
  unfold sharedFacts sharedStore
  iframe #
  ipureintro; exact hk

end proofs

end Perennial.raxos
