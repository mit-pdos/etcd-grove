/-
**The server's raft wrapper from raft's `StartNode`** (stage R8b-C of the raft v3.7 retarget,
2026-10-16; D12: `notes/decisions.md`, "The new cluster's start"): the composition that builds
`isServerBuilt`'s raft rows -- `isRaftNode`, the loop and apply tokens at `[]`, the right to close
`done`, `srvRaftLogInv` at `pre = []` -- from the new cluster's ghost allocation
(`ownRaftGhost_alloc_boot`'s output for this node), the cluster's budget, a fresh registered
`MemoryStorage`, the contracts and `bootstrappedRaft.newRaftNode`'s spec. Lean-first (no Rocq
counterpart).

**Where the wrapper lives.** `NewServer` copies the wrapper by value (`r: *b.raft.newRaftNode(...)`)
into `EtcdServer.r` and sets its `transport` afterwards (`srv.r.transport = tr`), so
`bootstrappedRaft.newRaftNode` cannot hand out `isRaftNode` at the pointer it returns: it hands out
the struct value with its components' predicates (`rnBuilt`, `InvNodeStart.lean`), and
`isRaftNode_of_rnParts` installs `isRaftNode` at the address the struct finally lives at, once the
transport is set -- the step a `NewServer` proof takes. `raftNode_of_StartNode` composes the two:
its post is the struct value, the loop's and the apply side's tokens (`rnLoopTok`/`rnApplyTok` at
`[]`, from raft's `nodeDriver` at `[]` and `applyc`'s halves), `srvRaftLogInv`, and the installer.

**The premises, classified** (the theorem's hypotheses, named as `isServerBuilt`'s rows):
* raft's results: `bootstrappedRaft.newRaftNode.spec` (through it `StartNode.spec`,
  `newRaftNode.spec`), `node.{Ready,Advance,Tick,ReadIndex}.spec` (for the node's contract,
  `isRaftNodeIfc_of_isNode`), all instantiated by the linked `wp_*` in `Results.lean`;
* the allocation's (`ownRaftGhost_alloc_boot`, `budget_alloc`, `NewMemoryStorage` registered):
  `raftCommitInv γ`, `isCommitted γ bootLog`, `ownRaftGhost γ cv.ID' (bootPState bootLog)`, the
  budget's invariant and `termLB bud 1` (`budget_alloc_boot`), `memStorReg`, `isStorage`/`ownStorage` of the fresh
  storage (`memOwnStorage_empty`, `memStorage_isStorage`);
* the server's own invariants: `rnEnvOk` (its `E.C` clauses are the KV invariant's, the
  server-construction unit's: for the wrapper names raft hands back) and `srvCommittedInv s E.γr`,
  premises of the installer (since unit N1 of the server-construction unit, 2026-10-17: `NewServer`
  evaluates `newRaftNode` inside the `EtcdServer` literal, before the server `s` exists); the names
  `E.γr.raft = ⟨γ, [], 0⟩` and the conf-change policy `srvCCPolicy` (the server's choice at the
  allocation), premises of the call;
* premises: `rnLogFits` (pure since D19b stage 5: the receipt bound past the bootstrap log, so
  raft's `Ready`s fit the `MemoryStorage`; D10 until then), `rnStopOkStarted` (D19r (A): `Stop` returns, of a started node)
  (`Stop` returns), `rnTickerOk`/`isRNTicker` (Perennial models no ticker), the `InitialState`
  closure in `StartNode.spec`'s `□` shape (a `MemoryStorage`'s `InitialState` consumes
  `memStorMeta`, which is not persistent: `MemoryStorage.InitialState.spec` cannot be the `□`
  closure; `StartNode` calls it once -- B's spec could drop the `□`), `bootMarshal` (protobuf's
  determinism at the peers' conf changes), the names-only contracts (`rnLoggerZapOk`,
  `rnSetLoggerOk`, `rnTimeoutDetectorOk`, `rnRaftStatusOk`, `rnNewStorageOk`, `rnClusterOk`,
  `isRNTransport`). Since D17d (2026-10-18) the closure borrows the storage's application
  snapshot token (`memSnapTok`, `bootOk`'s), which `StartNode` gives back (its `R`) and this
  theorem returns: `NewServer` reads `run`'s snapshot contract `rnSnapOnce ms 0 0` off it
  (`rnSnapOnce_of_tok`, `InvBoot.lean`; until then a residual premise of the construction).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedRaft__newRaftNode
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NodeBridge
public import Proof.go_etcd_io.raft.v3.MemstorageApi

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section compose
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The wrapper's fields that never change, read-only** (D21 M2, 2026-10-19): every field of
the struct at `a` but `transport` (set after the transport starts) and `latestTickTs` (`tickMu`'s
resource). Split off the struct early (`rnFixed_split`) so that the node's field is readable
(`EtcdServer.Process`) before the transport, which calls `Process`, is installed. -/
def rnFixed (a : Loc) (rv : raftNode) : IProp GF :=
  iprop("#lgR" ∷ rnLgAddr a ↦□ rv.lg' ∗ "#tickMuR" ∷ rnTickMuAddr a ↦□ rv.tickMu' ∗
    "#lgC" ∷ structFieldRef raftNodeConfig go!"lg" (rnCfgAddr a) ↦□ rv.raftNodeConfig'.lg' ∗
    "#isIDRemovedC" ∷ rnIsIDRemovedAddr a ↦□ rv.raftNodeConfig'.isIDRemoved' ∗
    "#NodeC" ∷ rnNodeAddr a ↦□ rv.raftNodeConfig'.Node' ∗
    "#raftStorageC" ∷ rnRaftStorageAddr a ↦□ rv.raftNodeConfig'.raftStorage' ∗
    "#storageC" ∷ rnStorageAddr a ↦□ rv.raftNodeConfig'.storage' ∗
    "#heartbeatC" ∷ rnHeartbeatAddr a ↦□ rv.raftNodeConfig'.heartbeat' ∗
    "#msgSnapCR" ∷ rnMsgSnapCAddr a ↦□ rv.msgSnapC' ∗ "#applycR" ∷ rnApplycAddr a ↦□ rv.applyc' ∗
    "#readStateCR" ∷ rnReadStateCAddr a ↦□ rv.readStateC' ∗ "#tickerR" ∷ rnTickerAddr a ↦□ rv.ticker' ∗
    "#tdR" ∷ rnTdAddr a ↦□ rv.td' ∗ "#stoppedR" ∷ rnStoppedAddr a ↦□ rv.stopped' ∗
    "#doneR" ∷ rnDoneAddr a ↦□ rv.done')

instance rnFixed_persistent (a : Loc) (rv : raftNode) : Persistent (rnFixed (GF := GF) a rv) := by
  unfold rnFixed; infer_instance

/-- The struct at `a`, split: its fixed fields read-only, `transport` and `latestTickTs` owned. -/
theorem rnFixed_split (a : Loc) (rv : raftNode) :
    a ↦ rv ⊢ |={⊤}=> rnFixed (GF := GF) a rv ∗
      rnTransportAddr a ↦ rv.raftNodeConfig'.transport' ∗ rnLatestTickTsAddr a ↦ rv.latestTickTs' := by
  iintro Ha
  iStructNamedSuffix Ha "R"
  iStructNamedSuffix raftNodeConfigR "C"
  ipersist lgR
  ipersist tickMuR
  ipersist lgC
  ipersist isIDRemovedC
  ipersist NodeC
  ipersist raftStorageC
  ipersist storageC
  ipersist heartbeatC
  ipersist msgSnapCR
  ipersist applycR
  ipersist readStateCR
  ipersist tickerR
  ipersist tdR
  ipersist stoppedR
  ipersist doneR
  imodintro
  iframe transportC latestTickTsR
  iunfold rnFixed
  simp only [named]
  iframe #

/-- **Installing the wrapper** (see the file header): the struct value `rv` at `a` (the server's
`r` field, after the copy and the transport set), its fresh `tickMu`, the components' predicates
and what the node and the server provide give `isRaftNode E γ a` and the right to close `done`.
A fancy update: `tickMu`'s guard over `latestTickTs` is made here (`sync.init_RWMutex`). -/
theorem isRaftNode_of_rnParts (E : RNEnv GF) (γ : RNNames) (a : Loc) (rv : raftNode) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      rnEnvOk E γ ∗ rnLogFits γ ∗ rnReadStateBridge E γ ∗
      (letI : MemStorReg GF := ⟨γ.reg⟩; memStorReg γ.ms γ.γs) ∗
      isRaftNodeIfc E γ rv.raftNodeConfig'.Node' ∗
      isRNIDRemoved rv.raftNodeConfig'.isIDRemoved' ∗
      ⌜rv.raftNodeConfig'.raftStorage' = γ.ms⌝ ∗ isRNMemStor γ γ.ms ∗
      isRNWal rv.raftNodeConfig'.storage' ∗
      isRNTransport E rv.raftNodeConfig'.transport' ∗
      rnParts E γ rv ∗
      rnFixed a rv ∗ rnTransportAddr a ↦ rv.raftNodeConfig'.transport' ∗
      rnLatestTickTsAddr a ↦ rv.latestTickTs' ∗ rv.tickMu' ↦ (zero_val sync.RWMutex) ∗
      ownBroadcastChan rv.done' γ.done iprop(True) .Pending ⊢
      |={⊤}=> isRaftNode E γ a ∗ rnDoneTok γ a ∗
        rnNodeAddr a ↦□ rv.raftNodeConfig'.Node' ∗
        rnTransportAddr a ↦□ rv.raftNodeConfig'.transport' := by
  iintro ⟨#Hpkg, #Henv, #Hfits, #Hrsb, #Hreg, #Hni, #Hidri, %Hmsγ, #Hmsi, #Hsti, #Htri, #Hparts,
    #Hfix, transportC, latestTickTsR, Hmu, Hdtok⟩
  iunfold rnParts at Hparts
  iNamed Hparts
  iunfold rnFixed at Hfix
  iNamed Hfix
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  imod sync.init_RWMutex (rnTickInv a) rv.tickMu' $$ [latestTickTsR] Hmu with Hslots
  · inext; iunfold rnTickInv; iexists rv.latestTickTs'; iexact latestTickTsR
  icases sync.ownRWMutex_slots_guard _ _ $$ Hslots with ⟨-, #Hmug⟩
  ipersist transportC
  imodintro
  isplitr
  · iunfold isRaftNode
    iexists rv.lg', rv.tickMu', rv.raftNodeConfig'.raftStorage', rv.td', rv.ticker',
      rv.raftNodeConfig'.Node', rv.raftNodeConfig'.storage', rv.raftNodeConfig'.transport',
      rv.raftNodeConfig'.isIDRemoved', rv.raftNodeConfig'.heartbeat', rv.msgSnapC', rv.applyc',
      rv.readStateC', rv.stopped', rv.done'
    simp only [named]
    iframe #
    isplitr
    · ipureintro; exact Hlgnn
    isplitr
    · ipureintro; exact Hmsγ
    rw [Hmsγ]
    iexact Hmsi
  · iframe NodeC transportC
    iunfold rnDoneTok
    iexists rv.done'
    iframe doneR Hdtok

/-- **The loop's and the apply side's tokens at the start** (`rnLoopTok γ []`, `rnApplyTok γ
[]`): from the node API's driver at its start (`NodeDriverState.init`: nothing delivered, with
`γ.pre = []`), its view of the configuration at index `0` (`StartNode`'s; 2026-10-30, the repair:
in every cluster), the loop's half of the running token, and `applyc`'s halves with `cum` at
`[[]]` (`newRaftNode`'s). (2026-10-27: over the node API.) -/
theorem rnToks_of_start (γ : RNNames) (hpre : γ.pre = [])
    (hcfg : srvCfgOk γ.node.cfg [] ⟨0, Membership.simple γ.node.cfg⟩) :
    (letI := srvStor (GF := GF) γ.node;
      iprop(nodeDriver γ.nl γ.node.cl srvClusterN
          (NodeDriverState.init (memStorIface γ.ms)) ∗
        nodeConfig γ.nl γ.node.cl srvClusterN ⟨0, Membership.simple γ.node.cfg⟩)) ∗ (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ∗
      spscProducer γ.ap ([] : List toApply) ∗ spscConsumer γ.ap ([] : List toApply) ∗
      monoListAuthOwn γ.cum 1 [([] : List EntryModel)] ∗
      monoListIdxOwn γ.cum 0 ([] : List EntryModel) ⊢
      rnLoopTok γ [] ∗ rnApplyTok γ [] := by
  letI := srvStor (GF := GF) γ.node
  iintro ⟨⟨Hdrv, Hcfg⟩, Hrun, Hprod, Hcons, Hcum, Hcum0⟩
  isplitl [Hdrv Hcfg Hrun Hprod Hcum]
  · iunfold rnLoopTok
    iexists hsZero
    iunfold rnLoopTokP
    iexists [], [[]]
    isplitl [Hdrv Hcfg]
    · iunfold rnDrv
      have h : rnDrvSt γ [] hsZero = NodeDriverState.init (memStorIface γ.ms) := by
        simp [rnDrvSt, NodeDriverState.init, srvLE, RNNames.srv, hpre]
      rw [h]
      iframe Hdrv
      unfold rnCfgAt srvCfgView
      iexists ⟨0, Membership.simple γ.node.cfg⟩
      iframe Hcfg
      ipureintro
      simp only [RNNames.srv, hpre, List.append_nil]
      exact hcfg
    iframe Hrun Hprod Hcum
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    ipureintro
    exact ⟨W64 0, by rw [hpre]; rfl, fun n m h => by simp at h⟩
  · iunfold rnApplyTok
    iexists []
    iframe Hcons
    iexact Hcum0

/-- **A fresh `MemoryStorage` boots a node** (2026-10-30, the repair: `StartNode.spec`'s
`bootStorage`, at the empty conf state and hard state, over raft's two-writer `MemoryStorage`
specs; until then the trusted `InitialState` closure and the old storage tokens): `FirstIndex` is
`1` and `LastIndex` `0` (the storage fresh: `memStorFresh_compacted`), `InitialState` answers the
zero hard state and the empty conf state (`memSnapEmpty`'s), and its update allocates the storage's
invariant at the node's justifications (`memStorInv_alloc`), the storage `isStorage`
(`memStorage_isStorage`), its dummy entry and end; the frame `Q` keeps the invariant and the hard
state. -/
theorem srvMem_bootStorage
    (wp_InitialState : MemoryStorage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (γr : SrvRaft) (ms : Loc) (γs : MemStorNames) (id : w64) :
    letI : MemStorReg GF := ⟨γr.reg⟩
    letI := srvStor (GF := GF) γr
    memStorReg ms γs ∗ memStorLock ms γs ∗ memStorFresh ms γs ∗
      memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
      memLog (GF := GF) γs 0 DFrac.discard [(zero_val EntryM : EntryM)] ∗ memEnd (GF := GF) γs 1 ⊢
      bootStorage γr.cl id (memStorIface ms) (HardStateM.mk (W64 0) (W64 0) (W64 0))
        memSnapEmpty.Metadata'.ConfState'
        iprop(memStorInv ms γs γr.cl id ∗
          memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0))) := by
  letI : MemStorReg GF := ⟨γr.reg⟩
  letI := srvStor (GF := GF) γr
  iintro ⟨#Hreg, #Hl, Hfresh, Hmeta, #Hlog, He⟩
  ihave #Hinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iunfold memStorLock at Hl; icases Hl with ⟨#H, -⟩; iexact H
  unfold bootStorage
  iexists (⟨MemoryStorage.ty.PointerType, intoVal ms⟩ : GoInterfaceOk)
  iexists iprop(memStorFresh ms γs ∗
    memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗ memEnd γs 1)
  isplitr
  · ipureintro; rfl
  isplitl [Hfresh Hmeta He]
  · iframe Hfresh Hmeta He
  isplitr
  · iintro !> %Φ ⟨Hfresh, Hmeta, He⟩ HΦ
    wp_apply wp_FirstIndex ms γs 0 $$ [$Hinit $Hl]
      as %fi ⟨%Hfi, #Hc⟩
    · iapply memCompacted_zero
    icases memStorFresh_compacted ms γs _ $$ [$Hfresh $Hc] with ⟨%H0, Hfresh⟩
    have Hfi1 : fi = W64 1 := by word
    subst Hfi1
    iapply HΦ
    iframe Hfresh Hmeta He
  isplitr
  · iintro !> %Φ ⟨Hfresh, Hmeta, He⟩ HΦ
    wp_apply wp_LastIndex ms γs 1 $$ [$Hinit $Hl $He]
      as %li ⟨He, %Hli⟩
    have Hli0 : li = W64 0 := by word
    subst Hli0
    iapply HΦ
    iframe Hfresh Hmeta He
  iintro !> %Φ ⟨Hfresh, Hmeta, He⟩ HΦ
  wp_apply wp_InitialState ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0))
    $$ [$Hinit $Hmeta $Hfresh]
    as %hp %cs ⟨#Hhs, Hmeta, Hfresh, Hcs⟩
  iapply HΦ $$ %hp %cs %true
  isplitr
  · iexact Hhs
  isplitl [Hcs]
  · have hce : memSnapEmpty.Metadata'.ConfState' = ConfStateM.mk [] [] [] [] false := rfl
    rw [hce]
    iexact Hcs
  imod memStorInv_alloc ms γs γr.cl id ⊤ $$ Hl Hfresh with #Hinv
  imodintro
  iframe Hinv
  isplitr
  · iapply memStorage_isStorage wp_LastIndex wp_FirstIndex wp_Term wp_Entries wp_Snapshot
      ms γs γr.cl id $$ Hinv Hreg
  isplitr [Hmeta]
  · iexists (zero_val EntryM)
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply memStorLog_of ms γs 0 DFrac.discard [zero_val EntryM] $$ Hreg Hlog
    iapply memStorEnd_of ms γs 1 $$ Hreg He
  iexact Hmeta
/-- **The composition's statement** (see the file header; 2026-10-27: over the node API, for the
server's raft names `γr` and the cluster's storage model `srvStor γr`): for the receiver `b` and the
config `cv` with `StartNode.spec`'s premises on it, the peers, the server's names
(`E.γr.raft = ⟨γr, [], 0⟩`) and its raft invariant (`srvRaftLogInv`, the cluster's allocation's):
`bootstrappedRaft.newRaftNode` over the node API's `StartNode`, with what the allocation, the server
and the trust boundary provide, yields the wrapper's struct value, the tokens and the installer of
`isRaftNode` at the address the server copies the struct to. -/
abbrev NodeStartSpec : Prop :=
  ∀ (γr : SrvRaft) (E : RNEnv GF) (b ss wal cl : Loc) (dq : DFrac)
    (bv : bootstrappedRaft) (cv : Config) (lok : GoInterfaceOk) (γs : MemStorNames)
    (pv : List Peer) (ps : List w64) (ctxs : List (List w8)) (issued : GName),
    -- `newRaftNode`'s premises
    bv.lg' ≠ null → bv.heartbeat' ≠ W64 0 →
    -- `NewRawNode`'s premises on `b.config`
    ConfigValid cv → cv.Logger' = interface.ok lok →
    cv.Storage' = memStorIface bv.storage' →
    sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
    cv.DisableProposalForwarding' = false → cv.ReadOnlyOption' = W64 0 →
    cv.DisableConfChangeValidation' = false →
    (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
    cv.AsyncStorageWrites' = false → cv.Applied' = W64 0 →
    -- the peers, the cluster's voters
    ps = pv.map Peer.ID' → ps ≠ [] → ps.Nodup → W64 0 ∉ ps →
    (ps.length : Int) < 2 ^ 62 → cv.ID' ∈ ps → γr.vs = ps →
    -- the time-receipt bound past the bootstrap log (`rnLogFits`)
    receiptBound GF + γr.boot.length ≤ 2 ^ 61 →
    -- the server's names: the cluster, the start log empty
    E.γr.raft.raft = γr → E.γr.raft.pre = [] → E.γr.raft.ai0 = W64 0 →
    letI : MemStorReg GF := ⟨γr.reg⟩
    letI := srvStor (GF := GF) γr
    {{ "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        -- the receiver, the config and its logger
        "Hb" ∷ b ↦{dq} bv ∗ "Hc" ∷ bv.config' ↦ cv ∗ "#Hlok" ∷ isLogger lok ∗
        -- (2026-10-30, the repair) the fresh registered `MemoryStorage`, as `NewMemoryStorage`
        -- leaves it (raft's two-writer specs): its lock, its fresh state, its hard state, its
        -- dummy entry and end; `StartNode`'s `bootStorage` over it (`srvMem_bootStorage`), whose
        -- `InitialState` allocates the storage's invariant at the node's justifications
        "#Hreg" ∷ memStorReg bv.storage' γs ∗
        "#Hlock" ∷ memStorLock bv.storage' γs ∗
        "Hfresh" ∷ memStorFresh bv.storage' γs ∗
        "Hmeta" ∷ memStorMeta bv.storage' γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
        "#Hlog0" ∷ memLog γs 0 DFrac.discard [zero_val EntryM] ∗ "Hend" ∷ memEnd γs 1 ∗
        -- the peers, their contexts
        "Hpeers" ∷ bv.peers' ↦*{dq} pv ∗ "#Hctx" ∷ peersCtx pv ctxs ∗
        -- the cluster's allocation's: this node's boot token (2026-10-30, the repair: raft's
        -- unified `cluster_alloc` with the bootstrap log), the server's raft invariant
        "Hboot" ∷ nodeBoot γr.cl srvClusterN ps ctxs cv.ID' ∗
        "#Hlinv" ∷ srvRaftLogInv E.γr.raft ∗
        -- the names-only contracts
        "#Hzap" ∷ rnLoggerZapOk ∗ "#Hsetlg" ∷ rnSetLoggerOk ∗ "#Htdok" ∷ rnTimeoutDetectorOk ∗
        "#Htkok" ∷ rnTickerOk E ∗ "#Hrs" ∷ rnRaftStatusOk ∗ "#Hns" ∷ rnNewStorageOk ∗
        "#Hcl" ∷ rnClusterOk cl }}
      (App (App (App (Val (b @!! go.GoType.PointerType bootstrappedRaft.ty @!! go!"newRaftNode"))
        (Val #ss)) (Val #wal)) (Val #cl))
    {{ (r : Loc), RET #r;
        ∃ (γw : RNNames) (rv : raftNode),
          ⌜γw.node = γr ∧ γw.id = cv.ID' ∧ γw.pre = [] ∧ γw.ms = bv.storage' ∧ γw.γs = γs ∧
            rv.lg' = bv.lg' ∧ rv.raftNodeConfig'.raftStorage' = bv.storage' ∧
            rv.raftNodeConfig'.heartbeat' = bv.heartbeat' ∧
            rv.raftNodeConfig'.transport' = GoInterface.nil ∧
            rv.raftNodeConfig'.Node' = rnNodeIface γw ∧
            -- (D22 J1a) the storage a `*storage` over the snapshotter `ss`
            rnStorageOf rv.raftNodeConfig'.storage' ss⌝ ∗
          -- the struct value, to be copied; its fresh mutex
          r ↦ rv ∗ rv.tickMu' ↦ (zero_val sync.RWMutex) ∗
          -- (D21 M2) the node's inbound methods (`Process`'s), from the start
          rnStepIfc γw (rnNodeIface γw) ∗
          -- `isServerBuilt`'s rows but `isRaftNode`; (2026-10-30, the repair) the apply side's
          -- half of the node's running token (`StartNode`'s `nodeRunning 1`, the other half in
          -- `rnLoopTok`)
          rnLoopTok γw [] ∗ rnApplyTok γw [] ∗ (letI := srvStor (GF := GF) γw.node; nodeRunning γw.nl γw.node.cl srvClusterN (1 : Qp).half) ∗
          -- the installer: `isRaftNode` and `rnDoneTok` at the address `a` the struct is copied
          -- to, once its `transport` is set to `tr`, with the server's own: `rnEnvOk` for the
          -- wrapper's names, the committed index's invariant of the server `s` and the read
          -- contexts' invariant (2026-10-27)
          (∀ (a s : Loc) (tr : GoInterface), rnEnvOk E γw -∗ srvCommittedInv s E.γr -∗
            srvRdCtxInv E.γr.raft issued -∗
            rnFixed a rv -∗ rnTransportAddr a ↦ tr -∗ rnLatestTickTsAddr a ↦ rv.latestTickTs' -∗
            isRNTransport E tr -∗ rv.tickMu' ↦ (zero_val sync.RWMutex) ={⊤}=∗
            isRaftNode E γw a ∗ rnDoneTok γw a ∗
            rnNodeAddr a ↦□ rnNodeIface γw ∗ raftPropose E.γr.raft (rnNodeIface γw) ∗
            rnTransportAddr a ↦□ tr) ∗
          -- (2026-10-27) the peers' slice not back (the node API's `StartNode` keeps it)
          b ↦{dq} bv ∗
          -- (2026-10-30, the repair) the storage's invariant at the node's justifications
          -- (`memStorInv`, allocated by `InitialState`, `bootStorage`'s `Q`) and its hard state
          memStorInv bv.storage' γs γr.cl cv.ID' ∗
          memStorMeta bv.storage' γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) }}

set_option maxHeartbeats 0 in
/-- **The composition** (see `NodeStartSpec` and the file header): from
`bootstrappedRaft.newRaftNode.spec` (through it the node API's `StartNode`) and the node API's node
specs (for its contract, `isRaftNodeIfc_of_isNode`), at the cluster's storage model. -/
theorem raftNode_of_StartNode
    (wp_bnr : bootstrappedRaft.newRaftNode.spec (GF := GF) (hG := hG))
    (wp_InitialState : MemoryStorage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (wp_Ready : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Ready.spec (GF := GF) (hG := hG))
    (wp_Advance : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Advance.spec (GF := GF) (hG := hG))
    (wp_Tick : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Tick.spec (GF := GF) (hG := hG))
    (wp_Stop : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Stop.spec (GF := GF) (hG := hG))
    (wp_ReadIndex : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReadIndex.spec (GF := GF) (hG := hG))
    (wp_Step : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Step.spec (GF := GF) (hG := hG))
    (wp_ReportUnreachable : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReportUnreachable.spec (GF := GF) (hG := hG))
    (wp_ReportSnapshot : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ReportSnapshot.spec (GF := GF) (hG := hG))
    (wp_Propose : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Propose.spec (GF := GF) (hG := hG))
    (wp_ApplyConfChange : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.ApplyConfChange.spec (GF := GF) (hG := hG)) :
    NodeStartSpec (GF := GF) := by
  intro γr E b ss wal cl dq bv cv lok γs pv ps ctxs issued Hlg Hhb Hvalid Hlok Hstor Hinfl
    Hdpf Hro Hdccv Hsizes Hasync Happlied Hps Hpsne Hnodup H0 Hpslen Hid Hvs Hfit HEγ HEpre HEai
  letI : MemStorReg GF := ⟨γr.reg⟩
  letI := srvStor (GF := GF) γr
  iintro %Φ Hpre HΦ
  iNamed Hpre
  ihave Hbs := srvMem_bootStorage wp_InitialState wp_Snapshot wp_LastIndex wp_FirstIndex wp_Term
      wp_Entries γr bv.storage' γs cv.ID' $$ [Hfresh Hmeta Hend]
  · iframe Hreg Hlock Hfresh Hmeta Hlog0 Hend
  wp_apply (wp_bnr E γr b ss wal cl dq bv cv lok γs [] pv ps ctxs
    iprop(memStorInv bv.storage' γs γr.cl cv.ID' ∗
      memStorMeta bv.storage' γs (HardStateM.mk (W64 0) (W64 0) (W64 0)))
    Hlg Hhb Hvalid Hlok Hstor Hinfl Hdpf Hro Hdccv Hsizes Hasync Happlied Hps Hpsne Hnodup H0
    (by omega) Hid Hvs)
    $$ [Hb Hc Hbs Hpeers Hboot]
    as %r Hpost
  · iframe #; iframe Hb Hc Hbs Hpeers Hboot
  icases Hpost with ⟨%n, %γw, %f, %st, %Hnames, #Hnode, Hdrv, Hncfg, Hrun, #Hidri, #Hsti, %Hstss,
    Hbuilt, Hb, ⟨#Hminv, Hmeta⟩⟩
  obtain ⟨Hwnode, Hwid, Hwnl, Hwpre, Hwms, Hwγs⟩ := Hnames
  iunfold rnBuilt at Hbuilt
  iNamed Hbuilt
  obtain ⟨Hrvlg, Hrvcfg⟩ := Hrv
  -- the bridges
  ihave #Hfits' : rnLogFits γw $$ []
  · iunfold rnLogFits; ipureintro; rw [Hwnode]; exact Hfit
  ihave #Hreg' : rnMemStorReg γw $$ []
  · unfold rnMemStorReg RNNames.reg; rw [Hwms, Hwγs, Hwnode]; iexact Hreg
  ihave #Hpraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hmsi : isRNMemStor γw γw.ms $$ []
  · iapply isRNMemStor_of_memstorage γw
    iframe Hpraft
    iexact Hreg'
  ihave #Hisnode : rnIsNode γw $$ []
  · unfold rnIsNode; rw [Hwnode, Hwid, Hwnl]; iexact Hnode
  -- the running token's halves
  icases ((nodeRunning_fractional n γr.cl srvClusterN).fractional (1 : Qp).half
      (1 : Qp).half).1 $$ [Hrun] with ⟨Hrun1, Hrun2⟩
  · rw [Qp.half_add_half]; iexact Hrun
  -- the tokens
  ihave ⟨Hloop, Happly⟩ := rnToks_of_start γw Hwpre
      (by
        rw [Hwnode]
        unfold SrvRaft.cfg
        rw [Hvs]
        refine srvCfgOk_nil _ (fun h0 => H0 ((GMap.elem_of_list_to_set _ _).1 h0)) ?_
        rw [GMap.size_list_to_set ps Hnodup]
        omega)
    $$ [Hdrv Hncfg Hrun1 Hprod Hcons Hcum Hcum0]
  · rw [Hwnode, Hwnl, Hwms]
    iframe Hdrv Hrun1 Hprod Hcons Hcum Hcum0
    unfold SrvRaft.cfg
    rw [Hvs]
    iexact Hncfg
  iapply HΦ
  iexists γw, rv
  isplitr
  · ipureintro
    refine ⟨Hwnode, Hwid, Hwpre, Hwms, Hwγs, Hrvlg, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [Hrvcfg]
    all_goals first | exact Hstss | simp only [rnNodeIface, Hwnl]
  iframe Hr Hmu Hloop Happly Hb Hminv Hmeta
  isplitr
  · iapply rnStepIfc_of_isNode γw (wp_Step γw.node) (wp_ReportUnreachable γw.node)
      (wp_ReportSnapshot γw.node)
    iframe Hpkg Hisnode
  isplitl [Hrun2]
  · rw [Hwnode, Hwnl]; iexact Hrun2
  -- the installer
  iintro %a %s %tr #Henv' #Hcommi #Hrdi #Hfix Htrf Hlts #Htri Hmu'
  ihave #Hrsb : rnReadStateBridge E γw $$ []
  · iapply rnReadStateBridge_of_raft E γw $$ Henv'
  ihave #Hni : isRaftNodeIfc E γw (rnNodeIface γw) $$ []
  · iapply isRaftNodeIfc_of_isNode E γw s issued (wp_Ready γw.node) (wp_Advance γw.node)
      (wp_Tick γw.node) (wp_Stop γw.node) (wp_ReadIndex γw.node)
      (wp_ApplyConfChange γw.node)
    iframe Hpkg Henv' Hisnode Hcommi Hreg' Hrdi
  ihave #Hprop : raftPropose E.γr.raft (rnNodeIface γw) $$ []
  · iapply raftPropose_of_isNode E γw (wp_Propose γw.node)
    iframe Hpkg Henv' Hisnode Hlinv
  ihave #Hfix' : rnFixed a
      { rv with raftNodeConfig' := { rv.raftNodeConfig' with transport' := tr } } $$ []
  · simp only [rnFixed]
    iexact Hfix
  imod (isRaftNode_of_rnParts E γw a
    { rv with raftNodeConfig' := { rv.raftNodeConfig' with transport' := tr } })
    $$ [Htrf Hlts Hmu' Hdtok] with ⟨#Hrn, Hdone, #Hnodef, #Htrf⟩
  · iframe Hpkg Henv' Hfits' Hrsb Hreg' Hfix' Htrf Hlts Hmu' Hdtok
    simp only [Hrvcfg]
    iframe Hidri Hsti Htri Hmsi
    isplitr
    · -- the node's contract, at the config's `Node` field
      rw [← Hwnl]
      iexact Hni
    isplitr
    · ipureintro; exact Hwms.symm
    -- the components are the same (`transport` is no component)
    iunfold rnParts at Hparts
    iunfold rnParts
    iNamed Hparts
    simp only [named]
    iframe #
    ipureintro; exact Hlgnn
  imodintro
  iframe Hrn Hdone Htrf Hprop
  have hn : rnNodeIface γw =
      ({ rv with raftNodeConfig' := { rv.raftNodeConfig' with transport' := tr } } : raftNode).raftNodeConfig'.Node' := by
    simp only [Hrvcfg, rnNodeIface, Hwnl]
  rw [hn]
  iexact Hnodef

end compose

end EtcdGrove
end Perennial
