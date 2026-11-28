/-
**The server's raft wrapper from raft's `StartNode`** (stage R8b-C of the raft v3.7 retarget,
2026-10-16; D12: `notes/decisions.md`, "The new cluster's start"): the composition that builds
`isServerBuilt`'s raft rows -- `isRaftNode`, the loop and apply tokens at `[]`, the right to close
`done` -- from the new cluster's ghost allocation for this node (its boot token, vacant id and
durable state), a fresh registered `MemoryStorage`, the WAL's durability, the contracts and
`bootstrappedRaft.newRaftNode`'s spec. Lean-first (no Rocq counterpart).

**Where the wrapper lives.** `NewServer` copies the wrapper by value (`r: *b.raft.newRaftNode(...)`)
into `EtcdServer.r` and sets its `transport` afterwards (`srv.r.transport = tr`), so
`bootstrappedRaft.newRaftNode` cannot hand out `isRaftNode` at the pointer it returns: it hands out
the struct value with its components' predicates (`rnBuilt`, `InvNodeStart.lean`), and
`isRaftNode_of_rnParts` installs `isRaftNode` at the address the struct finally lives at, once the
transport is set -- the step a `NewServer` proof takes. `raftNode_of_StartNode` composes the two:
its post is the struct value, the loop's and the apply side's tokens (`rnLoopTok`/`rnApplyTok` at
`[]`, from raft's `nodeDriver` at its start and `applyc`'s halves), and the installer, among
others (the node's inbound methods, the running token's other half, the storage's invariant and
hard state, the receiver and the peers' slice, the stop claim: see `NodeStartSpec`'s post).

**The premises, classified** (`NodeStartSpec`'s; 2026-11-05, rewritten: the list it replaced named
the allocation and contracts of before the node API):
* the callees' specs (`raftNode_of_StartNode`'s hypotheses): `bootstrappedRaft.newRaftNode.spec`
  (through it `StartNode.spec` and `newRaftNode.spec`), the `MemoryStorage` specs `StartNode`'s
  boot of the storage calls (`srvMem_bootStorage`), and the node API's `node` specs (for the
  node's contract, `isRaftNodeIfc_of_isNode`, its inbound methods and `Propose`), all instantiated
  by the linked `wp_*` in `Results.lean`;
* pure: the configuration and the peers (`rnStartCfg`), a positive heartbeat (`newRaftNode`'s, a
  scope restriction), the peers distinct, non-zero, fewer than `2 ^ 62` and the cluster's voters (the
  start's configuration view, `srvCfgOk_nil`), the WAL read (`NewStorage`'s contract), and the
  time-receipt bound past the bootstrap log (`rnLogFits`);
* the cluster's allocation's: this node's boot token, its id vacant and its durable state at
  `RaftState.init`; the fresh registered `MemoryStorage` as `NewMemoryStorage` leaves it; the
  peers and their contexts; the WAL's durability invariant, the loop's view at the start and its
  token (`wal.bootOk_start`);
* the contracts (`rnLoggerZapOk`, `rnTimeoutDetectorOk` (`rnNewStorageOk` until wal-nostorageok, 2026-11-21),
  `rnClusterOk` on names-only callees; `rnRaftStatusOk` the invariant of the package globals
  `raftStatus`/`raftStatusMu`);
* the installer's, given when the server exists (since unit N1 of the server-construction unit,
  2026-10-17: `NewServer` evaluates `newRaftNode` inside the `EtcdServer` literal, before the
  server `s` exists): `rnEnvOk` (the names tied, `E.γr.raft = ⟨γr, [], 0⟩`, and the server's raft
  invariant `srvRaftLogInv`), `srvCommittedInv s E.γr`, the read contexts' invariant, the
  transport's contract `isRNTransport` and the struct's fields where it lands.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedRaft__newRaftNode
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NodeBridge
public import Proof.go_etcd_io.raft.v3.MemstorageApi
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseRestartStor
public import Spec.go_etcd_io.raft.v3.MemoryStorage__InitialState

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

/-- The struct at `a`, split: its fixed fields read-only and its transport, tick timestamp and replay terms owned. -/
theorem rnFixed_split (a : Loc) (rv : raftNode) :
    a ↦ rv ⊢ |={⊤}=> rnFixed (GF := GF) a rv ∗
      rnTransportAddr a ↦ rv.raftNodeConfig'.transport' ∗ rnLatestTickTsAddr a ↦ rv.latestTickTs' ∗
      rnReplayTermsAddr a ↦ rv.raftNodeConfig'.initialReplayTerms' := by
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
  iframe transportC latestTickTsR initialReplayTermsC
  iunfold rnFixed
  simp only [named]
  iframe #

/-- **Installing the wrapper** (see the file header): the struct value `rv` at `a` (the server's
`r` field, after the copy and the transport set), its fresh `tickMu`, the components' predicates
and what the node and the server provide give `isRaftNode E γ a` and the right to close `done`.
A fancy update: `tickMu`'s guard over `latestTickTs` is made here (`sync.init_RWMutex`), and
(srvloops2, 2026-11-21, bounds B2 for `tickMu`) its reader slots become the pools `rnTickPool` (thread
pools at levels 3 and 4, half of the lock's `2 ^ 30 - 1` slots each, under `threadBound GF ≤ 2 ^ 29`);
the node is raft's (`Hnode`, recorded in `isRaftNode`). -/
theorem isRaftNode_of_rnParts (E : RNEnv GF) (γ : RNNames GF) (a : Loc) (rv : raftNode)
    (Hnode : rv.raftNodeConfig'.Node' = interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.node.ty) #γ.nl.loc)
    (Hbnd : threadBound GF ≤ 2 ^ 29) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      rnEnvOk E γ ∗ rnLogFits γ ∗ rnReadStateBridge E γ ∗
      -- (restart S3 item 7) the restart data
      rnRestartOk γ ∗
      (letI : MemStorReg GF := ⟨γ.reg⟩; memStorReg γ.ms γ.γs) ∗
      isRaftNodeIfc E γ rv.raftNodeConfig'.Node' ∗
      isRNIDRemoved rv.raftNodeConfig'.isIDRemoved' ∗
      ⌜rv.raftNodeConfig'.raftStorage' = γ.ms⌝ ∗ isRNMemStor γ γ.ms ∗
      isWalStorage rv.raftNodeConfig'.storage' γ.wal.h γ.ss ∗
      -- (2026-11-03, R2b-1 stage 3c) the WAL's durability invariant; (P5) the crash-aware one, with the
      -- node's arm
      rnDurInvK γ.node γ.id γ.walK γ.wal.h ∗
      (letI := srvStor (GF := GF) γ.node; nodeArm γ.nl γ.node.cl γ.walK.x) ∗
      ⌜γ.walK.sd = fun _ => iprop(True)⌝ ∗
      isRNTransport E rv.raftNodeConfig'.transport' ∗
      rnParts E γ rv ∗
      rnFixed a rv ∗ rnTransportAddr a ↦□ rv.raftNodeConfig'.transport' ∗
      rnLatestTickTsAddr a ↦ rv.latestTickTs' ∗ rnReplayTermsAddr a ↦ rv.raftNodeConfig'.initialReplayTerms' ∗
      rnReplayState γ rv.raftNodeConfig'.initialReplayTerms' γ.snap0 ∗ rv.tickMu' ↦ (zero_val sync.RWMutex) ∗
      ownBroadcastChan rv.done' γ.done (rnDoneEsc γ) .Pending ⊢
      |={⊤}=> isRaftNode E γ a ∗ rnWorkerStartTok γ a ∗
        rnNodeAddr a ↦□ rv.raftNodeConfig'.Node' ∗
        rnTransportAddr a ↦□ rv.raftNodeConfig'.transport' := by
  iintro ⟨#Hpkg, #Henv, #Hfits, #Hrsb, #Hrok, #Hreg, #Hni, #Hidri, %Hmsγ, #Hmsi, #Hsti, #Hdur, #Harm, %Hsd, #Htri, #Hparts,
    #Hfix, #transportC, latestTickTsR, Hreplay, #Hseed, Hmu, Hdtok⟩
  iunfold rnParts at Hparts
  iNamed Hparts
  iunfold rnFixed at Hfix
  iNamed Hfix
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  imod sync.init_RWMutex (rnTickInv a) rv.tickMu' $$ [latestTickTsR] Hmu with Hslots
  · inext; iunfold rnTickInv; iexists rv.latestTickTs'; iexact latestTickTsR
  icases sync.ownRWMutex_slots_guard _ _ $$ Hslots with ⟨Hslots, #Hmug⟩
  -- (srvloops2) `tickMu`'s pools at levels 3 and 4, half of the slots each
  have hsplit : Int.toNat sync.rwmutex.actualMaxReaders = (2 ^ 29 - 1) + 2 ^ 29 := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; decide
  ihave ⟨Hs3, Hs4⟩ : ([∗list] _x ∈ List.replicate (2 ^ 29 - 1) (),
      sync.ownRWMutex rv.tickMu' (rnTickInv a)) ∗
      [∗list] _x ∈ List.replicate (2 ^ 29) (), sync.ownRWMutex rv.tickMu' (rnTickInv a) $$ [Hslots]
  · rw [hsplit, ← List.replicate_append_replicate]
    iapply BigSepL.bigSepL_append.1
    iexact Hslots
  imod threadPool.initL (rnTickPoolN 3) 3 (sync.ownRWMutex rv.tickMu' (rnTickInv a)) ⊤
      (2 ^ 29 - 1) (by omega) $$ Hs3 with ⟨%γt3, #Htp3⟩
  imod threadPool.initL (rnTickPoolN 4) 4 (sync.ownRWMutex rv.tickMu' (rnTickInv a)) ⊤
      (2 ^ 29) (by omega) $$ Hs4 with ⟨%γt4, #Htp4⟩
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
    · ipureintro; exact Hmsγ
    isplitr
    · rw [Hmsγ]; iexact Hmsi
    isplitr
    · ipureintro; exact Hsd
    isplitr
    · ipureintro; exact Hnode
    iunfold rnTickPool
    iintro %l %hl
    rcases hl with rfl | rfl
    · iexists γt3; iexact Htp3
    · iexists γt4; iexact Htp4
  · iframe NodeC transportC
    iunfold rnWorkerStartTok
    isplitl [Hdtok]
    · iunfold rnDoneTok
      iexists rv.done', rv.raftNodeConfig'.storage'
      iframe doneR Hdtok
      iexact storageC
    iexists rv.raftNodeConfig'.initialReplayTerms'
    iframe Hreplay Hseed

/-- **The loop's and the apply side's tokens at the start** (`rnLoopTok γ []`, `rnApplyTok γ
[]`): from the node API's driver at its start (`NodeDriverState.init`: nothing delivered, with
`γ.pre = []`), its view of the configuration at index `0` (`StartNode`'s; 2026-10-30, the repair:
in every cluster), the loop's half of the running token, and `applyc`'s halves with `cum` at
`[[]]` (`newRaftNode`'s). (2026-10-27: over the node API. 2026-11-01, durability layer 4: the
driver at the storage's key `γ.key`, and the node's durable state at `RaftState.init`, which goes
into the loop's token beside the driver.) -/
theorem rnToks_of_start (γ : RNNames GF) (hpre : γ.pre = []) (ha : γ.a0 = []) (ht : γ.t0 = W64 0)
    (hc0 : γ.commit0 = 0) (hs0 : γ.snap0 = 0)
    (hcfg : srvCfgOk γ.node.cfg [] ⟨0, Membership.simple γ.node.cfg⟩) :
    (letI := srvStor (GF := GF) γ.node;
      iprop(nodeDriver γ.nl γ.node.cl srvClusterN
          (NodeDriverState.init (memStorIface γ.ms) γ.key) ∗
        nodeConfig γ.nl γ.node.cl srvClusterN ⟨0, Membership.simple γ.node.cfg⟩)) ∗ (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ∗
      sspscProducer γ.ap ([] : List toApply) ∗ sspscConsumer γ.ap ([] : List toApply) ∗
      monoListAuthOwn γ.cum 1 [([] : List EntryModel)] ∗
      monoListIdxOwn γ.cum 0 ([] : List EntryModel) ∗
      -- (2026-11-03, R2b-1 stage 4) the loop's view of the WAL at the start; (P5) the crash-aware
      -- invariant's (`rnDurK_alloc.law`)
      rnWalViewK γ.walK (walView0, none) ⊢
      rnLoopTok γ [] ∗ rnApplyTok γ [] := by
  letI := srvStor (GF := GF) γ.node
  iintro ⟨⟨Hdrv, Hcfg⟩, Hrun, Hprod, Hcons, Hcum, Hcum0, Hwv⟩
  -- (S1) the log handed out (none) committed, from the driver's delivered log
  ihave ⟨Hdrv, #Hdl⟩ := nodeDriver_deliveredLogLb γ.nl γ.node.cl srvClusterN _ $$ Hdrv
  ihave #HcL0 : isCommittedLogLb γ.node.cl (srvLE γ.srv []) $$ []
  · have h : srvLE γ.srv [] = (NodeDriverState.init (memStorIface γ.ms) γ.key).delivered := by
      simp [srvLE, NodeDriverState.init, RNNames.srv, hpre]
    rw [h]; iapply deliveredLogLb_committed $$ Hdl
  isplitl [Hdrv Hcfg Hrun Hprod Hcum Hwv]
  · iunfold rnLoopTok
    isplitr
    · ipureintro; rw [hs0]; exact Nat.zero_le _
    iexists hsZero
    isplitl; rotate_left
    · ipureintro; rw [ht]
    iunfold rnLoopTokP
    iexists [], [[]], RaftState.init, W64 0
    isplitl [Hdrv Hcfg]
    · iunfold rnDrv
      have h : rnDrvSt γ [] hsZero RaftState.init (W64 0) =
          NodeDriverState.init (memStorIface γ.ms) γ.key := by
        simp [rnDrvSt, NodeDriverState.init, srvLE, RNNames.srv, hpre]
      rw [h]
      iframe Hdrv
      iapply ((rnView_first γ ha).1 ⟨ht, hc0, hs0⟩ []).2
      unfold srvCfgView
      iexists ⟨0, Membership.simple γ.node.cfg⟩
      iframe Hcfg
      ipureintro
      simp only [RNNames.srv, hpre, List.append_nil]
      exact hcfg
    isplitr
    · ipureintro; intro h; cases h
    isplitl [Hwv]
    · iunfold rnWalView
      have h0 : (⟨RaftState.init, hsZero, none, srvLE γ.srv []⟩ : WalView) = walView0 := by
        simp [srvLE, RNNames.srv, hpre, walView0]
      rw [h0]
      iexact Hwv
    iframe Hrun Hprod Hcum
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · ipureintro
      exact ⟨W64 0, by rw [hpre]; rfl, fun n m h => by simp at h⟩
    isplitr
    · iunfold srvFrozenTerms
      iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
      itrivial
    -- (S1) the loop's fact at a first start: `commit0 = 0`
    isplitr
    · ipureintro; rw [hc0]; exact Nat.zero_le _
    iexact HcL0
  · iunfold rnApplyTok
    iexists []
    iframe Hcons
    iexact Hcum0

/-- (restart S3 item 8, 2026-11-11; Q34 (a)) **The loop's and the apply side's tokens at a restart**
(`rnLoopTok γ P`, `rnApplyTok γ P`), beside `rnToks_of_start`: from the node API's driver as
`RestartNode` leaves it (delivered the committed log of the restored base, here `srvLE γ.srv P`; the
restored hard state `p`; the durable state `S`; a follower), its view `v` after the ghost log
(`srvCfgOk`), the loop's half of the running token, `applyc`'s halves with `cum` at `[P]`
(`newRaftNode`'s at `L₀ = P`), the loop's WAL view at `⟨S, p, none, srvLE γ.srv P⟩`, `P`'s frozen terms
(the restarted storage's, `srvFrozenTerms_restart`), `P`'s indices from `1`, and the loop's fact
(`commit0 ≤ p.Commit'`). -/
theorem rnToks_of_restart (γ : RNNames GF) (P : List EntryModel) (p : HardStateM) (S : RaftState)
    (v : ConfigView) (hpre : γ.pre = []) (hidx : srvIdxOkW (W64 0) P)
    (hc0 : γ.commit0 ≤ uint.nat p.Commit') (hs0 : γ.snap0 ≤ (rnLogOf γ P).length)
    (hcfg : srvCfgOk γ.node.cfg (rnGhost γ P) v)
    -- (keepfix (c) step 1, T1) the restored hard state's term is the names' `t0`
    (ht : p.Term' = γ.t0) :
    (letI := srvStor (GF := GF) γ.node;
      iprop(nodeDriver γ.nl γ.node.cl srvClusterN
          ⟨memStorIface γ.ms, srvLE γ.srv P, p, none, γ.key, S, StateFollower⟩ ∗
        nodeConfig γ.nl γ.node.cl srvClusterN v)) ∗
      (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ∗
      sspscProducer γ.ap ([] : List toApply) ∗ sspscConsumer γ.ap ([] : List toApply) ∗
      monoListAuthOwn γ.cum 1 [P] ∗ monoListIdxOwn γ.cum 0 P ∗
      rnWalViewK γ.walK ((⟨S, p, none, srvLE γ.srv P⟩ : WalView), none) ∗
      srvFrozenTerms γ.γs 1 P ⊢
      rnLoopTok γ P ∗ rnApplyTok γ P := by
  letI := srvStor (GF := GF) γ.node
  iintro ⟨⟨Hdrv, Hcfg⟩, Hrun, Hprod, Hcons, Hcum, Hcum0, Hwv, #Hfz⟩
  ihave ⟨Hdrv, #Hdl⟩ := nodeDriver_deliveredLogLb γ.nl γ.node.cl srvClusterN _ $$ Hdrv
  ihave #HcL : isCommittedLogLb γ.node.cl (srvLE γ.srv P) $$ []
  · iapply deliveredLogLb_committed $$ Hdl
  isplitl [Hdrv Hcfg Hrun Hprod Hcum Hwv]
  · iunfold rnLoopTok
    isplitr
    · ipureintro; exact hs0
    iexists p
    isplitl; rotate_left
    · ipureintro; exact ht
    iunfold rnLoopTokP
    iexists [], [P], S, StateFollower
    isplitl [Hdrv Hcfg]
    · iunfold rnDrv
      have h : rnDrvSt γ P p S StateFollower =
          ⟨memStorIface γ.ms, srvLE γ.srv P, p, none, γ.key, S, StateFollower⟩ := rfl
      rw [h]
      iframe Hdrv
      iunfold rnCfgAt
      iunfold rnView
      iunfold srvCfgView
      iexists v
      iframe Hcfg
      ipureintro
      simp only [List.nil_append]
      exact hcfg
    isplitr
    · ipureintro; intro h; cases h
    isplitl [Hwv]
    · iunfold rnWalView
      iexact Hwv
    iframe Hrun Hprod Hcum
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · ipureintro
      exact ⟨W64 0, by rw [hpre]; rfl, hidx⟩
    isplitr
    · rw [hpre]; iexact Hfz
    isplitr
    · ipureintro; exact hc0
    iexact HcL
  · iunfold rnApplyTok
    iexists []
    iframe Hcons
    iexact Hcum0

/-- (restart S3 item 8, 2026-11-11) **The restarted storage freezes the log up to its base with its
terms**: the storage compacted through `|P|` and its entry at `|P|` frozen at `P`'s last term (what
`memStorRestarted` leaves at the base `σ.b = |P|`) give `P`'s frozen terms from index `1` (every
entry but the last compacted, the last frozen). -/
theorem srvFrozenTerms_restart (γs : MemStorNames) (P : List EntryModel) (e0 : EntryM)
    (hlt : lastTermIs P e0.Term') :
    memCompacted (GF := GF) γs P.length ∗ memLog γs P.length DFrac.discard [e0] ⊢
      srvFrozenTerms γs 1 P := by
  suffices h : iprop(□ (memCompacted (GF := GF) γs P.length ∗
      memLog γs P.length DFrac.discard [e0])) ⊢ srvFrozenTerms γs 1 P by
    iintro ⟨#Hc, #He⟩
    iapply h
    imodintro
    iframe Hc He
  unfold srvFrozenTerms
  refine BigSepL.bigSepL_intro fun k m hk => ?_
  iintro #H
  icases H with ⟨#Hc, #He⟩
  have hkl : k < P.length := (List.getElem?_eq_some_iff.1 hk).1
  by_cases hlast : k + 1 < P.length
  · iright
    isplitr
    · ipureintro; exact hlast
    iapply memCompacted_mono γs P.length (1 + k) (by omega) $$ Hc
  · ileft
    iexists e0
    have hkP : 1 + k = P.length := by omega
    rw [hkP]
    iframe He
    ipureintro
    rcases hlt with h | h
    · subst h; simp at hkl
    · have hg : P.getLast? = some m := by
        rw [List.getLast?_eq_getElem?, show P.length - 1 = k by omega]; exact hk
      rw [hg] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact h.symm

/-- (restart S3 item 8, 2026-11-11) **The restored base's term is the backend log's**: a committed
backend log `A₀` (`srvRLogLb`, at the server's names) reaching the records' base, and the records'
snapshot certificate (`walSnapCert`; the snapshot record's term the base's, `hterm`), give the base's
term as the last term of `A₀` up to the base (committed logs agree, `isCommittedLogLb_agree`). -/
theorem restart_lastTerm (γr : SrvRaft) (A₀ : List EntryModel) (σ : StorContents)
    (hb : σ.b ≤ A₀.length)
    (hterm : ∀ m : SnapshotMetadataM, σ.snap = some (SnapshotM.mk [] m) → m.Term' = σ.base.term') :
    srvRLogLb (GF := GF) ⟨γr, [], W64 0⟩ A₀ ∗ walSnapCert γr.cl σ ⊢
      ⌜lastTermIs (A₀.take σ.b) σ.base.term'⌝ := by
  letI := srvStor (GF := GF) γr
  iintro ⟨#HA, #Hc⟩
  iunfold walSnapCert at Hc
  icases Hc with (%H0 | ⟨%m, %Hsm, #Hv⟩)
  · ipureintro; left; rw [H0]; rfl
  obtain ⟨Hsnap, Hidx⟩ := Hsm
  iunfold snapshotValid at Hv
  icases Hv with ⟨%l, %mem, #Hl, -, -, %Hp⟩
  obtain ⟨h1, h2, h3, -⟩ := Hp
  iunfold srvRLogLb at HA
  icases HA with ⟨#HAc, -⟩
  icases isCommittedLogLb_agree γr.cl l (srvLE ⟨γr, [], W64 0⟩ A₀) $$ [Hl HAc] with %Hag
  · iframe Hl HAc
  ipureintro
  have hlb : l.length = σ.b := by simp only at h1; rw [h1, Hidx]
  have hSL : (srvLE ⟨γr, [], W64 0⟩ A₀).length = A₀.length := by simp [srvLE]
  have hl : l = (A₀.take σ.b).map EntryModel.toLE := by
    have e : (A₀.take σ.b).map EntryModel.toLE = (srvLE ⟨γr, [], W64 0⟩ A₀).take l.length := by
      rw [hlb]; simp [srvLE, List.map_take]
    rw [e]
    rcases Hag with h | h
    · exact List.prefix_iff_eq_take.1 h
    · have := h.length_le
      rw [hSL] at this
      have heq : srvLE ⟨γr, [], W64 0⟩ A₀ = l :=
        List.IsPrefix.eq_of_length h (by omega)
      rw [heq, List.take_length]
  right
  have ht : Option.map LogEntry.term l.getLast? = some m.Term' := h3
  rw [hterm m Hsnap] at ht
  rw [hl, List.getLast?_map, Option.map_map] at ht
  exact ht

/-- **A fresh `MemoryStorage` boots a node** (2026-10-30, the repair: `StartNode.spec`'s
`bootStorage`, at the empty conf state and hard state, over raft's two-writer `MemoryStorage`
specs; until then the trusted `InitialState` closure and the old storage tokens; 2026-11-01,
durability layer 4: `restartStorage` at the empty contents): `FirstIndex` is `1` and `LastIndex` `0`
(the storage fresh: `memStorFresh_compacted`), `InitialState` answers the zero hard state and the
empty conf state (`memSnapEmpty`'s), and its continuation, at the key `K` raft names, allocates the
storage's invariant at `K`'s justifications (`memStorInv_alloc`), the storage `isStorage`
(`memStorage_isStorage`), its dummy entry and end; the client's frame `F` is made from the
invariant and the hard state at the key (`HF`; 2026-11-01, stage-I fix G1-frame: the frame
depends on the key). -/
theorem srvMem_bootStorage
    (wp_InitialState : MemoryStorage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (γr : SrvRaft) (ms : Loc) (γs : MemStorNames) (applied pin : GName) (F : GName → IProp GF)
    (htr : Cluster.trace γr.cl = none)
    (hsz : γs.sz = true) :
    letI : MemStorReg GF := ⟨γr.reg⟩
    letI := srvStor (GF := GF) γr
    memStorReg ms γs ∗ memStorLock ms γs ∗ memStorFresh ms γs 0 memSnapEmpty ∗
      memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
      memLog (GF := GF) γs 0 DFrac.discard [(zero_val EntryM : EntryM)] ∗ memEnd (GF := GF) γs 1 ∗
      (∀ K : GName, memStorInvT ms γs γr.cl K (srvStoredOrigin γr.cl applied pin 0) -∗
        memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) -∗ F K) ⊢
      restartStorage γr.cl (memStorIface ms)
        ⟨HardStateM.mk (W64 0) (W64 0) (W64 0), none, entryID.mk (W64 0) (W64 0), []⟩
        memSnapEmpty.Metadata'.ConfState' 0 F (fun sv => iprop(snapshotValid γr.cl sv ∗ (srvStoredOrigin γr.cl applied pin 0) sv)) := by
  letI : MemStorReg GF := ⟨γr.reg⟩
  letI := srvStor (GF := GF) γr
  iintro ⟨#Hreg, #Hl, Hfresh, Hmeta, #Hlog, He, HF⟩
  ihave #Hinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iunfold memStorLock at Hl; icases Hl with ⟨#H, -⟩; iexact H
  unfold restartStorage
  iexists (⟨MemoryStorage.ty.PointerType, intoVal ms⟩ : GoInterfaceOk)
  iexists iprop(memStorFresh ms γs 0 memSnapEmpty ∗
    memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗ memEnd γs 1 ∗
    (∀ K : GName, memStorInvT ms γs γr.cl K (srvStoredOrigin γr.cl applied pin 0) -∗
      memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) -∗ F K))
  iexists 0
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; simp [StorContents.b, StorContents.commit]
  isplitl [Hfresh Hmeta He HF]
  · iframe Hfresh Hmeta He HF
  isplitr
  · iintro !> %Φ ⟨Hfresh, Hmeta, He, HF⟩ HΦ
    wp_apply wp_FirstIndex ms γs 0 $$ [$Hinit $Hl]
      as %fi ⟨%Hfi, #Hc⟩
    · iapply memCompacted_zero
    icases memStorFresh_compacted ms γs _ _ _ $$ [$Hfresh $Hc] with ⟨%H0, Hfresh⟩
    have Hfi1 : fi = W64 (StorContents.b ⟨HardStateM.mk (W64 0) (W64 0) (W64 0), none, entryID.mk (W64 0) (W64 0), []⟩ + 1) := by
      simp only [StorContents.b]; word
    rw [Hfi1]
    iapply HΦ
    iframe Hfresh Hmeta He HF
  isplitr
  · iintro !> %Φ ⟨Hfresh, Hmeta, He, HF⟩ HΦ
    wp_apply wp_LastIndex ms γs 1 $$ [$Hinit $Hl $He]
      as %li ⟨He, %Hli⟩
    have Hli0 : li = W64 (StorContents.last ⟨HardStateM.mk (W64 0) (W64 0) (W64 0), none, entryID.mk (W64 0) (W64 0), []⟩) := by
      simp only [StorContents.last, StorContents.b, List.length_nil]; word
    rw [Hli0]
    iapply HΦ
    iframe Hfresh Hmeta He HF
  iintro !> %Φ ⟨Hfresh, Hmeta, He, HF⟩ HΦ
  wp_apply wp_InitialState ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) 0 memSnapEmpty
    $$ [$Hinit $Hmeta $Hfresh]
    as %hp %cs ⟨#Hhs, Hmeta, Hfresh, #Hcs⟩
  iapply HΦ $$ %hp %cs %true
  iframe Hhs
  isplitr
  · have hce : memSnapEmpty.Metadata'.ConfState' = ConfStateM.mk [] [] [] [] false := rfl
    rw [hce]
    iexact Hcs
  iintro %K #HA #HD
  imod memStorInvP_alloc ms γs (memStorJT γr.cl K (srvStoredOrigin γr.cl applied pin 0)) ⊤ 0 memSnapEmpty $$ Hl Hfresh [] [] with #Hinv
  · iintro !> %k %hk
    have : k = 0 := by omega
    subst this
    simp only [memStorJT]
    iapply memStorJ_B_le_one γr.cl K 0 (by decide)
    iapply nodeAppliedLb_zero γr.cl K
  · ileft; ipureintro; rfl
  ihave #Hinv' : memStorInvT ms γs γr.cl K (srvStoredOrigin γr.cl applied pin 0) $$ []
  · unfold memStorInvT; iexact Hinv
  ihave HFK := HF $$ %K Hinv' Hmeta
  imodintro
  isplitr
  · ihave #Hstorage := memStorage_isStorageT wp_LastIndex wp_FirstIndex wp_Term wp_Entries wp_Snapshot
      ms γs γr.cl K (srvStoredOrigin γr.cl applied pin 0) (fun _ => hsz) htr $$ Hinv' Hreg
    iExactEq Hstorage; rfl
  iframe HFK
  iunfold storHolds
  have hb : (⟨HardStateM.mk (W64 0) (W64 0) (W64 0), none, entryID.mk (W64 0) (W64 0), []⟩ : StorContents).b = 0 := by
    simp [StorContents.b]
  have hl : (⟨HardStateM.mk (W64 0) (W64 0) (W64 0), none, entryID.mk (W64 0) (W64 0), []⟩ : StorContents).last = 0 := by
    simp [StorContents.last, StorContents.b]
  rw [hl, hb, Nat.zero_add]
  simp only [Nat.sub_self, List.take_zero, List.drop_zero]
  iexists (zero_val EntryM)
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply memStorCompacted_of ms γs 0 $$ Hreg
    iapply memCompacted_zero
  isplitr
  · iapply memStorLog_of ms γs 0 DFrac.discard [zero_val EntryM] $$ Hreg Hlog
  isplitr
  · iapply memStorLog_of ms γs 1 DFrac.discard [] $$ Hreg
    iapply memLog_nil
  isplitr
  · iapply memStorLog_of ms γs 1 (DFrac.own 1) [] $$ Hreg
    iapply memLog_nil
  iapply memStorEnd_of ms γs 1 $$ Hreg He

/-- (restart S3, 2026-11-11; Q39) **Every committed index's configuration is the boot one**: with
the server's raft-log invariant, a configuration recorded at an index `k` within a committed log is
`simple cfg` (`srv_confAt_simple` and `confAt_agree`). -/
theorem srv_confAt_eq_simple (γ : ServerRaftNames) (l : List LogEntry) (k : Nat) (m : Membership)
    (hk : k ≤ l.length) (E : CoPset) (hC : ↑srvConfN ⊆ E) (hL : ↑srvLogN ⊆ E) :
    srvRaftLogInv (GF := GF) γ ∗ isCommittedLogLb γ.raft.cl l ∗
      (letI := srvStor (GF := GF) γ.raft; confAt γ.raft.cl k m) ⊢
      |={E}=> ⌜m = Membership.simple γ.raft.cfg⌝ := by
  letI := srvStor (GF := GF) γ.raft
  iintro ⟨#Hinv, #Hl, #Hm⟩
  imod srv_confAt_simple γ l k hk E hC hL $$ [$Hinv $Hl] with #Hs
  ihave %H := confAt_agree γ.raft.cl k m (Membership.simple γ.raft.cfg) $$ [Hm Hs]
  · iframe Hm Hs
  imodintro; ipureintro; exact H

/-- (restart S3, 2026-11-11; D4) **The restarted storage's snapshot is valid**: from the records'
certificate (`walSnapCert`: base `0`, or a valid snapshot of no data at the base), the snapshot
`bootstrap` applies (`walSnapCS σ cs`: the base's index and term, the backend's conf state `cs`) is
valid at a base past `0`: the same committed log and data; its configuration is the boot one
(`srv_confAt_eq_simple`), which `cs` states (`hcs`, S6's from the backend's members, H10), within
raft's bounds (`hcsb`); the term the records' (`hterm`: the snapshot record's is the base's). -/
theorem walSnapCS_valid (γ : ServerRaftNames) (σ : StorContents) (cs : ConfStateM) (E : CoPset)
    (hC : ↑srvConfN ⊆ E) (hL : ↑srvLogN ⊆ E)
    (hterm : ∀ m : SnapshotMetadataM, σ.snap = some (SnapshotM.mk [] m) → m.Term' = σ.base.term')
    (hcs : confStateIs cs (Membership.simple γ.raft.cfg))
    (hcsb : (cs.Voters'.length + cs.Learners'.length + cs.VotersOutgoing'.length +
      cs.LearnersNext'.length : Int) ≤ 2 ^ 62) :
    srvRaftLogInv (GF := GF) γ ∗ walSnapCert γ.raft.cl σ ⊢
      |={E}=> (⌜σ.b = 0⌝ ∨ (letI := srvStor (GF := GF) γ.raft;
        snapshotValid γ.raft.cl (walSnapCS σ cs))) := by
  letI := srvStor (GF := GF) γ.raft
  iintro ⟨#Hinv, #Hc⟩
  iunfold walSnapCert at Hc
  icases Hc with (%H0 | ⟨%m, %Hsm, #Hv⟩)
  · imodintro; ileft; ipureintro; exact H0
  obtain ⟨Hsnap, Hidx⟩ := Hsm
  iunfold snapshotValid at Hv
  icases Hv with ⟨%l, %mem, #Hl, #Hca, #Hmade, %Hp⟩
  imod srv_confAt_eq_simple γ l l.length mem (Nat.le_refl _) E hC hL $$ [$Hinv $Hl $Hca] with %Hm
  subst Hm
  imodintro
  iright
  iunfold snapshotValid
  iexists l, Membership.simple γ.raft.cfg
  iframe Hl Hca
  isplitr
  · iExactEq Hmade; rfl
  ipureintro
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Hp
  refine ⟨?_, h2, ?_, hcs, h5, hcsb⟩
  · rw [h1]; exact Hidx
  · rw [h3]; exact congrArg some (hterm m Hsnap)

/-- **The storage a restart rebuilds restarts a node** (restart S3, 2026-11-11; generalizing
`srvMem_bootStorage`, as kvdurable's `kd_restartStorage`): `bootstrappedWAL.MemoryStorage`'s
`memStorRestarted` (the WAL's records `σ`, the backend's conf state `cs`) is `RestartNode`'s
`restartStorage` at `σ` and `cs`, the freeze point the base (nothing frozen above it): `FirstIndex`
answers the base `+ 1` (detached: compacted at most there), `LastIndex` the last index,
`InitialState` the hard state and `cs` (`walSnapCS`'s); its continuation attaches the storage at
raft's key (`memStorInvP_alloc`: compacting up to the base is justified by raft's applied bound at
the attach, `max σ.b A`; the stored snapshot, at base `0` the empty one's index, else valid,
`hval`, and delivered, below the stored commit). The base is at most the stored commit (`Hbc`). -/
theorem srvMem_restartStorage
    (wp_InitialState : MemoryStorage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (γr : SrvRaft) (ms : Loc) (γs : MemStorNames) (applied pin : GName) (σ : StorContents) (cs : ConfStateM) (A : Nat)
    (F : GName → IProp GF) (Hbc : σ.b ≤ σ.commit)
    (htr : Cluster.trace γr.cl = none) (hsz : γs.sz = true)
    -- (auth-lease S4, 2026-11-16) outside the cluster's no-snapshot mode (`RestartNode`'s)
    (Hns : ¬ clusterNoSnap γr.cl) :
    letI : MemStorReg GF := ⟨γr.reg⟩
    letI := srvStor (GF := GF) γr
    memStorReg ms γs ∗ memStorLock ms γs ∗ memStorRestarted ms γs σ cs ∗
      (⌜σ.b = 0⌝ ∨ snapshotValid γr.cl (walSnapCS σ cs)) ∗
      (∀ K : GName, memStorInvT ms γs γr.cl K (srvStoredOrigin γr.cl applied pin σ.b) -∗ memStorMeta ms γs σ.hs -∗
        memSnapNone γs (walSnapCS σ cs) -∗ F K) ⊢
      restartStorage γr.cl (memStorIface ms) σ cs A F (fun sv => iprop(snapshotValid γr.cl sv ∗ (srvStoredOrigin γr.cl applied pin σ.b) sv)) := by
  letI : MemStorReg GF := ⟨γr.reg⟩
  letI := srvStor (GF := GF) γr
  iintro ⟨#Hreg, #Hl, Hrest, Hval, HF⟩
  iunfold memStorRestarted at Hrest
  icases Hrest with ⟨Hfresh, Hmeta, #Hc, #He0, Hsn, Hents, Hend⟩
  ihave #Hinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iunfold memStorLock at Hl; icases Hl with ⟨#H, -⟩; iexact H
  unfold restartStorage
  iexists (⟨MemoryStorage.ty.PointerType, intoVal ms⟩ : GoInterfaceOk)
  iexists iprop(memStorFresh ms γs σ.b (walSnapCS σ cs) ∗ memStorMeta ms γs σ.hs ∗
    memLog γs (σ.b + 1) (DFrac.own 1) σ.ents ∗ memEnd γs (σ.last + 1) ∗
    (⌜σ.b = 0⌝ ∨ snapshotValid γr.cl (walSnapCS σ cs)) ∗ memSnapNone γs (walSnapCS σ cs) ∗
    (∀ K : GName, memStorInvT ms γs γr.cl K (srvStoredOrigin γr.cl applied pin σ.b) -∗ memStorMeta ms γs σ.hs -∗
      memSnapNone γs (walSnapCS σ cs) -∗ F K))
  iexists σ.b
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact ⟨Nat.le_refl _, Hbc⟩
  isplitl [Hfresh Hmeta Hents Hend Hval Hsn HF]
  · iframe Hfresh Hmeta Hents Hend Hval Hsn HF
  isplitr
  · -- FirstIndex: the base plus one (detached: compacted at most at the base)
    iintro !> %Φ ⟨Hfresh, HR⟩ HΦ
    wp_apply wp_FirstIndex ms γs σ.b $$ [$Hinit $Hl $Hc] as %fi ⟨%Hfi, #Hc'⟩
    icases memStorFresh_compacted ms γs _ _ _ $$ [$Hfresh $Hc'] with ⟨%Hle, Hfresh⟩
    have Hfi' : fi = W64 (σ.b + 1) := by word
    rw [Hfi']
    iapply HΦ
    iframe Hfresh HR
  isplitr
  · -- LastIndex: the last index
    iintro !> %Φ ⟨Hfresh, Hmeta, Hents, Hend, HR⟩ HΦ
    wp_apply wp_LastIndex ms γs (σ.last + 1) $$ [$Hinit $Hl $Hend] as %li ⟨Hend, %Hli⟩
    have Hli' : li = W64 σ.last := by word
    rw [Hli']
    iapply HΦ
    iframe Hfresh Hmeta Hents Hend HR
  -- InitialState: detached; its continuation attaches the storage at raft's key
  iintro !> %Φ ⟨Hfresh, Hmeta, Hents, Hend, Hval, Hsn, HF⟩ HΦ
  wp_apply wp_InitialState ms γs σ.hs σ.b (walSnapCS σ cs) $$ [$Hinit $Hmeta $Hfresh]
    as %hp %csp ⟨#Hhs, Hmeta, Hfresh, #Hcs⟩
  iapply HΦ $$ %hp %csp %true
  iframe Hhs Hcs
  iintro %K #HA #HD
  ihave #HB : □ (∀ k, ⌜k ≤ σ.b⌝ -∗ (memStorJT γr.cl K (srvStoredOrigin γr.cl applied pin σ.b)).B k) $$ []
  · iintro !> %k %hk
    simp only [memStorJT]
    iapply memStorJ_B_off γr.cl K k Hns
    iapply nodeAppliedLb_mono γr.cl K _ k (by omega) $$ HA
  ihave Hsv : (⌜(walSnapCS σ cs).Metadata'.Index' = W64 0⌝ ∨
      (memStorJT γr.cl K (srvStoredOrigin γr.cl applied pin σ.b)).SV (walSnapCS σ cs) ∗
        (memStorJT γr.cl K (srvStoredOrigin γr.cl applied pin σ.b)).DL (uint.nat (walSnapCS σ cs).Metadata'.Index')) $$ [Hval]
  · by_cases h0 : σ.b = 0
    · ileft; ipureintro
      unfold StorContents.b at h0
      show σ.base.index' = W64 0
      apply BitVec.eq_of_toNat_eq; simpa using h0
    · icases Hval with (%H | #Hv)
      · exact absurd H h0
      iright
      simp only [memStorJT, memStorJ]
      isplitr
      · iframe Hv
        iunfold srvStoredOrigin
        ileft; ipureintro; rw [walSnapCS_index]; exact Nat.le_refl _
      rw [walSnapCS_index]
      iapply nodeCommitLb_mono γr.cl K _ _ Hbc $$ HD
  imod memStorInvP_alloc ms γs (memStorJT γr.cl K (srvStoredOrigin γr.cl applied pin σ.b)) ⊤ σ.b (walSnapCS σ cs) $$ Hl Hfresh HB Hsv
    with #Hinv
  ihave #Hinv' : memStorInvT ms γs γr.cl K (srvStoredOrigin γr.cl applied pin σ.b) $$ []
  · unfold memStorInvT; iexact Hinv
  ihave HFK := HF $$ %K Hinv' Hmeta Hsn
  imodintro
  isplitr
  · ihave #Hstorage := memStorage_isStorageT wp_LastIndex wp_FirstIndex wp_Term wp_Entries wp_Snapshot
      ms γs γr.cl K (srvStoredOrigin γr.cl applied pin σ.b) (fun _ => hsz) htr $$ Hinv' Hreg
    iExactEq Hstorage; rfl
  iframe HFK
  iunfold storHolds
  simp only [Nat.sub_self, List.take_zero, List.drop_zero]
  iexists memDummy (walSnapCS σ cs)
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply memStorCompacted_of ms γs σ.b $$ Hreg Hc
  isplitr
  · iapply memStorLog_of ms γs σ.b DFrac.discard _ $$ Hreg He0
  isplitr
  · iapply memStorLog_of ms γs (σ.b + 1) DFrac.discard [] $$ Hreg
    iapply memLog_nil
  isplitl [Hents]
  · iapply memStorLog_of ms γs (σ.b + 1) (DFrac.own 1) σ.ents $$ Hreg Hents
  iapply memStorEnd_of ms γs (σ.last + 1) $$ Hreg Hend

/-- **The composition's statement** (see the file header; 2026-10-27: over the node API, for the
server's raft names `γr` and the cluster's storage model `srvStor γr`): for the receiver `b` and the
config `cv` and the peers of the boot configuration (`rnStartCfg`):
`bootstrappedRaft.newRaftNode` over the node API's `StartNode`, with what the allocation, the server
and the trust boundary provide, yields the wrapper's struct value, the tokens, the receiver and the
peers' slice back, and the installer of `isRaftNode` at the address the server copies the struct
to (which takes the server's names and raft invariant in `rnEnvOk`). -/
abbrev NodeStartSpec : Prop :=
  ∀ (γr : SrvRaft) (E : RNEnv GF) (b ss wal cl : Loc) (sd : GoString) (dq : DFrac)
    (bv : bootstrappedRaft) (cv : Config) (lok : GoInterfaceOk) (γs : MemStorNames)
    (hw : WalH GF)
    (pv : List Peer) (ps : List w64) (ctxs : List (List w8)) (issued : GName),
    letI : MemStorReg GF := ⟨γr.reg⟩
    letI := srvStor (GF := GF) γr
    {{ "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        -- the pure premises, one conjunction (2026-11-05, the user's M1: until then implications
        -- before the triple): the configuration and the peers (`rnStartCfg`, shared with
        -- `bootstrappedRaft.newRaftNode.spec` and `bootOk`), a positive heartbeat
        -- (`newRaftNode`'s, a scope restriction), the peers distinct, non-zero and fewer than
        -- `2 ^ 62`, the cluster's voters (the start's configuration view, `srvCfgOk`), the WAL read
        -- (`NewStorage`'s contract), and the time-receipt bound past the bootstrap log
        -- (`rnLogFits`). (2026-11-05, the review's S: until then also `cv.ID' ∈ ps` and the
        -- server's names `E.γr.raft = ⟨γr, [], 0⟩`, which nothing here uses: the installer's
        -- `rnEnvOk` ties the names.)
        "%Hraft" ∷ ⌜rnStartCfg bv cv lok pv ps ∧ 0 < sint.Z bv.heartbeat' ∧
          ps.Nodup ∧ W64 0 ∉ ps ∧ (ps.length : Int) < 2 ^ 62 ∧ γr.vs = ps ∧
          wal = hw.w ∧ receiptBound GF + γr.boot.length ≤ 2 ^ 61 ∧
          -- (2026-11-09, Q8 stage 0) the cluster untraced (`srvClusterOk`'s)
          Cluster.trace γr.cl = none⌝ ∗
        -- (premise-fixes-6) the wrapper's logger a zap logger (`newRaftNode` logs through it)
        "#Hlgz" ∷ zapLoggerOk bv.lg' ∗
        -- the receiver, the config and its logger
        "Hb" ∷ b ↦{dq} bv ∗ "Hc" ∷ bv.config' ↦ cv ∗ "#Hlok" ∷ isLogger lok ∗
        -- (2026-10-30, the repair) the fresh registered `MemoryStorage`, as `NewMemoryStorage`
        -- leaves it (raft's two-writer specs): its lock, its fresh state, its hard state, its
        -- dummy entry and end; `StartNode`'s `bootStorage` over it (`srvMem_bootStorage`), whose
        -- `InitialState` allocates the storage's invariant at the node's justifications
        "#Hreg" ∷ memStorReg bv.storage' γs ∗
        -- (out_size C2) sized (`bootOk`'s `Hγsz`): the server's cluster bounds proposed data
        "%Hγsz" ∷ ⌜γs.sz = true⌝ ∗
        "#Hlock" ∷ memStorLock bv.storage' γs ∗
        "Hfresh" ∷ memStorFresh bv.storage' γs 0 memSnapEmpty ∗
        "Hmeta" ∷ memStorMeta bv.storage' γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
        "#Hlog0" ∷ memLog γs 0 DFrac.discard [zero_val EntryM] ∗ "Hend" ∷ memEnd γs 1 ∗
        -- the peers, their contexts
        "Hpeers" ∷ bv.peers' ↦*{dq} pv ∗ "#Hctx" ∷ peersCtx pv ctxs ∗
        -- the cluster's allocation's: this node's boot token (2026-10-30, the repair: raft's
        -- unified `cluster_alloc` with the bootstrap log), with (2026-11-01, durability layer 4)
        -- its vacant id and its durable state at `RaftState.init` (2026-11-05: until then also the
        -- server's raft invariant `srvRaftLogInv E.γr.raft`, which the installer's `rnEnvOk` holds)
        "Hboot" ∷ (nodeBoot γr.cl srvClusterN ps ctxs cv.ID' ∗ raftState γr.cl cv.ID' RaftState.init ∗
          nodeVacant γr.cl cv.ID') ∗
        -- the names-only contracts
        -- (premises to axioms, 2026-11-24: `rnLoggerZapOk`, `rnTimeoutDetectorOk` gone, now `newRaftNode`'s callees' trust-boundary specs)
        "#Hrs" ∷ rnRaftStatusOk ∗
        "#Hcl" ∷ rnClusterOk cl ∗
        -- (wal-link L3) the snapshotter (`NewStorage`'s precondition)
        "#Hssi" ∷ snap.isSnapshotter ss sd ∗
        -- (P5, 2026-11-25: until then the WAL's durability `rnDurInv` allocated by the caller,
        -- `wal.bootOk_start`) the open WAL's empty history (`wal.bootOk_startK`): the crash-aware
        -- durability is allocated in `bootstrappedRaft.newRaftNode`, once the node is started
        "Hwrec" ∷ walHistH hw [] true }}
      (App (App (App (Val (b @!! go.GoType.PointerType bootstrappedRaft.ty @!! go!"newRaftNode"))
        (Val #ss)) (Val #wal)) (Val #cl))
    {{ (r : Loc), RET #r;
        ∃ (γw : RNNames GF) (rv : raftNode),
          ⌜γw.node = γr ∧ γw.id = cv.ID' ∧ γw.pre = [] ∧ γw.ms = bv.storage' ∧ γw.γs = γs ∧
            γw.wal.h = hw ∧ γw.walK.sd = (fun _ => iprop(True)) ∧ γw.ss = ss ∧ γw.a0 = [] ∧ γw.t0 = W64 0 ∧ γw.snap0 = 0 ∧
            rv.lg' = bv.lg' ∧ rv.raftNodeConfig'.raftStorage' = bv.storage' ∧
            rv.raftNodeConfig'.heartbeat' = bv.heartbeat' ∧
            rv.raftNodeConfig'.transport' = GoInterface.nil ∧
            rv.raftNodeConfig'.Node' = rnNodeIface γw⌝ ∗
          -- (wal-link L3: until then the pure `rnStorageOf … ss ∧ storage.walOf … = wal`) the storage over the
          -- open WAL `ν.h` and the snapshotter `ss`, with its two reader tokens (the loop's, the apply thread's)
          isWalStorage rv.raftNodeConfig'.storage' γw.wal.h γw.ss ∗
          walStorRd rv.raftNodeConfig'.storage' γw.wal.h ∗ walStorRd rv.raftNodeConfig'.storage' γw.wal.h ∗
          -- the struct value, to be copied; its fresh mutex
          r ↦ rv ∗ rv.tickMu' ↦ (zero_val sync.RWMutex) ∗
          -- (D21 M2) the node's inbound methods (`Process`'s), from the start
          rnStepIfc γw (rnNodeIface γw) ∗
          -- (2026-11-05, the lease-expiry plan's E2 revision 5) the node made by `StartNode`
          nodeStartedFresh γw.nl γr.cl srvClusterN ps ctxs cv.ID' ∗
          -- `isServerBuilt`'s rows but `isRaftNode`; (2026-10-30, the repair) the apply side's
          -- half of the node's running token (`StartNode`'s `nodeRunning 1`, the other half in
          -- `rnLoopTok`)
          rnLoopTok γw [] ∗ rnApplyTok γw [] ∗ (letI := srvStor (GF := GF) γw.node; nodeRunning γw.nl γw.node.cl srvClusterN (1 : Qp).half) ∗
          -- the installer: `isRaftNode` and `rnWorkerStartTok` at the address `a` the struct is copied
          -- to, once its `transport` is set to `tr`, with the server's own: `rnEnvOk` for the
          -- wrapper's names, the committed index's invariant of the server `s` and the read
          -- contexts' invariant (2026-10-27); (2026-11-05, R2b-3d stage 5c) the `transport` field
          -- read-only already (the caller's environment's `Stop` names it, `srvTrStop`)
          (∀ (a s : Loc) (tr : GoInterface), rnEnvOk E γw -∗ srvCommittedInv s E.γr -∗
            srvRdCtxInv E.γr.raft issued -∗
            rnFixed a rv -∗ rnTransportAddr a ↦□ tr -∗ rnLatestTickTsAddr a ↦ rv.latestTickTs' -∗
            rnReplayTermsAddr a ↦ rv.raftNodeConfig'.initialReplayTerms' -∗
            isRNTransport E tr -∗ rv.tickMu' ↦ (zero_val sync.RWMutex) -∗
            -- (srvloops2, 2026-11-21) the bound `tickMu`'s pool of reader slots needs
            ⌜threadBound GF ≤ 2 ^ 29⌝ ={⊤}=∗
            isRaftNode E γw a ∗ rnWorkerStartTok γw a ∗
            rnNodeAddr a ↦□ rnNodeIface γw ∗ raftPropose E.γr.raft (rnNodeIface γw) ∗
            rnTransportAddr a ↦□ tr) ∗
          -- the receiver and (2026-11-05: until then kept, as the node API's `StartNode` did until
          -- it gave it back) the peers' slice
          b ↦{dq} bv ∗ bv.peers' ↦*{dq} pv ∗
          -- (2026-10-30, the repair) the storage's invariant at the justifications of its key (the
          -- wrapper's, `γw.key`; `memStorInv`, allocated by `InitialState`, `restartStorage`'s
          -- frame) and its hard state
          srvAttachedMem bv.storage' γs γr.cl γw.key E.γr.cursor γw.nl γw.snap0 ∗
          memStorMeta bv.storage' γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
          -- (2026-11-04, R2b-3d) the claim on the loop's stop escrow, kept for the server's stop
          rnStopClaim γw ∗
          -- (P5) the crash-aware durability and the stop's and the apply thread's WAL tokens
          rnDurInvK γw.node γw.id γw.walK γw.wal.h ∗ token γw.wal.stop ∗ token γw.wal.app }}


/-- (restart S3 item 8, D5, 2026-11-11) **The composition's statement at a restart** (beside
`NodeStartSpec`, which stays the first start's: D5, so that `NewServer.lean` is untouched until S6):
`bootstrappedRaft.newRaftNode` over the node API's `RestartNode` (the boot `.restart σ cs S a' m A₀`, at
the configuration point `a' = min |A₀| σ.commit`: 2026-11-24, d6 step 3, until then `|A₀|`),
for the WAL's records `σ`, the backend's conf state `cs` and committed log `A₀` (its consistent index
`|A₀|` between the records' base and commit), the node's durable state `S` held by the records: the
storage `bootstrappedWAL.MemoryStorage` rebuilt (`memStorRestarted`; `srvMem_restartStorage`, its
snapshot valid by `walSnapCS_valid`), the WAL's durability at the view `⟨S, σ.hs, none, P⟩` with
`P = A₀.take σ.b` (`rnDur_alloc_view`, W4's records); yields the wrapper with the tokens at `P`
(Q34 (a); `rnToks_of_restart`), the names' restart data (`a0 = A₀`, `t0` the restored term, `commit0`,
`snap0` the restored commit and base), and the installer. (restart3 A1, 2026-11-15: until then the
installer took the restart-only premise `rnSnapTermAbove`, row 4, for `isRaftNode`'s `rnRestartOk`.)
(2026-11-24, d6 step 3) `|A₀| ≤ σ.commit` is no longer `RestartNode`'s (its point is `a'`); it stays
for `rnRestartOk`'s restart disjunct and `replaySeed_facts` (d6 T4 round 4, items 2 and 3). -/
abbrev NodeStartSpecR : Prop :=
  ∀ (γr : SrvRaft) (E : RNEnv GF) (b ss wal cl : Loc) (sd : GoString) (dq : DFrac)
    (bv : bootstrappedRaft) (cv : Config) (lok : GoInterfaceOk) (γs : MemStorNames)
    (hw : WalH GF) (pv : List Peer) (ctxs : List (List w8)) (issued : GName)
    (σ : StorContents) (cs : ConfStateM) (S : RaftState) (m : Membership) (A₀ : List EntryModel),
    letI : MemStorReg GF := ⟨γr.reg⟩
    letI := srvStor (GF := GF) γr
    {{ "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        -- the pure premises: the restart's configuration (`rnRestartCfg`), a positive heartbeat, the
        -- WAL read, the receipts' bound (`rnLogFits`), the voters within raft's bounds (the view's
        -- `srvCfgOk`), the backend's consistent index between the records' base and commit, the
        -- bootstrap log within the commit, the records holding `S`, the snapshot record's term the
        -- base's, the backend's conf state the voters' (D4, S6's) within raft's bounds
        "%Hraft" ∷ ⌜rnRestartCfg bv cv lok pv ∧ 0 < sint.Z bv.heartbeat' ∧ wal = hw.w ∧
          receiptBound GF + γr.boot.length ≤ 2 ^ 61 ∧ W64 0 ∉ γr.cfg ∧ GMap.size γr.cfg < 2 ^ 62 ∧
          σ.b ≤ A₀.length ∧ A₀.length ≤ σ.commit ∧ γr.cl.bootLen ≤ σ.commit ∧ StorageHolds S σ ∧
          (∀ m' : SnapshotMetadataM, σ.snap = some (SnapshotM.mk [] m') → m'.Term' = σ.base.term') ∧
          confStateIs cs (Membership.simple γr.cfg) ∧
          (cs.Voters'.length + cs.Learners'.length + cs.VotersOutgoing'.length +
            cs.LearnersNext'.length : Int) ≤ 2 ^ 62 ∧
          -- (auth-lease S4, 2026-11-16) outside the cluster's no-snapshot mode (`RestartNode`'s)
          ¬ clusterNoSnap γr.cl⌝ ∗
        "#Hlgz" ∷ zapLoggerOk bv.lg' ∗
        "Hb" ∷ b ↦{dq} bv ∗ "Hc" ∷ bv.config' ↦ cv ∗ "#Hlok" ∷ isLogger lok ∗
        -- the registered `MemoryStorage` as `bootstrappedWAL.MemoryStorage` rebuilds it
        "#Hreg" ∷ memStorReg bv.storage' γs ∗ "#Hlock" ∷ memStorLock bv.storage' γs ∗
        "Hrest" ∷ memStorRestarted bv.storage' γs σ cs ∗
        -- (out_size C3, 2026-11-12) sized (`bootOkR`'s `Hγsz`): the storage rebuilt from sized WAL
        -- files (`srvFiles`)
        "%Hγsz" ∷ ⌜γs.sz = true⌝ ∗
        "Hpeers" ∷ bv.peers' ↦*{dq} pv ∗ "#Hctx" ∷ peersCtx pv ctxs ∗
        -- the restart image's: the cluster, its receipts' bound, the id vacant, the durable state,
        -- the configuration at the backend's index, the server's raft-log invariant, the backend's
        -- log committed, the records' snapshot certificate
        "#Hclu" ∷ isCluster γr.cl srvClusterN ∗ "#Hrf" ∷ readyFits γr.cl srvClusterN ∗
        "Hvac" ∷ (∃ x, nodeVacantA γr.cl cv.ID' x) ∗ "HrS" ∷ raftState γr.cl cv.ID' S ∗
        "#Hconf" ∷ confAt γr.cl A₀.length m ∗
        "#Hlinv" ∷ srvRaftLogInv ⟨γr, [], W64 0⟩ ∗ "#HA0" ∷ srvRLogLb ⟨γr, [], W64 0⟩ A₀ ∗
        "#Hcert" ∷ walSnapCert γr.cl σ ∗
        -- the names-only contracts
        -- (premises to axioms, 2026-11-24: `rnLoggerZapOk`, `rnTimeoutDetectorOk` gone, now `newRaftNode`'s callees' trust-boundary specs)
        "#Hrs" ∷ rnRaftStatusOk ∗
        "#Hcl" ∷ rnClusterOk cl ∗
        -- (wal-link L3) the snapshotter (`NewStorage`'s precondition)
        "#Hssi" ∷ snap.isSnapshotter ss sd ∗
        -- (P5, 2026-11-25: until then the WAL's durability `rnDurInv` allocated by the caller at the
        -- restart's view) the restart's handover of the WAL (`rnRestartWal`), the records within the
        -- restart's view `⟨S, σ.hs, none, P⟩` and `P` committed: the crash-aware durability is
        -- allocated in `bootstrappedRaft.newRaftNode` (the isolated restart step, `rnRestartAllocK.law`)
        "Hwrec" ∷ rnRestartWal hw σ ∗
        "%Hwvok" ∷ ⌜ViewOk ⟨S, σ.hs, none, srvLE ⟨γr, [], W64 0⟩ (A₀.take σ.b)⟩ σ⌝ ∗
        "#HP" ∷ isCommittedLogLb γr.cl (srvLE ⟨γr, [], W64 0⟩ (A₀.take σ.b)) }}
      (App (App (App (Val (b @!! go.GoType.PointerType bootstrappedRaft.ty @!! go!"newRaftNode"))
        (Val #ss)) (Val #wal)) (Val #cl))
    {{ (r : Loc), RET #r;
        ∃ (γw : RNNames GF) (rv : raftNode),
          ⌜γw.node = γr ∧ γw.id = cv.ID' ∧ γw.pre = [] ∧ γw.ms = bv.storage' ∧ γw.γs = γs ∧
            γw.wal.h = hw ∧ γw.walK.sd = (fun _ => iprop(True)) ∧ γw.ss = ss ∧ γw.a0 = A₀ ∧ γw.t0 = σ.hs.Term' ∧ γw.commit0 = σ.commit ∧
            γw.snap0 = σ.b ∧
            rv.lg' = bv.lg' ∧ rv.raftNodeConfig'.raftStorage' = bv.storage' ∧
            rv.raftNodeConfig'.heartbeat' = bv.heartbeat' ∧
            rv.raftNodeConfig'.transport' = GoInterface.nil ∧
            rv.raftNodeConfig'.Node' = rnNodeIface γw⌝ ∗
          isWalStorage rv.raftNodeConfig'.storage' γw.wal.h γw.ss ∗
          walStorRd rv.raftNodeConfig'.storage' γw.wal.h ∗ walStorRd rv.raftNodeConfig'.storage' γw.wal.h ∗
          r ↦ rv ∗ rv.tickMu' ↦ (zero_val sync.RWMutex) ∗
          rnStepIfc γw (rnNodeIface γw) ∗
          -- the tokens at `P` (Q34 (a))
          rnLoopTok γw (A₀.take σ.b) ∗ rnApplyTok γw (A₀.take σ.b) ∗
          (letI := srvStor (GF := GF) γw.node; nodeRunning γw.nl γw.node.cl srvClusterN (1 : Qp).half) ∗
          -- the installer
          (∀ (a s : Loc) (tr : GoInterface), rnEnvOk E γw -∗ srvCommittedInv s E.γr -∗
            srvRdCtxInv E.γr.raft issued -∗
            rnFixed a rv -∗ rnTransportAddr a ↦□ tr -∗ rnLatestTickTsAddr a ↦ rv.latestTickTs' -∗
            rnReplayTermsAddr a ↦ rv.raftNodeConfig'.initialReplayTerms' -∗
            isRNTransport E tr -∗ rv.tickMu' ↦ (zero_val sync.RWMutex) -∗
            -- (srvloops2, 2026-11-21) the bound `tickMu`'s pool of reader slots needs
            ⌜threadBound GF ≤ 2 ^ 29⌝ ={⊤}=∗
            isRaftNode E γw a ∗ rnWorkerStartTok γw a ∗
            rnNodeAddr a ↦□ rnNodeIface γw ∗ raftPropose E.γr.raft (rnNodeIface γw) ∗
            rnTransportAddr a ↦□ tr) ∗
          b ↦{dq} bv ∗ bv.peers' ↦*{dq} pv ∗
          srvAttachedMem bv.storage' γs γr.cl γw.key E.γr.cursor γw.nl γw.snap0 ∗ memStorMeta bv.storage' γs σ.hs ∗
          -- (restart S6 B2, 2026-11-14) the storage's snapshot not yet opened for writes, the WAL's
          -- (which `run`'s `Snapshot()` answers: `restart_snapOnceR`)
          memSnapNone γs (walSnapCS σ cs) ∗
          rnStopClaim γw ∗
          -- (P5) the crash-aware durability and the stop's and the apply thread's WAL tokens
          rnDurInvK γw.node γw.id γw.walK γw.wal.h ∗ token γw.wal.stop ∗ token γw.wal.app }}

end compose

end EtcdGrove
end Perennial
