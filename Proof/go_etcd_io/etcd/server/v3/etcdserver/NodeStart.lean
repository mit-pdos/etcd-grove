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
* the contracts (`rnLoggerZapOk`, `rnTimeoutDetectorOk`, `rnNewStorageOk`,
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
      -- (restart S3 item 7) the restart data
      rnRestartOk γ ∗
      (letI : MemStorReg GF := ⟨γ.reg⟩; memStorReg γ.ms γ.γs) ∗
      isRaftNodeIfc E γ rv.raftNodeConfig'.Node' ∗
      isRNIDRemoved rv.raftNodeConfig'.isIDRemoved' ∗
      ⌜rv.raftNodeConfig'.raftStorage' = γ.ms⌝ ∗ isRNMemStor γ γ.ms ∗
      isWalStorage rv.raftNodeConfig'.storage' ∗
      -- (2026-11-03, R2b-1 stage 3c) the WAL's durability invariant
      rnDurInv γ.node.cl γ.wal (storage.walOf rv.raftNodeConfig'.storage') ∗
      isRNTransport E rv.raftNodeConfig'.transport' ∗
      rnParts E γ rv ∗
      rnFixed a rv ∗ rnTransportAddr a ↦□ rv.raftNodeConfig'.transport' ∗
      rnLatestTickTsAddr a ↦ rv.latestTickTs' ∗ rv.tickMu' ↦ (zero_val sync.RWMutex) ∗
      ownBroadcastChan rv.done' γ.done (rnDoneEsc γ (storage.walOf rv.raftNodeConfig'.storage'))
        .Pending ⊢
      |={⊤}=> isRaftNode E γ a ∗ rnDoneTok γ a ∗
        rnNodeAddr a ↦□ rv.raftNodeConfig'.Node' ∗
        rnTransportAddr a ↦□ rv.raftNodeConfig'.transport' := by
  iintro ⟨#Hpkg, #Henv, #Hfits, #Hrsb, #Hrok, #Hreg, #Hni, #Hidri, %Hmsγ, #Hmsi, #Hsti, #Hdur, #Htri, #Hparts,
    #Hfix, #transportC, latestTickTsR, Hmu, Hdtok⟩
  iunfold rnParts at Hparts
  iNamed Hparts
  iunfold rnFixed at Hfix
  iNamed Hfix
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  imod sync.init_RWMutex (rnTickInv a) rv.tickMu' $$ [latestTickTsR] Hmu with Hslots
  · inext; iunfold rnTickInv; iexists rv.latestTickTs'; iexact latestTickTsR
  icases sync.ownRWMutex_slots_guard _ _ $$ Hslots with ⟨-, #Hmug⟩
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
    rw [Hmsγ]
    iexact Hmsi
  · iframe NodeC transportC
    iunfold rnDoneTok
    iexists rv.done', rv.raftNodeConfig'.storage'
    iframe doneR Hdtok
    iexact storageC

/-- **The loop's and the apply side's tokens at the start** (`rnLoopTok γ []`, `rnApplyTok γ
[]`): from the node API's driver at its start (`NodeDriverState.init`: nothing delivered, with
`γ.pre = []`), its view of the configuration at index `0` (`StartNode`'s; 2026-10-30, the repair:
in every cluster), the loop's half of the running token, and `applyc`'s halves with `cum` at
`[[]]` (`newRaftNode`'s). (2026-10-27: over the node API. 2026-11-01, durability layer 4: the
driver at the storage's key `γ.key`, and the node's durable state at `RaftState.init`, which goes
into the loop's token beside the driver.) -/
theorem rnToks_of_start (γ : RNNames) (hpre : γ.pre = []) (ha : γ.a0 = []) (ht : γ.t0 = W64 0)
    (hc0 : γ.commit0 = 0) (hs0 : γ.snap0 = 0)
    (hcfg : srvCfgOk γ.node.cfg [] ⟨0, Membership.simple γ.node.cfg⟩) :
    (letI := srvStor (GF := GF) γ.node;
      iprop(nodeDriver γ.nl γ.node.cl srvClusterN
          (NodeDriverState.init (memStorIface γ.ms) γ.key) ∗
        raftState γ.node.cl γ.id RaftState.init ∗
        nodeConfig γ.nl γ.node.cl srvClusterN ⟨0, Membership.simple γ.node.cfg⟩)) ∗ (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ∗
      sspscProducer γ.ap ([] : List toApply) ∗ sspscConsumer γ.ap ([] : List toApply) ∗
      monoListAuthOwn γ.cum 1 [([] : List EntryModel)] ∗
      monoListIdxOwn γ.cum 0 ([] : List EntryModel) ∗
      -- (2026-11-03, R2b-1 stage 4) the loop's view of the WAL at the start (`wal.bootOk_start`)
      ghostVar γ.wal.view (1 : Qp).half walView0 ∗ token γ.wal.ok ⊢
      rnLoopTok γ [] ∗ rnApplyTok γ [] := by
  letI := srvStor (GF := GF) γ.node
  iintro ⟨⟨Hdrv, HrS, Hcfg⟩, Hrun, Hprod, Hcons, Hcum, Hcum0, Hwv, Hwok⟩
  -- (S1) the log handed out (none) committed, from the driver's delivered log
  ihave ⟨Hdrv, #Hdl⟩ := nodeDriver_deliveredLogLb γ.nl γ.node.cl srvClusterN _ $$ Hdrv
  ihave #HcL0 : isCommittedLogLb γ.node.cl (srvLE γ.srv []) $$ []
  · have h : srvLE γ.srv [] = (NodeDriverState.init (memStorIface γ.ms) γ.key).delivered := by
      simp [srvLE, NodeDriverState.init, RNNames.srv, hpre]
    rw [h]; iapply deliveredLogLb_committed $$ Hdl
  isplitl [Hdrv HrS Hcfg Hrun Hprod Hcum Hwv Hwok]
  · iunfold rnLoopTok
    iexists hsZero
    iunfold rnLoopTokP
    iexists [], [[]], RaftState.init, W64 0
    isplitl [Hdrv HrS Hcfg]
    · iunfold rnDrv
      have h : rnDrvSt γ [] hsZero RaftState.init (W64 0) =
          NodeDriverState.init (memStorIface γ.ms) γ.key := by
        simp [rnDrvSt, NodeDriverState.init, srvLE, RNNames.srv, hpre]
      rw [h]
      iframe Hdrv HrS
      iapply ((rnView_first γ ha).1 ⟨ht, hc0, hs0⟩ []).2
      unfold srvCfgView
      iexists ⟨0, Membership.simple γ.node.cfg⟩
      iframe Hcfg
      ipureintro
      simp only [RNNames.srv, hpre, List.append_nil]
      exact hcfg
    isplitr
    · ipureintro; intro h; cases h
    isplitl [Hwv Hwok]
    · iunfold rnWalView
      have h0 : (⟨RaftState.init, hsZero, none, srvLE γ.srv []⟩ : WalView) = walView0 := by
        simp [srvLE, RNNames.srv, hpre, walView0]
      rw [h0]
      iframe Hwv Hwok
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
theorem rnToks_of_restart (γ : RNNames) (P : List EntryModel) (p : HardStateM) (S : RaftState)
    (v : ConfigView) (hpre : γ.pre = []) (hidx : srvIdxOkW (W64 0) P)
    (hc0 : γ.commit0 ≤ uint.nat p.Commit')
    (hcfg : srvCfgOk γ.node.cfg (rnGhost γ P) v) :
    (letI := srvStor (GF := GF) γ.node;
      iprop(nodeDriver γ.nl γ.node.cl srvClusterN
          ⟨memStorIface γ.ms, srvLE γ.srv P, p, none, γ.key, S, StateFollower⟩ ∗
        raftState γ.node.cl γ.id S ∗
        nodeConfig γ.nl γ.node.cl srvClusterN v)) ∗
      (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ∗
      sspscProducer γ.ap ([] : List toApply) ∗ sspscConsumer γ.ap ([] : List toApply) ∗
      monoListAuthOwn γ.cum 1 [P] ∗ monoListIdxOwn γ.cum 0 P ∗
      ghostVar γ.wal.view (1 : Qp).half (⟨S, p, none, srvLE γ.srv P⟩ : WalView) ∗ token γ.wal.ok ∗
      srvFrozenTerms γ.γs 1 P ⊢
      rnLoopTok γ P ∗ rnApplyTok γ P := by
  letI := srvStor (GF := GF) γ.node
  iintro ⟨⟨Hdrv, HrS, Hcfg⟩, Hrun, Hprod, Hcons, Hcum, Hcum0, Hwv, Hwok, #Hfz⟩
  ihave ⟨Hdrv, #Hdl⟩ := nodeDriver_deliveredLogLb γ.nl γ.node.cl srvClusterN _ $$ Hdrv
  ihave #HcL : isCommittedLogLb γ.node.cl (srvLE γ.srv P) $$ []
  · iapply deliveredLogLb_committed $$ Hdl
  isplitl [Hdrv HrS Hcfg Hrun Hprod Hcum Hwv Hwok]
  · iunfold rnLoopTok
    iexists p
    iunfold rnLoopTokP
    iexists [], [P], S, StateFollower
    isplitl [Hdrv HrS Hcfg]
    · iunfold rnDrv
      have h : rnDrvSt γ P p S StateFollower =
          ⟨memStorIface γ.ms, srvLE γ.srv P, p, none, γ.key, S, StateFollower⟩ := rfl
      rw [h]
      iframe Hdrv HrS
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
    isplitl [Hwv Hwok]
    · iunfold rnWalView
      iframe Hwv Hwok
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
    (γr : SrvRaft) (ms : Loc) (γs : MemStorNames) (F : GName → IProp GF)
    (hsz : γs.sz = true) :
    letI : MemStorReg GF := ⟨γr.reg⟩
    letI := srvStor (GF := GF) γr
    memStorReg ms γs ∗ memStorLock ms γs ∗ memStorFresh ms γs 0 memSnapEmpty ∗
      memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
      memLog (GF := GF) γs 0 DFrac.discard [(zero_val EntryM : EntryM)] ∗ memEnd (GF := GF) γs 1 ∗
      (∀ K : GName, memStorInv ms γs γr.cl K -∗
        memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) -∗ F K) ⊢
      restartStorage γr.cl (memStorIface ms)
        ⟨HardStateM.mk (W64 0) (W64 0) (W64 0), none, entryID.mk (W64 0) (W64 0), []⟩
        memSnapEmpty.Metadata'.ConfState' 0 F := by
  letI : MemStorReg GF := ⟨γr.reg⟩
  letI := srvStor (GF := GF) γr
  iintro ⟨#Hreg, #Hl, Hfresh, Hmeta, #Hlog, He, HF⟩
  ihave #Hinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iunfold memStorLock at Hl; icases Hl with ⟨#H, -⟩; iexact H
  unfold restartStorage
  iexists (⟨MemoryStorage.ty.PointerType, intoVal ms⟩ : GoInterfaceOk)
  iexists iprop(memStorFresh ms γs 0 memSnapEmpty ∗
    memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗ memEnd γs 1 ∗
    (∀ K : GName, memStorInv ms γs γr.cl K -∗
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
  imod memStorInvP_alloc ms γs (memStorJ γr.cl K) ⊤ 0 memSnapEmpty $$ Hl Hfresh [] [] with #Hinv
  · iintro !> %k %hk
    have : k = 0 := by omega
    subst this
    unfold memStorJ
    iapply nodeAppliedLb_zero γr.cl K
  · ileft; ipureintro; rfl
  ihave #Hinv' : memStorInv ms γs γr.cl K $$ []
  · unfold memStorInv; iexact Hinv
  ihave HFK := HF $$ %K Hinv' Hmeta
  imodintro
  isplitr
  · iapply memStorage_isStorage wp_LastIndex wp_FirstIndex wp_Term wp_Entries wp_Snapshot
      ms γs γr.cl K (fun _ => hsz) $$ Hinv' Hreg
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
    (γr : SrvRaft) (ms : Loc) (γs : MemStorNames) (σ : StorContents) (cs : ConfStateM) (A : Nat)
    (F : GName → IProp GF) (Hbc : σ.b ≤ σ.commit) (hsz : γs.sz = true) :
    letI : MemStorReg GF := ⟨γr.reg⟩
    letI := srvStor (GF := GF) γr
    memStorReg ms γs ∗ memStorLock ms γs ∗ memStorRestarted ms γs σ cs ∗
      (⌜σ.b = 0⌝ ∨ snapshotValid γr.cl (walSnapCS σ cs)) ∗
      (∀ K : GName, memStorInv ms γs γr.cl K -∗ memStorMeta ms γs σ.hs -∗ F K) ⊢
      restartStorage γr.cl (memStorIface ms) σ cs A F := by
  letI : MemStorReg GF := ⟨γr.reg⟩
  letI := srvStor (GF := GF) γr
  iintro ⟨#Hreg, #Hl, Hrest, Hval, HF⟩
  iunfold memStorRestarted at Hrest
  icases Hrest with ⟨Hfresh, Hmeta, #Hc, #He0, #Hslb, Hents, Hend⟩
  ihave #Hinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iunfold memStorLock at Hl; icases Hl with ⟨#H, -⟩; iexact H
  unfold restartStorage
  iexists (⟨MemoryStorage.ty.PointerType, intoVal ms⟩ : GoInterfaceOk)
  iexists iprop(memStorFresh ms γs σ.b (walSnapCS σ cs) ∗ memStorMeta ms γs σ.hs ∗
    memLog γs (σ.b + 1) (DFrac.own 1) σ.ents ∗ memEnd γs (σ.last + 1) ∗
    (⌜σ.b = 0⌝ ∨ snapshotValid γr.cl (walSnapCS σ cs)) ∗
    (∀ K : GName, memStorInv ms γs γr.cl K -∗ memStorMeta ms γs σ.hs -∗ F K))
  iexists σ.b
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact ⟨Nat.le_refl _, Hbc⟩
  isplitl [Hfresh Hmeta Hents Hend Hval HF]
  · iframe Hfresh Hmeta Hents Hend Hval HF
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
  iintro !> %Φ ⟨Hfresh, Hmeta, Hents, Hend, Hval, HF⟩ HΦ
  wp_apply wp_InitialState ms γs σ.hs σ.b (walSnapCS σ cs) $$ [$Hinit $Hmeta $Hfresh]
    as %hp %csp ⟨#Hhs, Hmeta, Hfresh, #Hcs⟩
  iapply HΦ $$ %hp %csp %true
  iframe Hhs Hcs
  iintro %K #HA #HD
  ihave #HB : □ (∀ k, ⌜k ≤ σ.b⌝ -∗ (memStorJ γr.cl K).B k) $$ []
  · iintro !> %k %hk
    simp only [memStorJ]
    iapply nodeAppliedLb_mono γr.cl K _ k (by omega) $$ HA
  ihave Hsv : (⌜(walSnapCS σ cs).Metadata'.Index' = W64 0⌝ ∨
      (memStorJ γr.cl K).SV (walSnapCS σ cs) ∗
        (memStorJ γr.cl K).DL (uint.nat (walSnapCS σ cs).Metadata'.Index')) $$ [Hval]
  · by_cases h0 : σ.b = 0
    · ileft; ipureintro
      unfold StorContents.b at h0
      show σ.base.index' = W64 0
      apply BitVec.eq_of_toNat_eq; simpa using h0
    · icases Hval with (%H | #Hv)
      · exact absurd H h0
      iright
      simp only [memStorJ]
      isplitr
      · iexact Hv
      rw [walSnapCS_index]
      iapply nodeCommitLb_mono γr.cl K _ _ Hbc $$ HD
  imod memStorInvP_alloc ms γs (memStorJ γr.cl K) ⊤ σ.b (walSnapCS σ cs) $$ Hl Hfresh HB Hsv
    with #Hinv
  ihave #Hinv' : memStorInv ms γs γr.cl K $$ []
  · unfold memStorInv; iexact Hinv
  ihave HFK := HF $$ %K Hinv' Hmeta
  imodintro
  isplitr
  · iapply memStorage_isStorage wp_LastIndex wp_FirstIndex wp_Term wp_Entries wp_Snapshot
      ms γs γr.cl K (fun _ => hsz) $$ Hinv' Hreg
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
  ∀ (γr : SrvRaft) (E : RNEnv GF) (b ss wal cl : Loc) (dq : DFrac)
    (bv : bootstrappedRaft) (cv : Config) (lok : GoInterfaceOk) (γs : MemStorNames)
    (ν : WalNames)
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
          storage.walReady wal ∧ receiptBound GF + γr.boot.length ≤ 2 ^ 61⌝ ∗
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
        "#Hzap" ∷ rnLoggerZapOk ∗ "#Htdok" ∷ rnTimeoutDetectorOk ∗
        "#Hrs" ∷ rnRaftStatusOk ∗ "#Hns" ∷ rnNewStorageOk ∗
        "#Hcl" ∷ rnClusterOk cl ∗
        -- (2026-11-03, R2b-1 stage 3c) the WAL's durability (`wal.bootOk_start`): its invariant, the
        -- loop's view at the start and its token
        "#Hdur" ∷ rnDurInv γr.cl ν wal ∗ "Hwview" ∷ ghostVar ν.view (1 : Qp).half walView0 ∗
        "Hwok" ∷ token ν.ok }}
      (App (App (App (Val (b @!! go.GoType.PointerType bootstrappedRaft.ty @!! go!"newRaftNode"))
        (Val #ss)) (Val #wal)) (Val #cl))
    {{ (r : Loc), RET #r;
        ∃ (γw : RNNames) (rv : raftNode),
          ⌜γw.node = γr ∧ γw.id = cv.ID' ∧ γw.pre = [] ∧ γw.ms = bv.storage' ∧ γw.γs = γs ∧
            γw.wal = ν ∧ γw.a0 = [] ∧
            rv.lg' = bv.lg' ∧ rv.raftNodeConfig'.raftStorage' = bv.storage' ∧
            rv.raftNodeConfig'.heartbeat' = bv.heartbeat' ∧
            rv.raftNodeConfig'.transport' = GoInterface.nil ∧
            rv.raftNodeConfig'.Node' = rnNodeIface γw ∧
            -- (D22 J1a) the storage a `*storage` over the snapshotter `ss`
            rnStorageOf rv.raftNodeConfig'.storage' ss ∧
            -- (2026-10-31) over the WAL `wal` (whose open token `bootstrap`'s contract gives)
            storage.walOf rv.raftNodeConfig'.storage' = wal⌝ ∗
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
          -- the installer: `isRaftNode` and `rnDoneTok` at the address `a` the struct is copied
          -- to, once its `transport` is set to `tr`, with the server's own: `rnEnvOk` for the
          -- wrapper's names, the committed index's invariant of the server `s` and the read
          -- contexts' invariant (2026-10-27); (2026-11-05, R2b-3d stage 5c) the `transport` field
          -- read-only already (the caller's environment's `Stop` names it, `srvTrStop`)
          (∀ (a s : Loc) (tr : GoInterface), rnEnvOk E γw -∗ srvCommittedInv s E.γr -∗
            srvRdCtxInv E.γr.raft issued -∗
            rnFixed a rv -∗ rnTransportAddr a ↦□ tr -∗ rnLatestTickTsAddr a ↦ rv.latestTickTs' -∗
            isRNTransport E tr -∗ rv.tickMu' ↦ (zero_val sync.RWMutex) ={⊤}=∗
            isRaftNode E γw a ∗ rnDoneTok γw a ∗
            rnNodeAddr a ↦□ rnNodeIface γw ∗ raftPropose E.γr.raft (rnNodeIface γw) ∗
            rnTransportAddr a ↦□ tr) ∗
          -- the receiver and (2026-11-05: until then kept, as the node API's `StartNode` did until
          -- it gave it back) the peers' slice
          b ↦{dq} bv ∗ bv.peers' ↦*{dq} pv ∗
          -- (2026-10-30, the repair) the storage's invariant at the justifications of its key (the
          -- wrapper's, `γw.key`; `memStorInv`, allocated by `InitialState`, `restartStorage`'s
          -- frame) and its hard state
          memStorInv bv.storage' γs γr.cl γw.key ∗
          memStorMeta bv.storage' γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
          -- (2026-11-04, R2b-3d) the claim on the loop's stop escrow, kept for the server's stop
          rnStopClaim γw }}

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
  intro γr E b ss wal cl dq bv cv lok γs ν pv ps ctxs issued
  letI : MemStorReg GF := ⟨γr.reg⟩
  letI := srvStor (GF := GF) γr
  iintro %Φ Hpre HΦ
  iNamed Hpre
  obtain ⟨Hcfg, Hhb, Hnodup, H0, Hpslen, Hvs, Hwal, Hfit⟩ := Hraft
  ihave Hbs := srvMem_bootStorage wp_InitialState wp_Snapshot wp_LastIndex wp_FirstIndex wp_Term
      wp_Entries γr bv.storage' γs
      (fun K => iprop(memStorInv bv.storage' γs γr.cl K ∗
        memStorMeta bv.storage' γs (HardStateM.mk (W64 0) (W64 0) (W64 0)))) Hγsz
      $$ [Hfresh Hmeta Hend]
  · iframe Hreg Hlock Hfresh Hmeta Hlog0 Hend
    iintro %K Hi Hm
    iframe Hi Hm
  icases Hboot with ⟨#Hnboot, HrS, Hvac⟩
  wp_apply (wp_bnr E γr b ss wal cl dq bv cv lok γs [] ν pv ps ctxs
    (fun K => iprop(memStorInv bv.storage' γs γr.cl K ∗
      memStorMeta bv.storage' γs (HardStateM.mk (W64 0) (W64 0) (W64 0)))) .fresh)
    $$ [Hb Hc Hbs Hpeers HrS Hvac]
    as %r Hpost
  · iframe #; iframe Hb Hc Hpeers
    isplitr
    · ipureintro; exact ⟨Hhb, Hwal⟩
    simp only [rnBootPre]
    isplitr
    · ipureintro; exact Hcfg
    isplitl [Hbs]
    · iExactEq Hbs; rfl
    isplitr
    · iExactEq Hnboot; rfl
    isplitl [Hvac]
    · iExactEq Hvac; rfl
    iExactEq HrS; rfl
  icases Hpost with ⟨%n, %γw, %f, %st, %Hnames, #Hnode, Hrun, Hbpost, #Hidri, #Hsti,
    %Hstss, Hbuilt, Hb, Hpeers, ⟨#Hminv, Hmeta⟩⟩
  simp only [rnBootPost, RNBoot.P]
  icases Hbpost with ⟨#Hsfresh, Hdrv, HrS, Hncfg⟩
  simp only [RNBoot.a0, RNBoot.t0, RNBoot.commit0, RNBoot.snap0] at Hnames
  obtain ⟨Hwnode, Hwid, Hwnl, Hwpre, Hwms, Hwγs, Hwwal, Hwa0, Hwt0, Hwc0, Hws0⟩ := Hnames
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
    iframe Hpraft Hreg'
    rw [Hwms, Hwγs]; iexact Hlock
  ihave #Hisnode : rnIsNode γw $$ []
  · unfold rnIsNode; rw [Hwnode, Hwid, Hwnl]; iexact Hnode
  -- the running token's halves
  icases ((nodeRunning_fractional n γr.cl srvClusterN).fractional (1 : Qp).half
      (1 : Qp).half).1 $$ [Hrun] with ⟨Hrun1, Hrun2⟩
  · rw [Qp.half_add_half]; iexact Hrun
  -- the tokens
  ihave ⟨Hloop, Happly⟩ := rnToks_of_start γw Hwpre Hwa0 Hwt0 Hwc0 Hws0
      (by
        rw [Hwnode]
        unfold SrvRaft.cfg
        rw [Hvs]
        refine srvCfgOk_nil _ (fun h0 => H0 ((GMap.elem_of_list_to_set _ _).1 h0)) ?_
        rw [GMap.size_list_to_set ps Hnodup]
        omega)
    $$ [Hdrv HrS Hncfg Hrun1 Hprod Hcons Hcum Hcum0 Hwview Hwok]
  · rw [Hwnode, Hwnl, Hwms, Hwid, Hwwal]
    iframe Hdrv HrS Hrun1 Hprod Hcons Hcum Hcum0 Hwview Hwok
    unfold SrvRaft.cfg
    rw [Hvs]
    iexact Hncfg
  iapply HΦ
  iexists γw, rv
  isplitr
  · ipureintro
    refine ⟨Hwnode, Hwid, Hwpre, Hwms, Hwγs, Hwwal, Hwa0, Hrvlg, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [Hrvcfg]
    all_goals first | exact Hstss | simp only [rnNodeIface, Hwnl]
  iframe Hr Hmu Hloop Happly Hb Hpeers Hminv Hmeta Hsc
  isplitr
  · iapply rnStepIfc_of_isNode γw (wp_Step γw.node) (wp_ReportUnreachable γw.node)
      (wp_ReportSnapshot γw.node)
    iframe Hpkg Hisnode
  isplitr
  · rw [Hwnl]; iexact Hsfresh
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
  ihave #Hlinv : srvRaftLogInv E.γr.raft $$ []
  · iunfold rnEnvOk at Henv'
    icases Henv' with ⟨-, -, -, #H, -⟩
    iexact H
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
    isplitr
    · iunfold rnRestartOk; ileft; ipureintro; exact ⟨Hwa0, Hwt0, Hwc0, Hws0⟩
    simp only [Hrvcfg]
    iframe Hidri Hsti Htri Hmsi
    isplitr
    · -- the node's contract, at the config's `Node` field
      rw [← Hwnl]
      iexact Hni
    isplitr
    · ipureintro; exact Hwms.symm
    isplitr
    · rw [Hwwal, Hstss.2, Hwnode]; iexact Hdur
    -- the components are the same (`transport` is no component)
    iunfold rnParts at Hparts
    iunfold rnParts
    iNamed Hparts
    simp only [named]
    iframe #
    -- (2026-10-31) `stopped`'s bag at the storage's WAL; (R2b-3b) `done`'s escrow at it
    isplitr
    · iExactEq Hstci
      first | rfl | simp [Hrvcfg]
    iExactEq Hdnci
    first | rfl | simp [Hrvcfg]
  imodintro
  iframe Hrn Hdone Htrf Hprop
  have hn : rnNodeIface γw =
      ({ rv with raftNodeConfig' := { rv.raftNodeConfig' with transport' := tr } } : raftNode).raftNodeConfig'.Node' := by
    simp only [Hrvcfg, rnNodeIface, Hwnl]
  rw [hn]
  iexact Hnodef


/-- (restart S3 item 8, D5, 2026-11-11) **The composition's statement at a restart** (beside
`NodeStartSpec`, which stays the first start's: D5, so that `NewServer.lean` is untouched until S6):
`bootstrappedRaft.newRaftNode` over the node API's `RestartNode` (the boot `.restart σ cs S |A₀| m A₀`),
for the WAL's records `σ`, the backend's conf state `cs` and committed log `A₀` (its consistent index
`|A₀|` between the records' base and commit), the node's durable state `S` held by the records: the
storage `bootstrappedWAL.MemoryStorage` rebuilt (`memStorRestarted`; `srvMem_restartStorage`, its
snapshot valid by `walSnapCS_valid`), the WAL's durability at the view `⟨S, σ.hs, none, P⟩` with
`P = A₀.take σ.b` (`rnDur_alloc_view`, W4's records); yields the wrapper with the tokens at `P`
(Q34 (a); `rnToks_of_restart`), the names' restart data (`a0 = A₀`, `t0` the restored term, `commit0`,
`snap0` the restored commit and base), and the installer, which takes the restart-only premise
`rnSnapTermAbove` (row 4, R2d'a's) for `isRaftNode`'s `rnRestartOk`. -/
abbrev NodeStartSpecR : Prop :=
  ∀ (γr : SrvRaft) (E : RNEnv GF) (b ss wal cl : Loc) (dq : DFrac)
    (bv : bootstrappedRaft) (cv : Config) (lok : GoInterfaceOk) (γs : MemStorNames)
    (ν : WalNames) (pv : List Peer) (ctxs : List (List w8)) (issued : GName)
    (σ : StorContents) (cs : ConfStateM) (S : RaftState) (m : Membership) (A₀ : List EntryModel),
    letI : MemStorReg GF := ⟨γr.reg⟩
    letI := srvStor (GF := GF) γr
    {{ "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        -- the pure premises: the restart's configuration (`rnRestartCfg`), a positive heartbeat, the
        -- WAL read, the receipts' bound (`rnLogFits`), the voters within raft's bounds (the view's
        -- `srvCfgOk`), the backend's consistent index between the records' base and commit, the
        -- bootstrap log within the commit, the records holding `S`, the snapshot record's term the
        -- base's, the backend's conf state the voters' (D4, S6's) within raft's bounds
        "%Hraft" ∷ ⌜rnRestartCfg bv cv lok pv ∧ 0 < sint.Z bv.heartbeat' ∧ storage.walReady wal ∧
          receiptBound GF + γr.boot.length ≤ 2 ^ 61 ∧ W64 0 ∉ γr.cfg ∧ GMap.size γr.cfg < 2 ^ 62 ∧
          σ.b ≤ A₀.length ∧ A₀.length ≤ σ.commit ∧ γr.cl.bootLen ≤ σ.commit ∧ StorageHolds S σ ∧
          (∀ m' : SnapshotMetadataM, σ.snap = some (SnapshotM.mk [] m') → m'.Term' = σ.base.term') ∧
          confStateIs cs (Membership.simple γr.cfg) ∧
          (cs.Voters'.length + cs.Learners'.length + cs.VotersOutgoing'.length +
            cs.LearnersNext'.length : Int) ≤ 2 ^ 62⌝ ∗
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
        "Hvac" ∷ nodeVacant γr.cl cv.ID' ∗ "HrS" ∷ raftState γr.cl cv.ID' S ∗
        "#Hconf" ∷ confAt γr.cl A₀.length m ∗
        "#Hlinv" ∷ srvRaftLogInv ⟨γr, [], W64 0⟩ ∗ "#HA0" ∷ srvRLogLb ⟨γr, [], W64 0⟩ A₀ ∗
        "#Hcert" ∷ walSnapCert γr.cl σ ∗
        -- the names-only contracts
        "#Hzap" ∷ rnLoggerZapOk ∗ "#Htdok" ∷ rnTimeoutDetectorOk ∗
        "#Hrs" ∷ rnRaftStatusOk ∗ "#Hns" ∷ rnNewStorageOk ∗
        "#Hcl" ∷ rnClusterOk cl ∗
        -- the WAL's durability at the restart's view (`rnDur_alloc_view`)
        "#Hdur" ∷ rnDurInv γr.cl ν wal ∗
        "Hwview" ∷ ghostVar ν.view (1 : Qp).half
          (⟨S, σ.hs, none, srvLE ⟨γr, [], W64 0⟩ (A₀.take σ.b)⟩ : WalView) ∗
        "Hwok" ∷ token ν.ok }}
      (App (App (App (Val (b @!! go.GoType.PointerType bootstrappedRaft.ty @!! go!"newRaftNode"))
        (Val #ss)) (Val #wal)) (Val #cl))
    {{ (r : Loc), RET #r;
        ∃ (γw : RNNames) (rv : raftNode),
          ⌜γw.node = γr ∧ γw.id = cv.ID' ∧ γw.pre = [] ∧ γw.ms = bv.storage' ∧ γw.γs = γs ∧
            γw.wal = ν ∧ γw.a0 = A₀ ∧ γw.t0 = σ.hs.Term' ∧ γw.commit0 = σ.commit ∧
            γw.snap0 = σ.b ∧
            rv.lg' = bv.lg' ∧ rv.raftNodeConfig'.raftStorage' = bv.storage' ∧
            rv.raftNodeConfig'.heartbeat' = bv.heartbeat' ∧
            rv.raftNodeConfig'.transport' = GoInterface.nil ∧
            rv.raftNodeConfig'.Node' = rnNodeIface γw ∧
            rnStorageOf rv.raftNodeConfig'.storage' ss ∧
            storage.walOf rv.raftNodeConfig'.storage' = wal⌝ ∗
          r ↦ rv ∗ rv.tickMu' ↦ (zero_val sync.RWMutex) ∗
          rnStepIfc γw (rnNodeIface γw) ∗
          -- the tokens at `P` (Q34 (a))
          rnLoopTok γw (A₀.take σ.b) ∗ rnApplyTok γw (A₀.take σ.b) ∗
          (letI := srvStor (GF := GF) γw.node; nodeRunning γw.nl γw.node.cl srvClusterN (1 : Qp).half) ∗
          -- the installer, with the restart-only premise `rnSnapTermAbove`
          (∀ (a s : Loc) (tr : GoInterface), rnEnvOk E γw -∗ srvCommittedInv s E.γr -∗
            srvRdCtxInv E.γr.raft issued -∗ rnSnapTermAbove γw -∗
            rnFixed a rv -∗ rnTransportAddr a ↦□ tr -∗ rnLatestTickTsAddr a ↦ rv.latestTickTs' -∗
            isRNTransport E tr -∗ rv.tickMu' ↦ (zero_val sync.RWMutex) ={⊤}=∗
            isRaftNode E γw a ∗ rnDoneTok γw a ∗
            rnNodeAddr a ↦□ rnNodeIface γw ∗ raftPropose E.γr.raft (rnNodeIface γw) ∗
            rnTransportAddr a ↦□ tr) ∗
          b ↦{dq} bv ∗ bv.peers' ↦*{dq} pv ∗
          memStorInv bv.storage' γs γr.cl γw.key ∗ memStorMeta bv.storage' γs σ.hs ∗
          rnStopClaim γw }}

set_option maxHeartbeats 0 in
/-- (restart S3 item 8, 2026-11-11) **The composition at a restart** (see `NodeStartSpecR`): from
`bootstrappedRaft.newRaftNode.spec` at `.restart` (through it the node API's `RestartNode`) and the
node API's node specs, as `raftNode_of_StartNode`. -/
theorem raftNode_of_RestartNode
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
    NodeStartSpecR (GF := GF) := by
  intro γr E b ss wal cl dq bv cv lok γs ν pv ctxs issued σ cs S m A₀
  letI : MemStorReg GF := ⟨γr.reg⟩
  letI := srvStor (GF := GF) γr
  iintro %Φ Hpre HΦ
  iNamed Hpre
  obtain ⟨Hcfg, Hhb, Hwal, Hfit, H0, Hsz, Hba, Hac, Hboot, Hhold, Hterm, Hcs, Hcsb⟩ := Hraft
  have Hbc : σ.b ≤ σ.commit := Nat.le_trans Hba Hac
  -- the configuration at the backend's index the voters' (Q39)
  imod srv_confAt_eq_simple ⟨γr, [], W64 0⟩ (srvLE ⟨γr, [], W64 0⟩ A₀) A₀.length m
      (by simp [srvLE]) ⊤ (by simp) (by simp) $$ [$Hlinv $Hconf] with %Hm
  · iunfold srvRLogLb at HA0; icases HA0 with ⟨#H, -⟩; iexact H
  subst Hm
  -- the restarted storage's snapshot valid (D4) and its persistent part, for the frozen terms
  imod walSnapCS_valid ⟨γr, [], W64 0⟩ σ cs ⊤ (by simp) (by simp) Hterm Hcs Hcsb $$ [$Hlinv $Hcert]
    with Hval
  ihave %Hlt := restart_lastTerm γr A₀ σ Hba Hterm $$ [$HA0 $Hcert]
  iunfold memStorRestarted at Hrest
  icases Hrest with ⟨Hfresh, Hmeta, #Hcp, #He0, #Hslb, Hents, Hend⟩
  ihave #Hfz : srvFrozenTerms γs 1 (A₀.take σ.b) $$ []
  · have hlen : (A₀.take σ.b).length = σ.b := by simp; omega
    iapply srvFrozenTerms_restart γs (A₀.take σ.b) (memDummy (walSnapCS σ cs)) Hlt
    rw [hlen]
    iframe Hcp He0
  ihave Hbs := srvMem_restartStorage wp_InitialState wp_Snapshot wp_LastIndex wp_FirstIndex wp_Term
      wp_Entries γr bv.storage' γs σ cs 0
      (fun K => iprop(memStorInv bv.storage' γs γr.cl K ∗ memStorMeta bv.storage' γs σ.hs)) Hbc Hγsz
      $$ [Hfresh Hmeta Hents Hend Hval]
  · iframe Hreg Hlock Hval
    isplitl [Hfresh Hmeta Hents Hend]
    · iunfold memStorRestarted
      iframe Hfresh Hmeta Hcp He0 Hslb Hents Hend
    iintro %K Hi Hm
    iframe Hi Hm
  wp_apply (wp_bnr E γr b ss wal cl dq bv cv lok γs [] ν pv [] ctxs
    (fun K => iprop(memStorInv bv.storage' γs γr.cl K ∗ memStorMeta bv.storage' γs σ.hs))
    (.restart σ cs S A₀.length (Membership.simple γr.cfg) A₀))
    $$ [Hb Hc Hbs Hpeers HrS Hvac]
    as %r Hpost
  · iframe #; iframe Hb Hc Hpeers
    isplitr
    · ipureintro; exact ⟨Hhb, Hwal⟩
    simp only [rnBootPre]
    isplitr
    · ipureintro; exact ⟨Hcfg, Hba, Hac, Hboot, Hcs, Hhold⟩
    isplitl [Hbs]
    · iExactEq Hbs; rfl
    isplitr
    · iExactEq Hclu; rfl
    isplitr
    · iExactEq Hrf; rfl
    isplitl [Hvac]
    · iExactEq Hvac; rfl
    isplitl [HrS]
    · iExactEq HrS; rfl
    iExactEq Hconf; rfl
  icases Hpost with ⟨%n, %γw, %f, %st, %Hnames, #Hnode, Hrun, Hbpost, #Hidri, #Hsti,
    %Hstss, Hbuilt, Hb, Hpeers, ⟨#Hminv, Hmeta⟩⟩
  simp only [rnBootPost, RNBoot.P]
  icases Hbpost with ⟨%l, #Hl, %Hll, Hdrv, HrS, Hncfg⟩
  simp only [RNBoot.a0, RNBoot.t0, RNBoot.commit0, RNBoot.snap0] at Hnames
  obtain ⟨Hwnode, Hwid, Hwnl, Hwpre, Hwms, Hwγs, Hwwal, Hwa0, Hwt0, Hwc0, Hws0⟩ := Hnames
  -- the driver's delivered log is the backend's up to the base (committed logs agree)
  ihave %Hleq : ⌜l = srvLE ⟨γr, [], W64 0⟩ (A₀.take σ.b)⌝ $$ []
  · iunfold srvRLogLb at HA0
    icases HA0 with ⟨#HAc, -⟩
    icases isCommittedLogLb_agree γr.cl l (srvLE ⟨γr, [], W64 0⟩ A₀) $$ [Hl HAc] with %Hag
    · iframe Hl HAc
    ipureintro
    have hSL : (srvLE ⟨γr, [], W64 0⟩ A₀).length = A₀.length := by simp [srvLE]
    have e : srvLE ⟨γr, [], W64 0⟩ (A₀.take σ.b) = (srvLE ⟨γr, [], W64 0⟩ A₀).take l.length := by
      rw [Hll]; simp [srvLE, List.map_take]
    rw [e]
    rcases Hag with h | h
    · exact List.prefix_iff_eq_take.1 h
    · have := h.length_le
      rw [hSL] at this
      have heq : srvLE ⟨γr, [], W64 0⟩ A₀ = l := List.IsPrefix.eq_of_length h (by omega)
      rw [heq, List.take_length]
  subst Hleq
  iunfold rnBuilt at Hbuilt
  iNamed Hbuilt
  obtain ⟨Hrvlg, Hrvcfg⟩ := Hrv
  have Hsrv : γw.srv = ⟨γr, [], W64 0⟩ := by
    unfold RNNames.srv; rw [Hwnode, Hwpre]
  -- the bridges
  ihave #Hfits' : rnLogFits γw $$ []
  · iunfold rnLogFits; ipureintro; rw [Hwnode]; exact Hfit
  ihave #Hreg' : rnMemStorReg γw $$ []
  · unfold rnMemStorReg RNNames.reg; rw [Hwms, Hwγs, Hwnode]; iexact Hreg
  ihave #Hpraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hmsi : isRNMemStor γw γw.ms $$ []
  · iapply isRNMemStor_of_memstorage γw
    iframe Hpraft Hreg'
    rw [Hwms, Hwγs]; iexact Hlock
  ihave #Hisnode : rnIsNode γw $$ []
  · unfold rnIsNode; rw [Hwnode, Hwid, Hwnl]; iexact Hnode
  icases ((nodeRunning_fractional n γr.cl srvClusterN).fractional (1 : Qp).half
      (1 : Qp).half).1 $$ [Hrun] with ⟨Hrun1, Hrun2⟩
  · rw [Qp.half_add_half]; iexact Hrun
  -- the tokens at `P`
  ihave %HAidx : ⌜srvIdxOkW (W64 0) A₀⌝ $$ []
  · iunfold srvRLogLb at HA0; icases HA0 with ⟨-, %h⟩; ipureintro; exact h
  have hidx : srvIdxOkW (W64 0) (A₀.take σ.b) :=
    srvIdxOkW_prefix _ _ _ HAidx (List.take_prefix _ _)
  have hghost : rnGhost γw (A₀.take σ.b) = A₀ := by
    unfold rnGhost
    rw [Hwpre, Hwa0, List.nil_append, List.length_take, Nat.min_eq_left Hba, List.take_append_drop]
  have hcfgv : srvCfgOk γw.node.cfg (rnGhost γw (A₀.take σ.b))
      ⟨A₀.length, Membership.simple γr.cfg⟩ := by
    rw [hghost, Hwnode]
    exact ⟨Nat.le_refl _, fun _ _ h1 h2 _ => absurd h2 (by simp; omega),
      ⟨γr.cfg, rfl, fun _ h => h, fun _ h1 h2 => absurd h1 h2, H0, Hsz⟩⟩
  ihave ⟨Hloop, Happly⟩ := rnToks_of_restart γw (A₀.take σ.b) σ.hs S
      ⟨A₀.length, Membership.simple γr.cfg⟩ Hwpre hidx (by rw [Hwc0]; exact Nat.le_refl _) hcfgv
    $$ [Hdrv HrS Hncfg Hrun1 Hprod Hcons Hcum Hcum0 Hwview Hwok]
  · rw [Hsrv, Hwnode, Hwnl, Hwms, Hwid, Hwwal, Hwγs]
    iframe Hdrv HrS Hncfg Hrun1 Hprod Hcons Hcum Hcum0 Hwview Hwok Hfz
  iapply HΦ
  iexists γw, rv
  isplitr
  · ipureintro
    refine ⟨Hwnode, Hwid, Hwpre, Hwms, Hwγs, Hwwal, Hwa0, Hwt0, Hwc0, Hws0, Hrvlg, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [Hrvcfg]
    all_goals first | exact Hstss | simp only [rnNodeIface, Hwnl]
  iframe Hr Hmu Hloop Happly Hb Hpeers Hminv Hmeta Hsc
  isplitr
  · iapply rnStepIfc_of_isNode γw (wp_Step γw.node) (wp_ReportUnreachable γw.node)
      (wp_ReportSnapshot γw.node)
    iframe Hpkg Hisnode
  isplitl [Hrun2]
  · rw [Hwnode, Hwnl]; iexact Hrun2
  -- the installer
  iintro %a %s %tr #Henv' #Hcommi #Hrdi #Hsta #Hfix Htrf Hlts #Htri Hmu'
  ihave #Hrsb : rnReadStateBridge E γw $$ []
  · iapply rnReadStateBridge_of_raft E γw $$ Henv'
  ihave #Hni : isRaftNodeIfc E γw (rnNodeIface γw) $$ []
  · iapply isRaftNodeIfc_of_isNode E γw s issued (wp_Ready γw.node) (wp_Advance γw.node)
      (wp_Tick γw.node) (wp_Stop γw.node) (wp_ReadIndex γw.node)
      (wp_ApplyConfChange γw.node)
    iframe Hpkg Henv' Hisnode Hcommi Hreg' Hrdi
  ihave #Hlinv' : srvRaftLogInv E.γr.raft $$ []
  · iunfold rnEnvOk at Henv'
    icases Henv' with ⟨-, -, -, #H, -⟩
    iexact H
  ihave #Hprop : raftPropose E.γr.raft (rnNodeIface γw) $$ []
  · iapply raftPropose_of_isNode E γw (wp_Propose γw.node)
    iframe Hpkg Henv' Hisnode Hlinv'
  ihave #Hfix' : rnFixed a
      { rv with raftNodeConfig' := { rv.raftNodeConfig' with transport' := tr } } $$ []
  · simp only [rnFixed]
    iexact Hfix
  imod (isRaftNode_of_rnParts E γw a
    { rv with raftNodeConfig' := { rv.raftNodeConfig' with transport' := tr } })
    $$ [Htrf Hlts Hmu' Hdtok] with ⟨#Hrn, Hdone, #Hnodef, #Htrf⟩
  · iframe Hpkg Henv' Hfits' Hrsb Hreg' Hfix' Htrf Hlts Hmu' Hdtok
    isplitr
    · -- the restart data: the restart disjunct
      iunfold rnRestartOk; iright
      iframe Hsta
      isplitr
      · ipureintro; rw [Hwpre, Hws0, Hwa0, Hwc0]; exact ⟨rfl, Hba, Hac⟩
      rw [Hsrv, Hwa0]; iexact HA0
    simp only [Hrvcfg]
    iframe Hidri Hsti Htri Hmsi
    isplitr
    · rw [← Hwnl]
      iexact Hni
    isplitr
    · ipureintro; exact Hwms.symm
    isplitr
    · rw [Hwwal, Hstss.2, Hwnode]; iexact Hdur
    iunfold rnParts at Hparts
    iunfold rnParts
    iNamed Hparts
    simp only [named]
    iframe #
    isplitr
    · iExactEq Hstci
      first | rfl | simp [Hrvcfg]
    iExactEq Hdnci
    first | rfl | simp [Hrvcfg]
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
