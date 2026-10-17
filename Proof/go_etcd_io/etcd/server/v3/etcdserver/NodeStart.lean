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
* trust-boundary premises: `rnLogFits` (D10: raft's `Ready`s fit the `MemoryStorage`), `rnStopOk`
  (`Stop` returns), `rnTickerOk`/`isRNTicker` (Perennial models no ticker), the `InitialState`
  closure in `StartNode.spec`'s `□` shape (a `MemoryStorage`'s `InitialState` consumes
  `memStorMeta`, which is not persistent: `MemoryStorage.InitialState.spec` cannot be the `□`
  closure; `StartNode` calls it once -- B's spec could drop the `□`), `bootMarshal` (protobuf's
  determinism at the peers' conf changes), the names-only contracts (`rnLoggerZapOk`,
  `rnSetLoggerOk`, `rnTimeoutDetectorOk`, `rnRaftStatusOk`, `rnNewStorageOk`, `rnClusterOk`,
  `isRNTransport`), and -- not in this theorem, a premise of the construction as before --
  `rnSnapOnce ms 0 0` (`isServerBuilt`'s `Hsnap`: the server holds no `ownMemoryStorage` once
  raft owns the storage, and raft's `MemoryStorage.Snapshot.spec` does not state the clone's
  pointers non-nil, which `run` needs).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedRaft__newRaftNode
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NodeBridge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section compose
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

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
      a ↦ rv ∗ rv.tickMu' ↦ (zero_val sync.RWMutex) ∗
      ownBroadcastChan rv.done' γ.done iprop(True) .Pending ⊢
      |={⊤}=> isRaftNode E γ a ∗ rnDoneTok γ a ∗
        rnNodeAddr a ↦□ rv.raftNodeConfig'.Node' ∗
        rnTransportAddr a ↦□ rv.raftNodeConfig'.transport' := by
  iintro ⟨#Hpkg, #Henv, #Hfits, #Hrsb, #Hreg, #Hni, #Hidri, %Hmsγ, #Hmsi, #Hsti, #Htri, #Hparts,
    Ha, Hmu, Hdtok⟩
  iunfold rnParts at Hparts
  iNamed Hparts
  iStructNamedSuffix Ha "R"
  iStructNamedSuffix raftNodeConfigR "C"
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  imod sync.init_RWMutex (rnTickInv a) rv.tickMu' $$ [latestTickTsR] Hmu with Hslots
  · inext; iunfold rnTickInv; iexists rv.latestTickTs'; iexact latestTickTsR
  icases read_guard_of_slots _ _ $$ Hslots with ⟨-, #Hmug⟩
  ipersist lgR
  ipersist tickMuR
  ipersist lgC
  ipersist isIDRemovedC
  ipersist NodeC
  ipersist raftStorageC
  ipersist storageC
  ipersist heartbeatC
  ipersist transportC
  ipersist msgSnapCR
  ipersist applycR
  ipersist readStateCR
  ipersist tickerR
  ipersist tdR
  ipersist stoppedR
  ipersist doneR
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
[]`): from raft's driver at the empty delivered log (`nodeDriver … []`: `StartNode`'s, with
`γ.pre = []` so that `rnLogOf γ [] = []`), its view of the configuration, and `applyc`'s halves
with `cum` at `[[]]` (`newRaftNode`'s). -/
theorem rnToks_of_start (γ : RNNames) (ca : Nat) (cfg : CCState) (hpre : γ.pre = []) :
    (letI : MemStorReg GF := ⟨γ.reg⟩;
      iprop(nodeDriver γ.node γ.id γ.nl [] ∗ nodeCfg γ.node ca cfg)) ∗
      spscProducer γ.ap ([] : List toApply) ∗ spscConsumer γ.ap ([] : List toApply) ∗
      monoListAuthOwn γ.cum 1 [([] : List EntryModel)] ∗
      monoListIdxOwn γ.cum 0 ([] : List EntryModel) ⊢
      rnLoopTok γ [] ∗ rnApplyTok γ [] := by
  iintro ⟨⟨Hdrv, Hcfg⟩, Hprod, Hcons, Hcum, Hcum0⟩
  isplitl [Hdrv Hcfg Hprod Hcum]
  · iunfold rnLoopTok
    iexists [], [[]]
    isplitl [Hdrv Hcfg]
    · iunfold rnDrv
      have h : rnLogOf γ [] = [] := by unfold rnLogOf; rw [hpre]; rfl
      rw [h]
      iframe Hdrv
      iexists ca, cfg
      iexact Hcfg
    iframe Hprod Hcum
    ipureintro; exact ⟨rfl, rfl⟩
  · iunfold rnApplyTok
    iexists []
    iframe Hcons
    iexact Hcum0

/-- **`srvRaftLogInv` at the start** (`pre = []`, `ai0 = 0`): raft's commit invariant, the empty
log committed (a prefix of the committed boot log), and the policy. -/
theorem srvRaftLogInv_of_boot (γs : ServerRaftNames) (bootLog : List EntryM)
    (hpre : γs.pre = []) (hai : γs.ai0 = W64 0) (hpol : srvCCPolicy γs) :
    raftCommitInv γs.raft ∗ isCommitted γs.raft bootLog ⊢ srvRaftLogInv γs := by
  iintro ⟨#Hinv, #Hc⟩
  iunfold srvRaftLogInv
  iframe Hinv
  isplitl
  · iunfold srvRLogLb
    have h : srvLogOf γs [] = [] := by unfold srvLogOf; rw [hpre]; rfl
    rw [h]
    iapply isCommitted_mono γs.raft [] bootLog (List.nil_prefix) $$ Hc
  ipureintro; refine ⟨?_, hpol⟩; rw [hai, hpre]; simp

/-- **The composition's statement** (see the file header), a proposition over the registry's name
`reg` (the `MemoryStorage` instance's), so that `Results.lean` instantiates it with the linked
results: for the cluster's ghost names `γ`, the budget `bud`, the storage's names `γs`, the receiver
`b` and the config `cv` with `StartNode.spec`'s premises on it (**`CheckQuorum` and `PreVote` off:
not etcd's own configuration**), the peers and the bootstrap log, and the server's names
(`E.γr.raft = ⟨γ, [], 0⟩`, the policy `srvCCPolicy`): `bootstrappedRaft.newRaftNode` over raft's
`StartNode`, with what the allocation, the server and the trust boundary provide, yields the
wrapper's struct value, the tokens, `srvRaftLogInv`, and the installer of `isRaftNode` at the
address the server copies the struct to. -/
abbrev NodeStartSpec (reg : GName) : Prop :=
  ∀ (E : RNEnv GF) (γ : RaftNames) (bud : BudgetNames) (b ss wal cl : Loc) (dq : DFrac)
    (bv : bootstrappedRaft) (cv : Config) (lok : GoInterfaceOk) (γs : MemStorNames)
    (pv : List Peer) (ps : List w64) (ctxs : List (List w8)) (bootLog : List EntryM),
    -- `newRaftNode`'s premises
    bv.lg' ≠ null → bv.heartbeat' ≠ W64 0 →
    -- `NewRawNode`'s premises on `b.config` (**`CheckQuorum` and `PreVote` off**)
    ConfigValid cv → cv.Logger' = interface.ok lok →
    cv.Storage' = memStorIface bv.storage' →
    sint.Z cv.MaxInflightMsgs' < 2 ^ 62 → cv.CheckQuorum' = false →
    cv.DisableProposalForwarding' = false → cv.ReadOnlyOption' = W64 0 →
    cv.DisableConfChangeValidation' = false →
    (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
    cv.AsyncStorageWrites' = false → cv.PreVote' = false → cv.Applied' = W64 0 →
    -- the peers and the bootstrap log
    ps = pv.map Peer.ID' → ps ≠ [] → ps.Nodup → W64 0 ∉ ps →
    (ps.length : Int) ≤ 2 ^ 62 → cv.ID' ∈ ps → γ.reCfg = GMap.listToSet ps →
    γ.reBoot = bootLog → BootLogOk γ.reCCOk ps bootLog →
    -- the server's names: the raft names, the start log empty, the policy
    E.γr.raft.raft = γ → E.γr.raft.pre = [] → E.γr.raft.ai0 = W64 0 → srvCCPolicy E.γr.raft →
    letI : MemStorReg GF := ⟨reg⟩
    {{ "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        -- the receiver, the config and its logger
        "Hb" ∷ b ↦{dq} bv ∗ "Hc" ∷ bv.config' ↦ cv ∗ "#Hlok" ∷ isLogger lok ∗
        -- the fresh registered `MemoryStorage` (`NewMemoryStorage`, `memStorReg_register`,
        -- `memOwnStorage_empty`, `memStorage_isStorage`)
        "#Hreg" ∷ memStorReg bv.storage' γs ∗
        "#Hsi" ∷ isStorage (memStorIface bv.storage') ∗
        "Hsto" ∷ ownStorage (memStorIface bv.storage') memStorEmpty ∗
        -- trust boundary: `StartNode.spec`'s `InitialState` closure (see the file header)
        "#Hinit" ∷ □ (∀ (Φ : val → IProp GF) (ss' : entryID),
           ownStorage (memStorIface bv.storage') { memStorEmpty with ss := ss' } -∗
           (∀ (hp cs : Loc) (al : Bool),
            ownStorage (memStorIface bv.storage') { memStorEmpty with ss := ss' } -∗
            hsOpt hp (HardStateM.mk (W64 0) (W64 0) (W64 0)) -∗
            csPts cs DFrac.discard (ConfStateM.mk [] [] [] [] false) al -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
           WP (App (Val #(methods (go.GoType.PointerType MemoryStorage.ty) go!"InitialState" #bv.storage'))
             (Val #())) {{ Φ }}) ∗
        -- the peers, their contexts; trust boundary: `Marshal` at their conf changes
        "Hpeers" ∷ bv.peers' ↦*{dq} pv ∗ "#Hctx" ∷ peersCtx pv ctxs ∗
        "#Hmarshal" ∷ bootMarshal ps ctxs bootLog ∗
        -- the allocation's: this node's ghost state, the committed boot log, the commit
        -- invariant, the budget
        "Hghost" ∷ ownRaftGhost γ cv.ID' (bootPState bootLog) ∗ "#Hcomm" ∷ isCommitted γ bootLog ∗
        "#Hcinv" ∷ raftCommitInv γ ∗
        "#Hbud" ∷ inv budgetN (budgetInv bud) ∗ "#HtermLB" ∷ termLB bud (W64 1) ∗
        -- the names-only contracts
        "#Hzap" ∷ rnLoggerZapOk ∗ "#Hsetlg" ∷ rnSetLoggerOk ∗ "#Htdok" ∷ rnTimeoutDetectorOk ∗
        "#Htkok" ∷ rnTickerOk E ∗ "#Hrs" ∷ rnRaftStatusOk ∗ "#Hns" ∷ rnNewStorageOk ∗
        "#Hcl" ∷ rnClusterOk cl ∗
        -- trust boundary: raft's `Ready`s fit (D10), `Stop` returns
        "#Hfits" ∷ (∀ γw : RNNames,
          ⌜γw.node.raft = γ ∧ γw.node.bud = bud ∧ γw.node.stor = memStorIface bv.storage' ∧
            γw.node.mode = RNMode.static ∧ γw.reg = reg⌝ -∗ rnLogFits γw) ∗
        "#Hstop" ∷ (∀ n : Loc, rnStopOk n) }}
      (App (App (App (Val (b @!! go.GoType.PointerType bootstrappedRaft.ty @!! go!"newRaftNode"))
        (Val #ss)) (Val #wal)) (Val #cl))
    {{ (r : Loc), RET #r;
        ∃ (γw : RNNames) (rv : raftNode),
          ⌜γw.node.raft = γ ∧ γw.node.bud = bud ∧ γw.node.stor = memStorIface bv.storage' ∧
            γw.node.mode = RNMode.static ∧ γw.id = cv.ID' ∧ γw.pre = [] ∧ γw.ms = bv.storage' ∧
            γw.γs = γs ∧ γw.reg = reg ∧
            rv.lg' = bv.lg' ∧ rv.raftNodeConfig'.raftStorage' = bv.storage' ∧
            rv.raftNodeConfig'.heartbeat' = bv.heartbeat' ∧
            rv.raftNodeConfig'.transport' = GoInterface.nil⌝ ∗
          -- the struct value, to be copied; its fresh mutex
          r ↦ rv ∗ rv.tickMu' ↦ (zero_val sync.RWMutex) ∗
          -- `isServerBuilt`'s rows but `isRaftNode`
          rnLoopTok γw [] ∗ rnApplyTok γw [] ∗ srvRaftLogInv E.γr.raft ∗
          -- the installer: `isRaftNode` and `rnDoneTok` at the address `a` the struct is copied
          -- to, once its `transport` is set to `tr`, with the server's own: `rnEnvOk` for the
          -- wrapper's names and the committed index's invariant of the server `s` (allocated
          -- after the call: `NewServer` evaluates `newRaftNode` inside the server's literal)
          (∀ (a s : Loc) (tr : GoInterface), rnEnvOk E γw -∗ srvCommittedInv s E.γr -∗
            a ↦ { rv with raftNodeConfig' := { rv.raftNodeConfig' with transport' := tr } } -∗
            isRNTransport E tr -∗ rv.tickMu' ↦ (zero_val sync.RWMutex) ={⊤}=∗
            isRaftNode E γw a ∗ rnDoneTok γw a ∗
            -- the node's field, and its `Propose` (the request path's `raftPropose`); the
            -- transport's field (unit N4, 2026-10-17: `NewServer`'s `srvReqBuilt`)
            rnNodeAddr a ↦□ rnNodeIface γw ∗ raftPropose E.γr.raft (rnNodeIface γw) ∗
            rnTransportAddr a ↦□ tr) ∗
          b ↦{dq} bv ∗ bv.peers' ↦*{dq} pv }}

set_option maxHeartbeats 0 in
/-- **The composition** (see `NodeStartSpec` and the file header): from
`bootstrappedRaft.newRaftNode.spec` (through it `StartNode.spec` and `newRaftNode.spec`) and the
node's specs (for its contract, `isRaftNodeIfc_of_isNode`), under the `MemoryStorage` instance
`⟨reg⟩`. -/
theorem raftNode_of_StartNode (reg : GName)
    (wp_bnr : letI : MemStorReg GF := ⟨reg⟩;
      bootstrappedRaft.newRaftNode.spec (GF := GF) (hG := hG))
    (wp_Ready : letI : MemStorReg GF := ⟨reg⟩; node.Ready.spec (GF := GF) (hG := hG))
    (wp_Advance : letI : MemStorReg GF := ⟨reg⟩; node.Advance.spec (GF := GF) (hG := hG))
    (wp_Tick : letI : MemStorReg GF := ⟨reg⟩; node.Tick.spec (GF := GF) (hG := hG))
    (wp_ReadIndex : letI : MemStorReg GF := ⟨reg⟩; node.ReadIndex.spec (GF := GF) (hG := hG))
    (wp_Propose : letI : MemStorReg GF := ⟨reg⟩; node.Propose.spec (GF := GF) (hG := hG)) :
    NodeStartSpec (GF := GF) reg := by
  letI : MemStorReg GF := ⟨reg⟩
  intro E γ bud b ss wal cl dq bv cv lok γs pv ps ctxs bootLog Hlg Hhb Hvalid Hlok Hstor Hinfl
    Hcq Hdpf Hro Hdccv Hsizes Hasync Hpv Happlied Hps Hpsne Hnodup H0 Hpslen Hid Hcfg Hboot
    HbootOk HEγ HEpre HEai Hpol
  iintro %Φ Hpre HΦ
  iNamed Hpre
  wp_apply (wp_bnr E γ bud b ss wal cl dq bv cv lok γs reg [] pv ps ctxs bootLog Hlg Hhb Hvalid Hlok
    Hstor Hinfl Hcq Hdpf Hro Hdccv Hsizes Hasync Hpv Happlied Hps Hpsne Hnodup H0 Hpslen Hid Hcfg
    Hboot HbootOk) $$ [Hb Hc Hsto Hpeers Hghost]
    as %r ⟨%γn, %n, %γw, %f, %st, %Hnames, #Hnode, Hdrv, Hncfg, #Hidri, #Hsti, Hbuilt, Hb, Hpeers⟩
  · iframe #; iframe Hb Hc Hsto Hpeers Hghost
  obtain ⟨Hγraft, Hγbud, Hγstor, Hγmode, Hwnode, Hwid, Hwnl, Hwpre, Hwms, Hwγs, Hwreg⟩ := Hnames
  subst Hwreg
  iunfold rnBuilt at Hbuilt
  iNamed Hbuilt
  obtain ⟨Hrvlg, Hrvcfg⟩ := Hrv
  -- the bridges
  ihave #Hfits' : rnLogFits γw $$ []
  · iapply Hfits
    ipureintro
    exact ⟨by rw [Hwnode]; exact Hγraft, by rw [Hwnode]; exact Hγbud,
      by rw [Hwnode]; exact Hγstor, by rw [Hwnode]; exact Hγmode, rfl⟩
  ihave #Hlinv : srvRaftLogInv E.γr.raft $$ []
  · iapply srvRaftLogInv_of_boot E.γr.raft bootLog HEpre HEai Hpol
    rw [HEγ]
    iframe Hcinv Hcomm
  ihave #Hreg' : memStorReg γw.ms γw.γs $$ []
  · rw [Hwms, Hwγs]; iexact Hreg
  ihave #Hpraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hmsi : isRNMemStor γw γw.ms $$ []
  · iapply isRNMemStor_of_memstorage γw
    iframe Hpraft
    iexact Hreg'
  ihave #Hisnode : rnIsNode γw $$ []
  · unfold rnIsNode; rw [Hwnode, Hwid, Hwnl]; iexact Hnode
  -- the tokens
  ihave ⟨Hloop, Happly⟩ := rnToks_of_start γw 0 (cfgState (GMap.listToSet ps) ∅) Hwpre
    $$ [Hdrv Hncfg Hprod Hcons Hcum Hcum0]
  · rw [Hwnode, Hwid, Hwnl]
    iframe Hdrv Hncfg Hprod Hcons Hcum Hcum0
  iapply HΦ
  iexists γw, rv
  isplitr
  · ipureintro
    refine ⟨by rw [Hwnode]; exact Hγraft, by rw [Hwnode]; exact Hγbud,
      by rw [Hwnode]; exact Hγstor, by rw [Hwnode]; exact Hγmode, Hwid, Hwpre, Hwms, Hwγs, rfl,
      Hrvlg, ?_, ?_, ?_⟩ <;> rw [Hrvcfg]
  iframe Hr Hmu Hloop Happly Hlinv Hb Hpeers
  -- the installer
  iintro %a %s %tr #Henv' #Hcommi Ha #Htri Hmu'
  ihave #Hrsb : rnReadStateBridge E γw $$ []
  · iapply rnReadStateBridge_of_raft E γw $$ Henv' Hlinv
  ihave #Hni : isRaftNodeIfc E γw (rnNodeIface γw) $$ []
  · iapply isRaftNodeIfc_of_isNode E γw s wp_Ready wp_Advance wp_Tick wp_ReadIndex
    iframe Hpkg Henv' Hisnode Hlinv Hcommi
    iapply Hstop
  ihave #Hprop : raftPropose E.γr.raft (rnNodeIface γw) $$ []
  · iapply raftPropose_of_isNode E γw wp_Propose
    iframe Hpkg Henv' Hisnode Hlinv
  imod (isRaftNode_of_rnParts E γw a
    { rv with raftNodeConfig' := { rv.raftNodeConfig' with transport' := tr } })
    $$ [Ha Hmu' Hdtok] with ⟨#Hrn, Hdone, #Hnodef, #Htrf⟩
  · iframe Hpkg Henv' Hfits' Hrsb Hreg' Ha Hmu' Hdtok
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
