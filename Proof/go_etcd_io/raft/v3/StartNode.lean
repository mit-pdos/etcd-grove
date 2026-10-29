/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.StartNode
public import Spec.go_etcd_io.raft.v3.setupNode
public import Spec.go_etcd_io.raft.v3.node__run
public import Proof.go_etcd_io.raft.v3.InvNodeRun
public import Proof.go_etcd_io.raft.v3.InvAdvance
import all Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Proof.go_etcd_io.raft.v3.ApiVocab
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiDyn

@[expose] public section

noncomputable section


namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The raw triple (internal: private to this file)

What the proof over raft's internals shows, from which the wrapper (below) derives the spec. Its documentation, as when it was the spec (until 2026-10-28):
-/

/-! Lean-first (no Rocq counterpart).

## `StartNode(c, peers)` (node.go:271): the start of a new cluster

`setupNode(c, peers)` -- `NewRawNode(c)` on the empty storage of a new cluster (whose conf state
is **empty**: `NewRawNode.spec_empty`), then `rn.Bootstrap(peers)` (`RawNode.Bootstrap.spec`):
`becomeFollower(1, None)`, one `EntryConfChange` per peer at term `1` and indices `1..n`
appended to the log and committed (`raftLog.committed = n`), each applied to the tracker
(`applyConfChange`), nothing applied to the application -- in a `node` whose goroutine `run` it
starts, for the cluster's term budget `bud`. It returns the node (`isNodeChan`, persistent: what
`Propose`, `Step`, `Tick` and `Ready` take) and the driver's token (`nodeDriverChan`), at the empty
delivered log, and the driver's view of the configuration (`nodeCfg`, at index `0` and the
peers' configuration), as `RestartNode.spec` does (2026-10-16, stage R8b, D12).

**Why the driver starts at `[]`.** `Bootstrap` leaves `applied = 0`: the application sees the
conf changes through the first `Ready`, whose `CommittedEntries` are the boot entries beside
`Entries 1..n` and the hard state `{Term: 1, Commit: n}` (`prevHardSt = emptyState`). So the
delivered log is empty although the committed log is `bootLog` (`isCommitted γ bootLog`, the
allocation's): the driver's `Advance` delivers it.

**The ghost state.** The cluster's ghost state is allocated before the call, in the mode `md`
(statically `ownRaftGhost_alloc_boot`, `Protocol/Facts.lean`: every member at `bootPState
bootLog`, the committed log `bootLog` from the start, `RaftNames.reBoot = bootLog`, `γ.reCfg` the
peers; dynamically, since 2026-10-25, T-M M2a, `raft_dyn_alloc_boot`, `Protocol/ResultsDyn.lean`:
every member at `rboot c0 bootLog`, `c0` the peers' configuration, at the configuration index `0`,
so that the application's re-application of the boot entries through the first `Ready` is the
dynamic mode's ordinary `ApplyConfChange`). This node takes its `bootInit γ md cv.ID' V bootLog`
and `isCommitted γ bootLog`, and the log's description `BootLogOk ps bootLog` (entry `k`: type
`1`, term `1`, index `k + 1`, bytes decoding to `AddNode ps[k]`; until 2026-10-27 also admitted by
the cluster's conf-change policy, now each a tracked proposal the allocation registered).

**The bytes** (`bootMarshal`, `InvBoot.lean`): `proto.Marshal` of the `k`-th peer's conf change
returns `bootLog[k]`'s bytes -- protobuf's determinism at these inputs, a trust-boundary fact
taken as a premise in the style of `RestartNode.spec`'s `InitialState` closure, discharged where
the node is composed.

**The peers**: a `[]Peer` slice at `dq` holding `pv`, their ids `ps` (distinct, non-zero, at most
`2^62`, this node among them, the ghost configuration) and their `Context` bytes `ctxs`
(read-only, `peersCtx`). The `Config` premises are `NewRawNode`'s (static mode only: no
`StepDownOnRemoval` requirement). **The term budget** is at least at term `1`, the bootstrap
term (`budget_alloc_boot`, `InvNode.lean`: a budget allocated for a new cluster; `run` starts
with `termLB bud term`). -/

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
private abbrev StartNode.specRaw : Prop :=
  ∀ (γ : RaftNames) (md : RNMode) (bud : BudgetNames) (c : Loc) (cv : Config)
    (lok si : GoInterfaceOk)
    (σ : StorState)
    (hs : HardStateM) (csm : ConfStateM) (R : IProp GF)
    (peers : GoSlice) (dq : DFrac) (pv : List Peer) (ps : List w64) (ctxs : List (List w8))
    (bootLog : List EntryM) (sn : Bool),
  -- `NewRawNode`'s premises
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  cv.Applied' = W64 0 →
  -- an empty storage: no entries, no `HardState`, no snapshot
  σ.prev = entryID.mk (W64 0) (W64 0) →
  σ.ents = [] →
  (uint.Z σ.ss.index' = 0 ∨ σ.ss = σ.prev) →
  σ.pend = [] →
  HsEmpty hs →
  -- the conf state empty: a new cluster's
  csm.Voters' = [] →
  csm.VotersOutgoing' = [] →
  csm.Learners' = [] →
  csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  -- the peers: their ids `ps`, distinct and non-zero, this node among them, the cluster
  ps = pv.map Peer.ID' →
  ps ≠ [] → ps.Nodup → W64 0 ∉ ps →
  (ps.length : Int) ≤ 2 ^ 62 →
  cv.ID' ∈ ps →
  γ.reCfg = GMap.listToSet ps →
  -- the bootstrap log, the ghost state's
  γ.reBoot = bootLog →
  BootLogOk ps bootLog →
  -- (D19i part 1) the floor not raised yet: the storage's view, fresh to raft
  σ.fl = W64 0 →
  -- (2026-10-29, stage U8) and the hold (`HdOk`; a fresh storage, `memOwnStorage_empty`)
  σ.hd = W64 0 →
  -- (D22 S-d4, 2026-10-21) the node takes a `MsgSnap` from the network (`NodeNames.snapIn`) only
  -- outside the no-snapshot mode (2026-10-25 to 2026-10-28, stage U3d: also in the static mode)
  (sn = true → γ.reNoSnap = false) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isStorage (interface.ok si) ∗ ownStorage (interface.ok si) σ ∗
      -- `NewRawNode`'s `InitialState` premise (D7's shape; the conf state's record `csm` empty)
      (∀ (Φ : val → IProp GF) (ss' : entryID), ownStorage (interface.ok si) { σ with ss := ss' } -∗
           (∀ (hp cs : Loc) (al : Bool), ownStorage (interface.ok si) { σ with ss := ss' } -∗
            R -∗ hsOpt hp hs -∗ csPts cs DFrac.discard csm al -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
           WP (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #())) {{ Φ }}) ∗
      -- the peers, their contexts, and `Marshal` at their conf changes (`InvBoot.lean`)
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗ bootMarshal ps ctxs bootLog ∗
      -- this node's ghost state at the bootstrap state in the mode `md` (2026-10-25, T-M M2a;
      -- until then static), and the committed boot log
      bootInit γ md cv.ID' (GMap.listToSet ps) bootLog ∗ isCommitted γ bootLog ∗
      -- the cluster's term budget, at least at the bootstrap term `1` (`budget_alloc_boot`)
      inv budgetN (budgetInv bud) ∗ termLB bud (W64 1) ∗
      -- (2026-10-19, D21 M3) in the cluster's no-snapshot mode (`RaftNames.reNoSnap`), a storage
      -- never compacted past index `1` (`Bootstrap`'s)
      NsCap γ.reNoSnap (interface.ok si) ∗
      -- (D22 S-b′3, 2026-10-20) the storage's certificate link (`certLink`: none needed in the
      -- no-snapshot mode)
      certLink γ (interface.ok si) }}
    (App (App (Val #(functions StartNode [])) (Val #c)) (Val #peers))
  {{ (nd : GoInterface), RET #nd;
      -- (D17d, 2026-10-18) what the `InitialState` premise gives back: `InitialState` runs before
      -- the node's goroutine starts
      R ∗ ∃ (γn : NodeNames) (n : Loc),
        ⌜γn.raft = γ ∧ γn.bud = bud ∧ γn.stor = interface.ok si ∧ γn.mode = md ∧
         γn.snapIn = sn ∧ nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        -- (D43 M3, 2026-10-25) the mode is static exactly when the names are (`ownRawNode_mode`)
        ⌜md = .static ↔ γ.reDyn = none⌝ ∗
        isNodeChan γn cv.ID' n ∗ nodeDriverChan γn cv.ID' n [] hsZero ∗
        -- the driver's view of the configuration: the peers'
        nodeCfg γn 0 (cfgState (GMap.listToSet ps) ∅) ∗
        -- the peers' slice, read only
        peers ↦*{dq} pv }}

end spec

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `setupNode`, then as `RestartNode.wp_proof` from `newNode` on: the node's ghost state (the
channels' hand-shakes, the tick channel's invariant, `dlv` and `rof`, the configuration shared
with the driver at the peers), `go n.run()` with `runPre` at the delivered log `[]` (D12: the
boot entries reach the application through the first `Ready`). -/
private theorem StartNode.wp_raw
    (wp_setupNode : setupNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    StartNode.specRaw (GF := GF) (hG := hG) := by
  intro γ md bud c cv lok si σ hs csm R peers dq pv ps ctxs bootLog sn P1 P2 P3 P4 P5 P6 P7 P8 P9 P11
    P12 P13 P14 P15 P16 Q1 Q2 Q3 Q4 Q5 R1 R2 R3 R4 R5 R6 R7 R8 R9 Hfl0 Hhd0 Hsn0
  wp_start as ⟨Hc, #Hlg, #Hsto, Hown, Hinit, Hpeers, #Hctx, #Hmarshal, Hghost, #Hcommitted,
    #Hbud, #Hlb1, #Hnscap, #Hcl⟩
  ihave #Hcinv : raftCommitInv γ $$ [Hghost]
  · iapply bootInit_inv γ md cv.ID' _ bootLog $$ Hghost
  wp_auto
  wp_apply wp_setupNode γ md c cv lok si σ hs csm R peers dq pv ps ctxs bootLog P1 P2 P3 P4 P5 P6 P7
    P8 P9 P11 P12 P13 P14 P15 P16 Q1 Q2 Q3 Q4 Q5 R1 R2 R3 R4 R5 R6 R7 R8 R9 Hfl0 Hhd0
    $$ [$Hc $Hlg $Hsto $Hown $Hinit $Hpeers $Hctx $Hmarshal $Hghost $Hcommitted $Hnscap $Hcl]
    as %np ⟨HR, %nv, %rn, Hn, %Hnvrn, Hchans, Hrn, Hpeers⟩
  ipersist Hn
  try wp_auto
  -- the node's ghost state
  imod dghostVar_alloc ((([] : List EntryM), hsZero) : List EntryM × HardStateM) with ⟨%γdlv, Hdlv⟩
  icases dghostVar_halves _ _ $$ Hdlv with ⟨Hdlv1, Hdlv2⟩
  imod dghostVar_alloc (([], [], [], hsZero, none) : List EntryM × List EntryM ×
    List EntryM × HardStateM × Option SnapLoan) with ⟨%γrof, Hrof⟩
  icases dghostVar_halves _ _ $$ Hrof with ⟨Hrof1, Hrof2⟩
  -- the configuration shared with the driver: the peers'
  imod mono_list_own_alloc ([] : List EntryM) with ⟨%γdlm, Hdlm, #Hdlb⟩
  imod dghostVar_alloc ((0 : Nat), cfgState (GMap.listToSet ps) ∅) with ⟨%γcap, Hcap⟩
  icases dghostVar_halves _ _ $$ Hcap with ⟨Hcap1, Hcap2⟩
  imod dghostVar_alloc ((0 : Nat), cfgState (GMap.listToSet ps) ∅) with ⟨%γccq, Hccq⟩
  icases dghostVar_halves _ _ $$ Hccq with ⟨Hccq1, Hccq2⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γcam, Hcam, #Hcamlb⟩
  -- (D19i part 1) the driver's request on `advancec`
  imod dghostVar_alloc (((none, none) : AdvReq)) with ⟨%γreq, Hreq⟩
  icases dghostVar_halves _ _ $$ Hreq with ⟨Hreq1, Hreq2⟩
  unfold newNodeChans
  icases Hchans with ⟨%γp, %γr, %γc, %γcs, %γrd, %γa, %γt, %γd, %γs, %γst, #Hcp, Hop, #Hcr, Hor,
    #Hcc, Hoc, #Hccs, Hocs, #Hcrd, Hord, #Hca, Hoa, #Hct, Hot, #Hcd, Hod, #Hcs, Hos, #Hcst, Host⟩
  let γn : NodeNames := { raft := γ, id := cv.ID', bud := bud, stor := interface.ok si, propc := γp,
                          recvc := γr, confc := γc, confstatec := γcs, readyc := γrd, advancec := γa, tick := γt,
                          done := γd, stop := γs, status := γst, dlv := γdlv, rof := γrof,
                          mode := md, dlm := γdlm, cap := γcap, ccq := γccq, cam := γcam, req := γreq,
                          snapIn := sn }
  imod start_handshake nv.propc' (propP γn) iprop(True) γp $$ Hcp Hop with #Hhp
  imod start_handshake nv.recvc' (netP γn cv.ID') iprop(True) γr $$ Hcr Hor with #Hhr
  imod start_handshake nv.confc' (confcP γn) iprop(True) γc $$ Hcc Hoc with #Hhc
  imod start_handshake nv.confstatec' (confstateP γn) iprop(True) γcs $$ Hccs Hocs with #Hhcs
  imod start_handshake nv.readyc' (readyP γn) iprop(True) γrd $$ Hcrd Hord with #Hhrd
  imod adv_start γn nv.rn' cv.ID' nv.advancec' $$ Hca Hoa with #Hha
  imod start_handshake nv.done' (fun (_ : Unit) => iprop(False)) iprop(True) γd $$ Hcd Hod
    with #Hhd
  imod start_handshake nv.stop' (fun (_ : Unit) => iprop(False)) iprop(True) γs $$ Hcs Hos
    with #Hhs
  imod start_handshake nv.status' (fun (_ : GoChan) => iprop(False)) iprop(True) γst
    $$ Hcst Host with #Hhst
  imod tickCred_zero bud with Hcr0
  imod inv_alloc tickN ⊤ (tickInv γn) $$ [Hot Hcr0] with #Htickinv
  · inext
    unfold tickInv
    iexists []
    iframe
  icases ownRawNode_shared γ rn cv.ID' _ $$ Hrn with ⟨%r, %lok', #Hrr, #Hrid, #Hrlg, #Hlg', Hrn⟩
  icases ownRawNode_mode γ rn cv.ID' _ $$ Hrn with ⟨%Hmd, Hrn⟩
  ihave #Hnode : isNodeChan γn cv.ID' np $$ []
  · unfold isNodeChan
    iexists nv, r, lok'
    simp only [named]
    rw [Hnvrn]
    iframe #
    ipureintro; rfl
  -- `go n.run()`
  wp_apply wp_fork $$ [Hrn Hdlv1 Hrof1 Hrof2 Hdlm Hcap1 Hcam]
  · wp_apply wp_node_run γn cv.ID' np $$ [Hrn Hdlv1 Hrof1 Hrof2 Hdlm Hcap1 Hcam]
    · iframe Hnode
      unfold runPre
      iexists nv, _, (([], [], [], hsZero, none) : List EntryM × List EntryM × List EntryM ×
        HardStateM × Option SnapLoan)
      rw [Hnvrn]
      iframe Hn Hrn Hrof1 Hrof2
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      iframe Hdlv1 Hlb1
      unfold runCfg
      isplitr
      · ipureintro
        exact ⟨rfl, Nat.le_refl _, rfl, fun _ => ⟨rfl, rfl⟩, Hsn0, fun _ h => by cases h⟩
      isplitl [Hdlm]
      · iExactEq Hdlm; rfl
      iexists 0
      iframe Hcap1 Hcam
      isplitr
      · ipureintro; exact Nat.le_refl _
      iapply undecFree_empty
    itrivial
  iapply HΦ
  iframe HR
  iexists γn, np
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  isplitr
  · ipureintro; exact Hmd
  iframe Hnode Hpeers
  isplitl [Hdlv2 Hreq1 Hreq2]
  · unfold nodeDriverChan dlvLb
    iframe Hnode Hdlv2 Hdlb
    iexists _
    iframe Hreq1 Hreq2
  unfold nodeCfg
  iframe Hcap2 Hcamlb
  iexists _
  iframe Hccq1 Hccq2

end proof

/-! ## The spec, from the raw triple -/

namespace ApiImpl

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `StartNode.spec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem wp_StartNode_impl
    (hS : EtcdGrove.StartNode.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.StartNode.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.StartNode.spec EtcdGrove.Cluster EtcdGrove.isNode EtcdGrove.nodeBoot EtcdGrove.nodeDriver EtcdGrove.storageCertLink
  intro γ N c cv lok si σ hs csm R peers dq pv ps ctxs H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hp He Hss
    Hpe Hhs Hv Hvo Hl Hln Hal Hps Hne Hnd Hnz Hlen Hid Hfl Hhd
  iintro %Φ ⟨#Hinit, Hc, #Hlog, #Hstor, Hown, Hinst, Hpeers, #Hpc, Hboot, #Hlink⟩ HΦ
  iunfold nodeBoot at Hboot
  icases Hboot with ⟨⟨%so, #Hst⟩, %Hok, Hg, #Hc0, #Hm, #Hbinv, #Htlb⟩
  iunfold isStaticCluster at Hst
  icases Hst with ⟨%Hsn, #Hci⟩
  obtain ⟨Hcfg, Hdyn, Hns, -, Hγm, Hsl, Hcert, -⟩ := Hsn
  ihave #Hok' := storCertOk_of_link γ N _ Hcert Hns $$ Hci Hlink
  iapply (hS γ.raft .static γ.bud c cv lok si σ hs csm R peers dq pv ps ctxs γ.raft.reBoot true
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hp He Hss Hpe Hhs Hv Hvo Hl Hln Hal Hps Hne Hnd Hnz Hlen Hid
    Hcfg rfl Hok Hfl Hhd (fun _ => Hns)) $$ [Hc Hown Hinst Hpeers Hg]
  · iframe Hinit Hc Hlog Hstor Hown Hinst Hpeers Hpc Hm Hc0 Hbinv Htlb
    isplitl [Hg]
    · unfold bootInit; iexact Hg
    isplitr
    · unfold NsCap; imodintro; iintro %h; rw [Hns] at h; cases h
    · unfold certLink; iright; iexact Hok'
  iintro !> %nd ⟨HR, %γn, %n, %Hf, -, #Hnode, Hdrv, Hcfg, -⟩
  obtain ⟨Hγr, Hγb, Hγs, Hmd, Hsn, Hnd'⟩ := Hf
  have Hnok : NodeOk γ γn := ⟨Hγr, Hγb, Hsl, by rw [Hmd, Hγm, RNMode.all_self], .inl Hsn⟩
  iapply HΦ
  iframe HR
  iexists n
  isplitr
  · ipureintro; exact Hnd'
  isplitr
  · unfold isNode
    iexists γn
    iframe Hnode Hci
    ipureintro; exact Hnok
  unfold nodeDriver NodeDriverState.init
  iexists γn, cv.ID', []
  isplitr
  · ipureintro; exact ⟨Hnok, Hγs, rfl⟩
  iframe Hci
  isplitr
  · iapply isCommittedLogLb_nil_impl
  isplitl [Hcfg]
  · iright; iframe Hlink; iexists 0, cfgState (GMap.listToSet ps) ∅; iexact Hcfg
  isplitr
  · ileft; ipureintro; rw [Hmd]; rfl
  ileft
  isplitr
  · ipureintro; rfl
  iexact Hdrv

/-- `StartNode.dynamicSpec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem wp_StartNode_dynamic_impl
    (hS : EtcdGrove.StartNode.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.StartNode.dynamicSpec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.StartNode.dynamicSpec EtcdGrove.Cluster EtcdGrove.isNode EtcdGrove.nodeConfig EtcdGrove.nodeDriver EtcdGrove.nodeDynamicBoot
  intro γ N c cv lok si σ hs csm R peers dq pv ps ctxs H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hp He Hss
    Hpe Hhs Hv Hvo Hl Hln Hal Hps Hne Hnd Hnz Hlen Hid Hfl Hhd
  iintro %Φ ⟨#Hinit, Hc, #Hlog, #Hstor, Hown, Hinst, Hpeers, #Hpc, Hboot, #Hcap⟩ HΦ
  iunfold nodeDynamicBoot at Hboot
  icases Hboot with ⟨⟨%c0, %decode, #Hdc⟩, %Hok, Hg, #Hc0, #Hm, #Hbinv, #Htlb, ⟨%g, %Hg0, Ha⟩⟩
  obtain ⟨Hok, Hcfg⟩ := Hok
  ihave #Hdc' := Hdc
  iunfold isDynamicCluster at Hdc'
  icases Hdc' with ⟨%Hdn, #Hci⟩
  have Hns := Hdn.noSnap
  have Hsl : γ.raft.reSnapLoc = (fun _ => none) := by obtain ⟨-, -, -, -, h⟩ := Hdn; exact h
  iapply wp_fupd
  iapply (hS γ.raft (γ.mode inferInstance) γ.bud c cv lok si σ hs csm R peers dq pv ps ctxs
    γ.raft.reBoot false
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hp He Hss Hpe Hhs Hv Hvo Hl Hln Hal Hps Hne Hnd Hnz Hlen Hid
    Hcfg rfl Hok Hfl Hhd (fun h => by cases h)) $$ [Hc Hown Hinst Hpeers Hg]
  · iframe Hinit Hc Hlog Hstor Hown Hinst Hpeers Hpc Hm Hc0 Hbinv Htlb Hg
    isplitr
    · unfold NsCap; imodintro; iintro -; iexact Hcap
    · unfold certLink; ileft; ipureintro; exact Hns
  iintro !> %nd ⟨HR, %γn, %n, %Hf, -, #Hnode, Hdrv, Hcf, -⟩
  obtain ⟨Hγr, Hγb, Hγs, Hmd, -, Hnd'⟩ := Hf
  have Hnok : NodeOk γ γn := ⟨Hγr, Hγb, Hsl, Hmd, .inr Hns⟩
  have Hdy := Hdn.isDyn Hnok
  imod ghost_map_insert_persist cv.ID' (cfgNamesOf γn) (GMap.lookup_empty _) $$ Ha with ⟨-, #He⟩
  ihave #Htb : nodeTabOk (GF := GF) γ cv.ID' γn $$ []
  · unfold nodeTabOk; iexists g; iframe He; ipureintro; exact Hg0
  imodintro
  iapply HΦ
  iframe HR
  iexists n
  isplitr
  · ipureintro; exact Hnd'
  isplitr
  · unfold isNode
    iexists γn
    iframe Hnode Hci
    ipureintro; exact Hnok
  isplitl [Hdrv]
  · unfold nodeDriver NodeDriverState.init
    iexists γn, cv.ID', []
    isplitr
    · ipureintro; exact ⟨Hnok, Hγs, rfl⟩
    iframe Hci
    isplitr
    · iapply isCommittedLogLb_nil_impl
    isplitr
    · ileft; ipureintro; exact Hdy
    isplitr
    · iright; iframe Htb
      isplitr
      · unfold hsCommitted; ileft; ipureintro; rfl
      ileft; ipureintro; exact Hns
    ileft
    isplitr
    · ipureintro; rfl
    iexact Hdrv
  unfold nodeConfig
  iexists γn, cv.ID'
  iframe Hnode Htb
  isplitr
  · ipureintro
    refine ⟨Hnok, Hdy, ?_⟩
    show CCGood (stOf (Membership.simple (GMap.listToSet ps)))
    rw [stOf_simple]; exact ccGood_cfgState _
  rw [stOf_simple]; iexact Hcf

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem StartNode.wp_proof
    (wp_setupNode : setupNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    StartNode.spec (GF := GF) (hG := hG) :=
  ApiImpl.wp_StartNode_impl (StartNode.wp_raw wp_setupNode wp_node_run)

theorem StartNode.wp_proof_dynamic
    (wp_setupNode : setupNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    StartNode.dynamicSpec (GF := GF) (hG := hG) :=
  ApiImpl.wp_StartNode_dynamic_impl (StartNode.wp_raw wp_setupNode wp_node_run)

end proof

end EtcdGrove
end Perennial
