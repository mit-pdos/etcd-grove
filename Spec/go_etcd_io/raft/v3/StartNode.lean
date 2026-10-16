/- Lean-first (no Rocq counterpart).

## `StartNode(c, peers)` (node.go:271): the start of a new cluster

`setupNode(c, peers)` -- `NewRawNode(c)` on the empty storage of a new cluster (whose conf state
is **empty**: `NewRawNode.spec_empty`), then `rn.Bootstrap(peers)` (`RawNode.Bootstrap.spec`):
`becomeFollower(1, None)`, one `EntryConfChange` per peer at term `1` and indices `1..n`
appended to the log and committed (`raftLog.committed = n`), each applied to the tracker
(`applyConfChange`), nothing applied to the application -- in a `node` whose goroutine `run` it
starts, for the cluster's term budget `bud`. It returns the node (`isNode`, persistent: what
`Propose`, `Step`, `Tick` and `Ready` take) and the driver's token (`nodeDriver`), at the empty
delivered log, and the driver's view of the configuration (`nodeCfg`, at index `0` and the
peers' configuration), as `RestartNode.spec` does (2026-10-16, stage R8b, D12).

**Why the driver starts at `[]`.** `Bootstrap` leaves `applied = 0`: the application sees the
conf changes through the first `Ready`, whose `CommittedEntries` are the boot entries beside
`Entries 1..n` and the hard state `{Term: 1, Commit: n}` (`prevHardSt = emptyState`). So the
delivered log is empty although the committed log is `bootLog` (`isCommitted γ bootLog`, the
allocation's): the driver's `Advance` delivers it.

**The ghost state.** The cluster's ghost state is allocated before the call
(`ownRaftGhost_alloc_boot`, `Protocol/Facts.lean`: every member at `bootPState bootLog`, the
committed log `bootLog` from the start, `RaftNames.reBoot = bootLog`), in the static mode with
`γ.reCfg` the peers. This node takes its `ownRaftGhost γ cv.ID' (bootPState bootLog)` and
`isCommitted γ bootLog`, and the log's description `BootLogOk γ.reCCOk ps bootLog` (entry `k`: type
`1`, term `1`, index `k + 1`, bytes decoding to `AddNode ps[k]`, admitted by the cluster's
conf-change policy).

**The bytes** (`bootMarshal`, `InvBoot.lean`): `proto.Marshal` of the `k`-th peer's conf change
returns `bootLog[k]`'s bytes -- protobuf's determinism at these inputs, a trust-boundary fact
taken as a premise in the style of `RestartNode.spec`'s `InitialState` closure, discharged where
the node is composed.

**The peers**: a `[]Peer` slice at `dq` holding `pv`, their ids `ps` (distinct, non-zero, at most
`2^62`, this node among them, the ghost configuration) and their `Context` bytes `ctxs`
(read-only, `peersCtx`). The `Config` premises are `NewRawNode`'s (static mode only: no
`StepDownOnRemoval` requirement). -/
module

public import Proof.go_etcd_io.raft.v3.InvNode
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.NewRawNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev StartNode.spec : Prop :=
  ∀ (γ : RaftNames) (bud : BudgetNames) (c : Loc) (cv : Config)
    (lok si : GoInterfaceOk)
    (σ : StorState)
    (hs : HardStateM) (csm : ConfStateM)
    (peers : GoSlice) (dq : DFrac) (pv : List Peer) (ps : List w64) (ctxs : List (List w8))
    (bootLog : List EntryM),
  -- `NewRawNode`'s premises
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.CheckQuorum' = false →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  cv.PreVote' = false →
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
  BootLogOk γ.reCCOk ps bootLog →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isStorage (interface.ok si) ∗ ownStorage (interface.ok si) σ ∗
      -- `NewRawNode`'s `InitialState` premise (D7's shape; the conf state's record `csm` empty)
      □ (∀ (Φ : val → IProp GF) (ss' : entryID), ownStorage (interface.ok si) { σ with ss := ss' } -∗
           (∀ (hp cs : Loc) (al : Bool), ownStorage (interface.ok si) { σ with ss := ss' } -∗
            hsOpt hp hs -∗ csPts cs DFrac.discard csm al -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
           WP (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #())) {{ Φ }}) ∗
      -- the peers, their contexts, and `Marshal` at their conf changes (`InvBoot.lean`)
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗ bootMarshal ps ctxs bootLog ∗
      -- this node's ghost state at the bootstrap state, and the committed boot log
      ownRaftGhost γ cv.ID' (bootPState bootLog) ∗ isCommitted γ bootLog ∗
      -- the cluster's term budget
      inv budgetN (budgetInv bud) ∗ termLB bud (W64 0) }}
    (App (App (Val #(functions StartNode [])) (Val #c)) (Val #peers))
  {{ (nd : GoInterface), RET #nd;
      ∃ (γn : NodeNames) (n : Loc),
        ⌜γn.raft = γ ∧ γn.bud = bud ∧ γn.stor = interface.ok si ∧ γn.mode = RNMode.static ∧
         nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNode γn cv.ID' n ∗ nodeDriver γn cv.ID' n [] ∗
        -- the driver's view of the configuration: the peers'
        nodeCfg γn 0 (cfgState (GMap.listToSet ps) ∅) ∗
        -- the peers' slice, read only
        peers ↦*{dq} pv }}

end spec

end EtcdGrove
end Perennial
