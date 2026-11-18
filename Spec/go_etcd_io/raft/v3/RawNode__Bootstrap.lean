/- Lean-first (no Rocq counterpart).

## `RawNode.Bootstrap(peers)` (bootstrap.go:32): a new cluster's initial log

On a node `NewRawNode` just built on an empty storage with an empty conf state (`rawNodeFresh`
at no voter, `InvBoot.lean`), for the peers `peers` (at least one; `len(peers) == 0` and a
non-empty storage are the two error returns, excluded): `rn.prevHardSt = emptyState` (so the
first `Ready` carries the hard state), `becomeFollower(1, None)`, one `EntryConfChange` per peer
(`{Type: AddNode, NodeId: peer.ID, Context: peer.Context}` marshalled, at term `1`, index `i + 1`)
appended to the log, `raftLog.committed = len(peers)` (the raw store: the entries are committed
although unstable, D12), then `applyConfChange((&pb.ConfChange{NodeId: peer.ID, Type:
AddNode}).AsV2())` per peer, which installs the peers as the voters with fresh `Progress`
(`Next = max(lastIndex, 1) = n`, `Match = 0`). Nothing is applied (`applied = applying = 0`): the
application sees the conf changes through the first `Ready` (`StartNode.spec`).

The result is the node closed, `ownRawNode` in the mode `md` at the peers' configuration, with
the delivered log empty, the term `1`, and the ghost state of the bootstrap state (`bootInit γ md
id V bootLog`, allocated before the call: statically `ownRaftGhost γ id (bootPState bootLog)`,
`ownRaftGhost_alloc_boot`; dynamically, since 2026-10-25, T-M M2a, the dynamic model's `rboot c0
bootLog` at the configuration index `0`, `raft_dyn_alloc_boot`), which the physical state refines:
a follower at term `1`, the log `bootLog` from the empty base, committed through it.

The premises are `StartNode.spec`'s on the peers and the bootstrap log (`BootLogOk ps
bootLog`: entry `k` is the `k`-th peer's, which fixes the terms, indices and types the code
writes), and `bootMarshal` ties `proto.Marshal`'s bytes to `bootLog[k].Data'` (protobuf's
determinism at these inputs, a trust-boundary premise discharged where the node is composed;
`InvBoot.lean`). `isCommitted γ bootLog` gives the empty delivered log's `isCommitted γ []`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvBoot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. (2026-11-12, trace-check step 5, bootstrap positions 3 to `|ps| + 3`) Both modes: `γ.reTrace = none` replaced by `s.gh.tr = γ.reTrace` and, traced, pre-vote and check-quorum off with fewer than `2^40` peers; the capability after positions 0-2 and `trNoCut` in; the completion witness `bootDoneG` (minted by `trCapB_bootDone` at the last line) out. -/
abbrev RawNode.Bootstrap.spec : Prop :=
  ∀ (γ : RaftNames) (md : RNMode) (rn r : Loc) (id : w64) (si : GoInterfaceOk) (sdr pre : Bool)
    (s : NState)
    (peers : GoSlice) (dq : DFrac) (pv : List Peer) (ps : List w64) (ctxs : List (List w8))
    (bootLog : List EntryM),
  ps = pv.map Peer.ID' →
  ps ≠ [] → ps.Nodup → W64 0 ∉ ps →
  (ps.length : Int) ≤ 2 ^ 62 →
  id ∈ ps →
  γ.reCfg = GMap.listToSet ps →
  γ.reBoot = bootLog →
  BootLogOk ps bootLog →
  γ.reNoSnap = false →
  -- (step 5) in place of `γ.reTrace = none`: the node's mode the cluster's, and the traced scope
  s.gh.tr = γ.reTrace →
  (γ.reTrace ≠ none → pre = false ∧ s.cq = false ∧ ps.length < 2 ^ 40) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      rawNodeFresh rn r id si ∅ sdr pre s ∗
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗ bootMarshal ps ctxs bootLog ∗
      bootInit γ md id (GMap.listToSet ps) bootLog ∗ isCommitted γ bootLog ∗
      certLink γ s.gh.sn ∗
      -- (step 5) the capability after positions 0-2, and the storage's no-compaction
      trCapB γ.reTrace γ r id (bootCfg ps) false (bootPhase ps id) (bootAt ps id 2) ∗
      trNoCut γ.reTrace (interface.ok si) }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Bootstrap")) (Val #peers))
  {{ (err : GoInterface), RET #err;
      ⌜err = interface.nil⌝ ∗
      ownRawNode γ rn id
        { delivered := [], unpersisted := [], steps := [], term := W64 1,
          storage := interface.ok si, sn := s.gh.sn, mode := md,
          cfg := cfgState (GMap.listToSet ps) ∅, tc := W64 1 } ∗
      peers ↦*{dq} pv ∗
      -- (step 5, A8.3) the completion witness
      bootDoneG γ.reTrace id }}

end spec

end EtcdGrove
end Perennial
