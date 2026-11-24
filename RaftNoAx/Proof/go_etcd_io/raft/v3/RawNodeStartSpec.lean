-- The copy for the part `RaftNoAx/` of `Proof/go_etcd_io/raft/v3/RawNodeStartSpec.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

## A `RawNode` started in a cluster, closed (2026-11-23, #33 S3a)

`NewRawNode.spec` returns the node **open** (`rawNodeAt`: raft's struct at a state refining the
protocol's restored state, with no ghost state). Until now only `RestartNode` and `StartNode`
closed it (`ownRawNode`, with the id's slot opened by `raft_restart`, the storage named at the
attach), inside their own proofs, and handed the node to `node.run`. A client that drives a
`RawNode` itself (one goroutine per node, `Ready`/`Step`/`Advance` called directly: the Antithesis
harness of mit-pdos/etcd-grove#33) needs that closing step on its own.

`NewRawNode.restartSpec` is it: `NewRawNode` called with `RestartNode`'s precondition, minus the
node API's `run` (no node, no driver token), returns the `RawNode` closed (`ownRawNode` at the
record `rawNodeRestarted …` below), with the generation of the id's slot whole and its free queue
(`genView … 1 g`, `slotFree … g`: what `RawNode.Ready.spec` takes) and the client's durable state
back (`raftState`, opened by `raftState_open` for `Ready`'s *enter*). It is proved over
`NewRawNode.spec` by `RestartNode`'s closing step (`RawNodeStart.lean`). The differences from
`RestartNode.spec`'s precondition:
- the client's durable state is owned (`raftState γ id S` with `StorageHolds S σ`), not behind an
  atomic update: a `RawNode` client has no concurrent `run` to linearize against;
- the rest is the same premise for premise, so that in-process restarts (a later stage of #33)
  start from the same statement.

`rawNodeEmptyStart` (`RawNodeStart.lean`) is the instance for a new cluster's node with an empty
storage whose `ConfState` names the voters (Antithesis's `EtcdBindingEmpty.cfg`).
-/
module

public import RaftNoAx.Proof.go_etcd_io.raft.v3.InvNode
public import RaftNoAx.Proof.go_etcd_io.raft.v3.InvNodeRule
public import RaftNoAx.Proof.go_etcd_io.raft.v3.InvRawnode
public import RaftNoAx.Proof.go_etcd_io.raft.v3.NodeApiVocab
public import RaftNoAx.Proof.go_etcd_io.raft.v3.InvNodeChan
public import RaftNoAx.Proof.go_etcd_io.raft.v3.InvApi
import all RaftNoAx.Proof.go_etcd_io.raft.v3.InvNode
import all RaftNoAx.Proof.go_etcd_io.raft.v3.InvNodeRule

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- The cluster's raft names (what raft's own predicates, `ownRawNode`, `genView`, `ownDurGhost`, are
of), for a `RawNode` client. -/
@[no_expose] def Cluster.raftNames (γ : Cluster) : RaftNames := ApiImpl.Cluster.raft γ

/-- The cluster's term budget names. -/
@[no_expose] def Cluster.budget (γ : Cluster) : BudgetNames := ApiImpl.Cluster.bud γ

/-- The cluster's nodes' mode (static, or dynamic). -/
@[no_expose] def Cluster.rnMode (γ : Cluster) : RNMode := ApiImpl.Cluster.mode γ inferInstance

/-- (#33 S4, 2026-11-24) **`cluster_alloc_nb` with the names' facts**, for a `RawNode` client that
starts its nodes itself (the antithesis harness's `RunCluster`): a new cluster of the voters `vs`
without a bootstrap log, no duplicate proposals, no snapshot directories and no data bound; its raft
names' configuration the voters, no bootstrap log, raft's namespace `N.@"raft"`, untraced, no data
bound. -/
theorem cluster_alloc_names (N : Namespace) (vs : List w64) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) < 2 ^ 62 →
    ⊢ |={E}=> ∃ γ : Cluster,
      ⌜γ.dup = false ∧ γ.bootLen = 0 ∧ γ.maxData = none ∧ ¬ clusterNoSnap γ ∧
        Cluster.trace γ = none⌝ ∗
      ⌜γ.raftNames.reCfg = GMap.listToSet vs ∧ γ.raftNames.reBoot = [] ∧
        γ.raftNames.reNs = N.@"raft" ∧ γ.raftNames.reTrace = none ∧ γ.raftNames.maxData = none⌝ ∗
      ownCommittedOps (GF := GF) γ [] ∗ isCluster γ N ∗
      confAt γ 0 (Membership.simple (GMap.listToSet vs)) ∗
      [∗list] id ∈ vs, raftState γ id RaftState.init ∗ nodeVacant γ id := by
  intro Hrb Hne Hnd Hnz Hlen
  unfold ownCommittedOps isCluster confAt Cluster.dup Cluster.bootLen Cluster.trace Cluster.maxData
    raftState nodeVacant clusterNoSnap Cluster.raftNames
  imod ApiImpl.cluster_alloc_dec_impl (GF := GF) N vs false (fun _ => none) E none
      (fun _ h => by cases h) Hrb Hne Hnd Hnz Hlen
    with ⟨%γ, %Hd, Hops, -, #Hcl, -, #Hca, -, -, Hfs⟩
  imodintro
  iexists γ
  iframe Hops Hcl Hca Hfs
  obtain ⟨h1, -, h3, h4, h5, h6, h7, h8, h9⟩ := Hd
  isplitr
  · ipureintro; exact ⟨h1, h3, h5, by rw [h6]; decide, h4⟩
  ipureintro; exact ⟨h7, h8, h9, h4, h5⟩

/-- **A started `RawNode`'s record** (`NewRawNode.restartSpec`'s post): the committed log `l`
handed out (the stored log up to the applied index it starts at), nothing to persist or to step,
the stored hard state's term, the storage `st` with raft's names `sn` for it, the term ceiling at
the durable state's term, the cluster's mode, the configuration `m` at the configuration index `a`,
the stored hard state as `prevHardSt`, the durable state `S`, a follower; the rest at the
defaults (no snapshot pending or lent, nothing queued). -/
def rawNodeRestarted (γ : Cluster) (l : List EntryM) (st : Storage) (sn : StorNames)
    (hs : HardStateM) (S : RaftState) (m : Membership) (a : Nat) : RNState :=
  { delivered := l, unpersisted := [], steps := [], term := hs.Term', storage := st, sn := sn,
    tc := S.term, mode := γ.rnMode, cfg := ApiImpl.stOf m, capplied := a, phs := hs, dur := S,
    role := StateFollower }

/-- **The client's durable state, opened** (for a `RawNode` client: `RawNode.Ready.spec`'s
*enter* moves raft's durable half `ownDurGhost`): the durable half, the term budget's lower bound
at its term, and the budget's invariant. (`raftState` is sealed for the node API's clients, whose
`node.Ready` does the enter itself.) -/
theorem raftState_open (γ : Cluster) (id : w64) (S : RaftState) :
    raftState (GF := GF) γ id S ⊣⊢
      ownDurGhost γ.raftNames id S ∗ termLB γ.budget S.term ∗ inv budgetN (budgetInv γ.budget) := by
  unfold raftState ApiImpl.raftStateU Cluster.raftNames Cluster.budget
  exact .rfl

/-- **An empty storage's contents** (a node that stored nothing): the zero hard state, no snapshot,
the base `⟨0, 0⟩`, no entries. -/
abbrev emptyStorContents : StorContents :=
  ⟨hsZero, none, entryID.mk (W64 0) (W64 0), []⟩

/-- **The conf state naming the voters `vs`**, simple (no outgoing voters, no learners). -/
abbrev votersConfState (vs : List w64) : ConfStateM := ConfStateM.mk vs [] [] [] false

end api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`NewRawNode(c)` started in a cluster, closed** (see the file header): `RestartNode.spec`'s
precondition with the durable state `S` owned, and the `RawNode` closed in its post. Premises and
resources as `RestartNode.spec`'s (whose docstring explains each): the id `cv.ID'` vacant and armed
at `x`, the receipts' bound (`readyFits`), the configuration `m` after the first `a` committed
entries (`confAt`), which the storage's `ConfState` reports, and the storage holding `σ`
(`restartStorage`, with the frame `F` at raft's key `K`). The post: `err` nil; the `RawNode` at
`rawNodeRestarted` (its committed log `l` handed out: committed, as long as the applied index it
starts at, the stored entries from the base); the id's generation `g` whole with its free queue;
the durable state back; the storage's frame. -/
abbrev NewRawNode.restartSpec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (σ : StorContents) (csm : ConfStateM) (a : Nat) (m : Membership) (S : RaftState)
    (F : GName → IProp GF),
  ∀ (SV : SnapshotM → IProp GF) [∀ sv, Persistent (SV sv)],
  (∀ sv, SV sv ⊢ snapshotValid γ sv) →
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  (γ.maxData ≠ none → uint.Z cv.MaxSizePerMsg' ≤ entsCutMax) →
  (uint.nat cv.Applied' = 0 ∨ σ.b ≤ uint.nat cv.Applied' ∧ uint.nat cv.Applied' ≤ σ.commit) →
  max σ.b (uint.nat cv.Applied') ≤ a → a ≤ σ.commit →
  γ.bootLen ≤ σ.commit →
  confStateIs csm m →
  ¬ clusterNoSnap γ →
  TraceLoggerOk cv.TraceLogger' →
  Cluster.trace γ = none →
  -- the durable state, which the storage holds
  StorageHolds S σ →
  ∀ (x : CrashNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isCluster γ N ∗ nodeVacantA γ cv.ID' x ∗ readyFits γ N ∗
      raftState γ cv.ID' S ∗
      confAt γ a m ∗
      restartStorage γ (interface.ok si) σ csm (uint.nat cv.Applied') F SV }}
    (App (Val #(functions NewRawNode [])) (Val #c))
  {{ (rn : Loc) (err : GoInterface), RET (PairV #rn #err);
      ⌜err = interface.nil⌝ ∗
      ∃ (l : List EntryM) (sn : StorNames) (g : Nat) (K : GName),
        ownRawNode γ.raftNames rn cv.ID' (rawNodeRestarted γ l (interface.ok si) sn σ.hs S m a) ∗
        isCommitted γ.raftNames l ∗
        ⌜l.length = max σ.b (uint.nat cv.Applied') ∧ l.drop σ.b = σ.ents.take (l.length - σ.b)⌝ ∗
        genView γ.raftNames cv.ID' x 1 g ∗ slotFree γ.raftNames cv.ID' g ∗
        raftState γ cv.ID' S ∗ F K }}

/-- **`NewRawNode(c)` for a node of a new cluster without a bootstrap log** (#33's
`EtcdBindingEmpty.cfg`: empty logs at term `0`, the voters from the storage's `ConfState`):
`NewRawNode.restartSpec` at an empty storage (`emptyStorContents`) whose `InitialState` reports the
conf state naming the voters `vs` (`votersConfState`), the durable state `RaftState.init`, nothing
applied, the configuration the voters' simple membership at index `0` (what `cluster_alloc` with no
bootstrap log gives every voter: `raftState … RaftState.init`, `nodeVacant`, `confAt γ 0 …`). The
post: the node at `rawNodeRestarted` with nothing handed out, the zero hard state, term ceiling `0`,
the voters' configuration at index `0`. -/
abbrev NewRawNode.emptyStartSpec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (c : Loc) (cv : Config) (lok si : GoInterfaceOk) (vs : List w64)
    (F : GName → IProp GF),
  ∀ (SV : SnapshotM → IProp GF) [∀ sv, Persistent (SV sv)],
  (∀ sv, SV sv ⊢ snapshotValid γ sv) →
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  (γ.maxData ≠ none → uint.Z cv.MaxSizePerMsg' ≤ entsCutMax) →
  cv.Applied' = W64 0 →
  γ.bootLen = 0 →
  vs.Nodup →
  ¬ clusterNoSnap γ →
  TraceLoggerOk cv.TraceLogger' →
  Cluster.trace γ = none →
  ∀ (x : CrashNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isCluster γ N ∗ nodeVacantA γ cv.ID' x ∗ readyFits γ N ∗
      raftState γ cv.ID' RaftState.init ∗
      confAt γ 0 (Membership.simple (GMap.listToSet vs)) ∗
      restartStorage γ (interface.ok si) emptyStorContents (votersConfState vs) 0 F SV }}
    (App (Val #(functions NewRawNode [])) (Val #c))
  {{ (rn : Loc) (err : GoInterface), RET (PairV #rn #err);
      ⌜err = interface.nil⌝ ∗
      ∃ (sn : StorNames) (g : Nat) (K : GName),
        ownRawNode γ.raftNames rn cv.ID' (rawNodeRestarted γ [] (interface.ok si) sn hsZero RaftState.init
          (Membership.simple (GMap.listToSet vs)) 0) ∗
        genView γ.raftNames cv.ID' x 1 g ∗ slotFree γ.raftNames cv.ID' g ∗
        raftState γ cv.ID' RaftState.init ∗ F K }}

end spec

end EtcdGrove
end Perennial
