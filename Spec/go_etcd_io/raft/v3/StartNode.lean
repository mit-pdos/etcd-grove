/-
## `StartNode(c, peers)`

**Users.** etcd's `bootstrappedRaft.newRaftNode` (`server/etcdserver/bootstrap.go:599`), a member of a
new cluster (`--initial-cluster-state new`, no WAL): `raftConfig` (CheckQuorum on, PreVote as
configured, `Applied` 0) over a fresh `MemoryStorage`, peers the members with their JSON contexts.
No example uses it (they start with `RestartNode` on a storage holding the configuration). Snippet:
`examples/specreq/raftnode/restart.go` (`ReqStartFresh`).

**Proof sketch.** `setupNode` (`NewRawNode`: `newRaft` validates the configuration, reads the empty
storage's `InitialState` and attaches it -- `S StorState.empty` into the node's invariant, with
`nodeStorage`; `Bootstrap` appends and commits the bootstrap log, which `bootLog γ boot` says is the
cluster's, and switches the tracker to the voters, `confAt γ |boot|` from `cluster_alloc`); the client's
update fires inside `newRaft` at the storage read (checks the durable state is empty); `newNode`;
`go n.run()` with `nodeLoop`. The node's invariant is allocated at `γ.ns`, holding the vacancy.

**Changes** (from `specs-ref/Spec/go_etcd_io/raft/v3/StartNode.lean`): over opaque predicates; the
storage is any `Storage` (its contract `isStorage`), not a `MemoryStorage` key; the configuration
premises are `ConfigOk` (no `ReadOnlyOption`/`DisableProposalForwarding` restriction beyond
`ConfigOk`'s scope, any CheckQuorum/PreVote/StepDownOnRemoval/size limits); no `nodeStartedFresh`,
`readyFits` (receipt bounds); the view starts after the bootstrap log (the bootstrap `AddNode`s are
re-delivered and re-applied as no-ops: `node.ApplyConfChange.spec`'s second case).

**Margin.** A non-empty storage is excluded (Go logs a warning and runs the node as a restart:
`nonissues/raft-startnode-nonempty-storage-silent-restart.md`); the config `c` is returned with
`validate`'s defaults written.
-/
module

public import Spec.go_etcd_io.raft.v3.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [ctx_sem : context.Assumptions]

/-- **Starts node `id` of `γ` as a founding member** from an empty storage: the bootstrap log `boot`
of `peers` is the cluster's; the client's update checks its durable state is empty. Returns the
running node, its `Ready` loop's token at the empty delivered log, its configuration view at the
voters after the bootstrap log, and its storage's handle. -/
def StartNode.spec : Prop :=

  ∀ (γ : Cluster) (id : w64) (c : Loc) (cv : go_etcd_io.raft.v3.Config) (peers : GoSlice)
    (dq : DFrac) (ps : List (w64 × List w8)) (boot : List LogEntry)
    (S : StorState → IProp GF) (cf : StorState → ConfState) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗
      ⌜ConfigOk cv ∧ cv.ID' = id ∧ cv.Applied' = W64 0 ∧ ps ≠ [] ∧ BootLog ps boot ∧
        cf StorState.empty = ConfState.empty⌝ ∗
      (⌜cv.Logger' = interface.nil⌝ ∨ loggerOk cv.Logger') ∗
      isStorage cv.Storage' S cf ∗ S StorState.empty ∗ peersPts peers dq ps ∗ bootLog γ boot ∗
      nodeVacant γ id ∗
      (AU <{ ∃∃ (D : Durable), raftState γ id D ∗ ⌜D = Durable.init⌝ }> @ ⊤ \ ↑γ.ns, ∅
        <{ raftState γ id D, COMM Q }>) }}
    (App (App (Val (@! go_etcd_io.raft.v3.StartNode)) (Val #c)) (Val #peers))
  {{ (nd : GoInterface), RET #nd;
      ∃ (n : Loc) (cv' : go_etcd_io.raft.v3.Config), ⌜nd = nodeIface n⌝ ∗ c ↦ cv' ∗
      isNode n γ id ∗ nodeRunning n 1 ∗
      nodeDriver n γ (Driver.start [] HardState.empty Durable.init) ∗
      nodeConf n γ ⟨boot.length, Membership.simple (listToSet (ps.map (·.1)))⟩ ∗
      nodeStorage n γ S ∗ appliedLb n 0 ∗ storSnapLb n 0 ∗ peersPts peers dq ps ∗ Q }}

end spec
end Raft
end EtcdGrove
end Perennial
