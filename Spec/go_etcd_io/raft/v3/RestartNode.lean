/-
## `RestartNode(c)`

**Users.** etcd's `newRaftNode` with a WAL (`bootstrapRaftFromWAL`: a `MemoryStorage` rebuilt from
the WAL's snapshot, hard state and entries, `bwal.MemoryStorage()`, `Applied` 0) and for a member
joining an existing cluster (`bootstrapRaftFromCluster` with no peers: an empty `MemoryStorage`);
the examples' every start (`examples/raft/kv`, `kvreconf`, `kvdurable`, `kvfile`: a storage holding
the initial configuration in an index-0 snapshot or its `InitialState`, or the replica's file, with
`Applied` 0 or at most the stored snapshot's index). Snippets: `restart.go` (`ReqRestartDurable`,
`ReqJoin`), `storage.go` (`ReqBootstrapFromWAL`).

**Proof sketch.** `NewRawNode` (`newRaft`: validate; `InitialState` on the detached storage, the
client's update fired there -- `StorageHolds D σ` and the client's `raftState γ id D`, which raft's
invariant ties to the committed log: the stored entries up to the stored commit are committed,
`committedLb γ l`; the tracker restored from `cf σ`, the configuration at `a`, `confAt γ a m`;
`appliedTo(Applied)`; `S σ` into the node's invariant); `newNode`; `go n.run()`.

**Changes** (from `specs-ref`'s `RestartNode.lean`, durability stage II (u)): over opaque predicates;
any `Storage` (`isStorage`, with the configuration `InitialState` reports, `cf σ`) in place of
`restartStorage`'s method triples and the storage key; no `readyFits` (receipt bounds) nor the
bootstrap-length premise (`γ.bootLen ≤ σ.commit`: a restart below the bootstrap log has an empty or
partial configuration, which `confAt γ a m` with `(cf σ).Is m` must still name -- a joiner's empty
one at index 0, `cluster_alloc`); `Applied`'s premise as before (`appliedTo` panics outside it); the
configuration point `a` as before (`nonissues/raft-applied-above-snapshot-confstate.md`).

**Round 1.** The configuration point `a` is no longer bounded by the stored commit (completeness F1,
provability S3: etcd restarts at the backend's configuration, at its consistent index, which a crash
can leave above the WAL's commit: `bootstrap.go:107-116`, `632-636`); `confAt γ a m` alone says the
first `a` entries are committed cluster-wide, and raft's restored tracker is that committed
configuration (an obligation on raft's invariant, R2: `req/go_etcd_io_raft_v3.md`). The stored
snapshot is empty or valid (provability F3: raft sends it in `MsgSnap`s).

**Margin.** The node starts a follower at the stored term; the delivered log is the committed log up
to the applied index, whose stored part the post states. Out of scope: `--force-new-cluster`
(`bootstrap.go:628-648`: etcd raises the WAL's commit and manufactures conf entries outside raft,
which no cluster history admits). A crash's vacancy is `Api.lean`'s crossing's (`raftState_gen`,
`raftState_crash`: verify-round F-raft-storage F1); the start's first step refutes the `crashed`
disjunct of the vacancy's realization (the generation's `notCrashed`).
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

/-- **Restarts node `id` of `γ` from a storage holding `σ`**, which holds the client's durable state
(checked by the client's update when raft reads the storage), at the configuration `m` after the
first `a` committed entries (which the storage reports). Returns the running node, its driver at the
committed log up to the applied index, its configuration view at `a`, its storage's handle. -/
def RestartNode.spec : Prop :=

  ∀ (γ : Cluster) (id : w64) (c : Loc) (cv : go_etcd_io.raft.v3.Config)
    (S : StorState → IProp GF) (cf : StorState → ConfState) (σ : StorState) (a : Nat)
    (m : Membership) (Q : Durable → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗
      ⌜ConfigOk cv ∧ cv.ID' = id⌝ ∗
      ⌜uint.nat cv.Applied' = 0 ∨
        (σ.off ≤ uint.nat cv.Applied' ∧ uint.nat cv.Applied' ≤ uint.nat σ.hs.commit)⌝ ∗
      ⌜max σ.off (uint.nat cv.Applied') ≤ a ∧ (cf σ).Is m⌝ ∗
      (⌜σ.snap.isEmpty⌝ ∨ snapValid γ σ.snap) ∗
      (⌜cv.Logger' = interface.nil⌝ ∨ loggerOk cv.Logger') ∗
      isStorage cv.Storage' S cf ∗ S σ ∗ confAt γ a m ∗ nodeVacant γ id ∗
      (AU <{ ∃∃ (D : Durable), raftState γ id D ∗ ⌜StorageHolds D σ⌝ }> @ ⊤ \ ↑γ.ns, ∅
        <{ raftState γ id D, COMM Q D }>) }}
    (App (Val (@! go_etcd_io.raft.v3.RestartNode)) (Val #c))
  {{ (nd : GoInterface), RET #nd;
      ∃ (n : Loc) (D : Durable) (l : List LogEntry) (cv' : go_etcd_io.raft.v3.Config),
      ⌜nd = nodeIface n⌝ ∗ c ↦ cv' ∗ isNode n γ id ∗ nodeRunning n 1 ∗
      committedLb γ l ∗
      ⌜l.length = max σ.off (uint.nat cv.Applied') ∧
        ∀ j e, σ.off ≤ j → l[j]? = some e → σ.ents[j - σ.off]? = some e⌝ ∗
      nodeDriver n γ (Driver.start l σ.hs D) ∗ nodeConf n γ ⟨a, m⟩ ∗
      nodeStorage n γ S ∗ appliedLb n l.length ∗ storSnapLb n (uint.nat σ.snap.index) ∗ Q D }}

end spec
end Raft
end EtcdGrove
end Perennial
