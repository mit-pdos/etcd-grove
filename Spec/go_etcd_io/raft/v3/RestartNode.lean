/- Lean-first (no Rocq counterpart).

## `RestartNode`

The node API's spec. (2026-10-28: moved here from `NodeApiDraft.lean`, where it was drafted over the
API's sealed predicates, now `InvNode.lean`'s; until then this file held the triple over raft's
internals, now the proof's private `RestartNode.specRaw`.)
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode
public import Proof.go_etcd_io.raft.v3.InvNodeRule

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

/-- **`RestartNode(c)` in a cluster with snapshots and reconfiguration** (2026-11-01, durability
stage I; candidate 12 §4; until then from a founder's or a newcomer's token on an empty storage):
starts node `cv.ID'` of the cluster (`isCluster`), whose id is vacant (`nodeVacant`: no node of it
runs), from a storage holding the contents `σ` (`restartStorage`), at the configuration `m` after
the first `a` committed entries (`confAt`), which the storage's `ConfState` reports; `Applied` is
`0` or within the stored log's committed part.

The client's update (`AU`) fires inside `RestartNode`, when it reads the storage (its
`InitialState`, before any step), and leaves the client's durable state `S` (`raftState`)
unchanged: it checks that the storage holds `S` (`StorageHolds`), so that a stale storage fails it.

Raft names the storage by a fresh key `K` at the attach (`restartStorage`'s continuation). The post:
the node, its `Ready` loop's token at the committed log of the applied index it starts at
(`max σ.b A`), the stored hard state, the durable state `S`, the follower's role, the storage's key;
its view of the configuration at `(a, m)` (the conf entries up to `a` are the client's to skip); its
running token whole; the update's `COMM`; and the storage's frame.

Scope (to file when adopted): `a ≤ σ.commit` (whether a configuration point above the stored commit
is safe is open); a cluster with a bootstrap log restarts a node only once its stored commit covers
the bootstrap log (`γ.bootLen ≤ σ.commit`, review 3's A2); a `MemoryStorage` is attached once.
(2026-11-01: `isCluster` taken, which until then the founder's or newcomer's token held: `nodeVacant`
names no namespace.) -/
abbrev RestartNode.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (σ : StorContents) (csm : ConfStateM) (a : Nat) (m : Membership)
    (Q : RaftState → IProp GF) (F : GName → IProp GF),
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
  -- `Applied` (raft's `appliedTo` panics otherwise; `0`: from the base)
  (uint.nat cv.Applied' = 0 ∨ σ.b ≤ uint.nat cv.Applied' ∧ uint.nat cv.Applied' ≤ σ.commit) →
  -- the configuration point, within the stored committed log [scope]
  max σ.b (uint.nat cv.Applied') ≤ a → a ≤ σ.commit →
  -- the bootstrap log within the stored commit [scope]
  γ.bootLen ≤ σ.commit →
  confStateIs csm m →
  -- (2026-11-02, stage II (p)) at most `2^62` ids in the conf state's lists [scope: `newRaft`'s
  -- premise, the tracker's sort; a valid membership has fewer than `2^62` ids, which bounds the
  -- lists' total only by `2^63`]
  csm.Voters'.length + csm.VotersOutgoing'.length + csm.Learners'.length +
    csm.LearnersNext'.length ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isCluster γ N ∗ nodeVacant γ cv.ID' ∗
      -- (2026-11-02, stage II (p)) the receipts' bound past the bootstrap log within `2^61`
      -- (`readyFits`): the stored log's last index has a time receipt, so it fits a word with room
      -- for one more (`newRaft`'s premise) [scope]
      readyFits γ N ∗
      -- the client's durable state at `RestartNode`'s linearization point (its `InitialState`
      -- read, before any step): the storage holds it
      -- ((2026-11-01, durability stage II (k)) under a later: `raftState` holds an invariant, so
      -- it is not timeless, and a client keeping it in an invariant opens it later-ed)
      AU <{ ∃∃ (S : RaftState), ▷ raftState γ cv.ID' S ∗ ⌜StorageHolds S σ⌝ }> @ ⊤ \ ↑N, ∅
         <{ raftState γ cv.ID' S, COMM Q S }> ∗
      confAt γ a m ∗
      restartStorage γ (interface.ok si) σ csm (uint.nat cv.Applied') F }}
    (App (Val #(functions RestartNode [])) (Val #c))
  {{ (nd : GoInterface), RET #nd;
      ∃ (n : Loc) (S : RaftState) (l : List LogEntry) (K : GName),
        ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNode n γ N cv.ID' ∗
        isCommittedLogLb γ l ∗ ⌜l.length = max σ.b (uint.nat cv.Applied')⌝ ∗
        -- (2026-11-01, durability stage II (k), addendum S1b) the delivered log is the stored
        -- entries up to its length (raft read them from the storage)
        ⌜(LogEntry.toEntries l 0).drop σ.b = σ.ents.take (l.length - σ.b)⌝ ∗
        nodeDriver n γ N ⟨interface.ok si, l, σ.hs, none, K, S, StateFollower⟩ ∗
        nodeConfig n γ N ⟨a, m⟩ ∗
        nodeRunning n γ N 1 ∗
        Q S ∗ F K }}

end spec

end EtcdGrove
end Perennial
