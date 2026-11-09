/-
## `newRaft(c)`

**Users.** `NewRawNode` (`rawnode.go:52`), its only caller (and through it `StartNode`,
`RestartNode`, `node`'s `setupNode`). R1's `NewRawNode.spec` is this spec, then the `RawNode`'s
allocation and `raftBoot_bind`. Snippet: `ready.go` (`ReqNewRawNode`).

**Proof sketch.** `c.validate()` (`Config.validate.spec`: `ConfigOk` passes it; a `nil` logger
becomes `getLogger()`'s, which is `loggerOk`); `newLogWithSize` (R3: the log over the storage, its
committed and applied index at the compaction point `σ.off`); `InitialState` (`isStorage`'s first
method, on `S σ`: the hard state and `cf σ`), where the client's update fires (`StorageHolds D σ`);
`confchange.Restore` (R4) of `cf σ`, which lists `m` (`confAt γ a m`, valid by `confAt_valid`: no
panic, and `assertConfStatesEquivalent` passes, `nonissues/raft-restore-malformed-confstate-panic.md`);
`loadState` (the commit is within `[σ.off, σ.last]`: `StorageHolds`); `appliedTo(Applied)` (within
`[σ.off, σ.hs.commit]`); `becomeFollower(Term, None)`. The ghost state: `nodeVacant γ id` and the
durable state `D` (read in the cluster invariant at the update) start the node's protocol state at
`D`'s term, vote and log; the committed prefix `l` (up to the applied index, which `StorageHolds`
puts within the durable commit) is `committedLb`; the storage's `S σ` goes into the node's ghost
state (R1's `nodeStorage` once bound). The start configuration is `confAt γ a m` (R1's view).

**Changes** (from `specs-ref`'s `newRaft.lean`): over opaque predicates; one spec for a first start
and every restart (was `RNMode`-indexed, with `restartStorage`'s method triples); the node-level
start state is a one-shot `raftBoot`, bound to the `RawNode` by a law.

**Changes (round 1).** The configuration after `validate` is stated (`Config.defaulted`):
`NewRawNode` reads `AsyncStorageWrites` back from it (`rawnode.go:56`).

**Margin.** The view's `prs` is not related to `m` here (R1's `nodeConf` says what the tracker
holds); the panics of an invalid configuration or storage are excluded by the premises.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

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

/-- **A raft struct for node `id`** from a storage holding `σ`: at the stored hard state, a follower with no leader; its node-level start state to bind to a `RawNode`; the client's update fired at the storage read. -/
def newRaft.spec : Prop :=
  ∀ (γ : Cluster) (id : w64) (c : Loc) (cv : go_etcd_io.raft.v3.Config)
    (S : StorState → IProp GF) (cf : StorState → ConfState) (σ : StorState) (a : Nat)
    (m : Membership) (Q : Durable → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ ⌜ConfigOk cv ∧ cv.ID' = id⌝ ∗
      ⌜uint.nat cv.Applied' = 0 ∨
        (σ.off ≤ uint.nat cv.Applied' ∧ uint.nat cv.Applied' ≤ uint.nat σ.hs.commit)⌝ ∗
      ⌜max σ.off (uint.nat cv.Applied') ≤ a ∧ (cf σ).Is m⌝ ∗
      (⌜σ.snap.isEmpty⌝ ∨ snapValid γ σ.snap) ∗
      (⌜cv.Logger' = interface.nil⌝ ∨ loggerOk cv.Logger') ∗
      isStorage cv.Storage' S cf ∗ S σ ∗ confAt γ a m ∗ nodeVacant γ id ∗
      (AU <{ ∃∃ (D : Durable), raftState γ id D ∗ ⌜StorageHolds D σ⌝ }> @ ⊤ \ ↑γ.ns, ∅
        <{ raftState γ id D, COMM Q D }>) }}
    (App (Val (@! go_etcd_io.raft.v3.newRaft)) (Val #c))
  {{ (r : Loc), RET #r;
      ∃ (D : Durable) (l : List LogEntry) (cv' : go_etcd_io.raft.v3.Config) (ρ : CoreView),
      c ↦ cv' ∗ (∃ lg, ⌜cv' = Config.defaulted cv lg⌝ ∗ loggerOk lg) ∗ raftCore r γ id ρ ∗
      ⌜ρ.hs = σ.hs ∧ ρ.lead = W64 0 ∧ ρ.role = StateFollower⌝ ∗
      raftBoot r γ ρ (Driver.start l σ.hs D) ⟨a, m⟩ S l.length (uint.nat σ.snap.index) ∗
      committedLb γ l ∗
      ⌜l.length = max σ.off (uint.nat cv.Applied') ∧
        ∀ j e, σ.off ≤ j → l[j]? = some e → σ.ents[j - σ.off]? = some e⌝ ∗
      Q D }}

end spec
end Raft
end EtcdGrove
end Perennial
