/-
## `raft.handleAppendEntries(m)` (internal)

**Users.** `stepFollower`, `stepCandidate` (after becoming a follower of the term).

**Proof sketch.** Below the commit index: acknowledge the commit index. Else R3's `maybeAppend` (the sender led the term, `msgSent_leaderOf`; its `msgSent` says its log holds the entries after the matching `(index, logTerm)`: by log matching, a conflict is past the commit index, so no panic; the new commit `min(commit, last new)` is committed) and an acknowledgement of the last new index (queued after the append: its `msgSent` once durable), or a rejection with a hint (R3's `findConflictByTerm`).

**The entries' capacity (integration I2, the coordinator's decision).** `raftLog.maybeAppend` (R3)
takes the slice with no spare capacity or with its capacity owned (`unstable.truncateAndAppend`
may adopt it, `u.entries = ents`, and a later append writes into its capacity). The message is a
received one (`msgRecv`: rafthttp's decoders give fresh slices; raft's own `MsgApp`s have none, `raftLog.slice`
clipping them; an in-process transport clones,
`nonissues/raft-msgapp-inprocess-aliasing.md`), so `logSliceFromMsgApp` (with `rc = true`) splits
its capacity off with the entries (`entriesRO … (index + 1)`), and the suffix `a.entries[ci -
offset:]` that `maybeAppend` appends keeps the rest of it. **Alternative, open for the user:** the
fork clips the slice in `logSliceFromMsgApp` (`slices.Clip(m.GetEntries())`, behavior-preserving),
after which `len = cap` and no message needs its capacity.

**Changes** (from `specs-ref`'s `raft__handleAppendEntries.lean`): over `raftCore` and `msgSent`.

**Margin.** The new view keeps the term, vote, leader and role; its commit index is not stated.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

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

/-- (internal) Handles a `MsgApp` of the follower's term. -/
def raft.handleAppendEntries.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (ml : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ msgRecv ml m ∗ msgSent γ m ∗
      ⌜m.type = MsgApp ∧ m.to = id ∧ m.term = ρ.hs.term ∧ ρ.role = StateFollower⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"handleAppendEntries")) (Val #ml))
  {{ RET #(); ∃ ρ', raftCore r γ id ρ' ∗ ⌜ρ'.hs.term = ρ.hs.term ∧ ρ'.hs.vote = ρ.hs.vote ∧ ρ'.lead = ρ.lead ∧ ρ'.role = ρ.role⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
