/-
Port of `election_proof/spec_newRaft.v`.

# `newRaft`: the constructor of `ownRaftPhys`

This triple is the witness that `ownRaftPhys` is **satisfiable** by a struct the Go code
actually builds: from a `Config` and a `Storage` it produces `ownRaftPhys cfg r id s` at
a well-formed follower state. Every other spec in the development takes `ownRaftPhys`
as given; this is the one that establishes it.

## What it assumes, and why

`newRaft` panics on several inputs, and its spec has to exclude each one. The premises
are, in order:

- `ConfigValid cv` (`Spec/Config__validate.lean`): what `validate` checks, so
  `validate` returns `nil` -- plus a non-nil `Logger`.
- **`MaxInflightMsgs < 2^62`: not implied by `validate`**, which only checks `> 0`.
  `ownTracker`'s `HmaxInfl` (`InvTracker.lean`) demands it because `Inflights.grow`
  computes `len(buffer) * 2`, which overflows a Go `int` once the buffer reaches
  `2^62`. So `ownRaftPhys` is **unsatisfiable for a valid `Config` with
  `MaxInflightMsgs ≥ 2^62`** (found writing this spec, 2026-09-24). Not a bug a real run
  can hit -- the buffer only grows to `2^62` with that many messages in flight -- but a
  gap between what raft accepts and what the proof covers.
- the development's scope: `PreVote = CheckQuorum = false`.
- the storage's contents (`ownStorage (interface.ok si) prev ents`): contiguous indices
  and **no configuration-change entry**. The second is `HnoConfChange`'s scope
  assumption and is false of a node `RawNode.Bootstrap` just bootstrapped
  (notes/STATUS.md).
- `Storage.InitialState` returns `(hs, cs, nil)` and lends `cs.Voters`. This is a
  premise, not a clause of `isStorage`: it is a fact about one storage at one moment,
  and nothing else calls the method.
- `hs.Commit` lies in `[prev.index, lastIndex]` unless `hs` is empty (else `loadState`
  panics), and `Applied` is `0` or lies in `[prev.index, committed]` (else `appliedTo`
  panics).
- the `ConfState` is **voters-only**, with a non-empty list of **distinct, non-zero**
  voters. Each clause is needed: learners/joint configurations are out of scope;
  `Restore` skips a zero id and de-duplicates, after which `assertConfStatesEquivalent`
  panics; and an empty voter set is what a node joining an existing cluster starts with
  (etcd's `StartNode` with no peers), which `ownTracker`'s `Hcfg_ne` excludes -- so
  **such a node is outside the development** until it receives a snapshot, which is out
  of scope too.

## What it gives

`ownRaftPhys` over the voter set, at a state that is `NStateWf` (ready for `Step`), a
follower with no leader, an empty tally and an empty outbox, whose `term` and `vote` are
the persisted `HardState`'s. For a fresh storage (`hs` empty) that is
`NStateRel s initPState` (`newRaft_post_init`, Rocq `election.v`): the struct `newRaft`
builds refines the protocol state `ownRaftGhost_alloc` starts every node in.

Lean notes: the `InitialState` premise's `WP` is applied to the value
`#(methods si.ty go!"InitialState" si.v)`, as in `isStorage`; Rocq's
`Φ (#hs, #cs, #interface.nil)%V` is `Φ (PairV (PairV #hs #cs) #interface.nil)`.
`HsEmpty` gets a `Decidable` instance so that `committedAfter` can branch on it
(Rocq's `bool_decide`).
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys
import EtcdGrove.Raft.ElectionProof.Spec.Config__validate

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [FfiSyntax]

def HsEmpty (hs : raftpb.HardState) : Prop :=
  hs.Term' = W64 0 ∧ hs.Vote' = W64 0 ∧ hs.Commit' = W64 0

instance HsEmpty.decidable (hs : raftpb.HardState) : Decidable (HsEmpty hs) := by
  unfold HsEmpty; infer_instance

/-- `raftLog.committed` after `newRaft`'s `loadState` (skipped for an empty
`HardState`). -/
def committedAfter (prev : entryID) (hs : raftpb.HardState) : w64 :=
  if HsEmpty hs then prev.index' else hs.Commit'

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `newRaft(c)`: see the file header. -/
abbrev newRaft.spec : Prop :=
  ∀ (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (prev : entryID) (ents : List raftpb.Entry)
    (hs : raftpb.HardState) (cs : raftpb.ConfState)
    (voters : List w64) (dqv : DFrac),
  -- the Config
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.PreVote' = false →
  cv.CheckQuorum' = false →
  -- the stored log
  LogIndicesOk prev ents →
  (∀ e ∈ ents, e.Type' = EntryNormal) →
  -- the persisted HardState
  (¬ HsEmpty hs →
   uint.Z prev.index' ≤ uint.Z hs.Commit' ∧
     uint.Z hs.Commit' ≤ uint.Z prev.index' + (ents.length : Int)) →
  (cv.Applied' = W64 0 ∨
   uint.Z prev.index' ≤ uint.Z cv.Applied' ∧
     uint.Z cv.Applied' ≤ uint.Z (committedAfter prev hs)) →
  -- the persisted ConfState: voters only
  voters ≠ [] → voters.Nodup → W64 0 ∉ voters →
  cs.VotersOutgoing'.len = W64 0 →
  cs.Learners'.len = W64 0 →
  cs.LearnersNext'.len = W64 0 →
  cs.AutoLeave' = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isStorage (interface.ok si) ∗ ownStorage (interface.ok si) prev ents ∗
      □ (∀ Φ : val → IProp GF, ownStorage (interface.ok si) prev ents -∗
           (ownStorage (interface.ok si) prev ents -∗
            cs.Voters' ↦*{dqv} voters -∗
            Φ (PairV (PairV #hs #cs) #interface.nil)) -∗
           WP (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #())) {{ Φ }}) }}
    (App (Val #(functions newRaft [])) (Val #c))
  {{ (r : Loc) (s : NState), RET #r;
      ownRaftPhys (GMap.listToSet voters) r cv.ID' s ∗
      ⌜NStateWf s ∧
        s.term = hs.Term' ∧
        s.vote = hs.Vote' ∧
        s.lead = W64 0 ∧ s.role = .follower ∧
        s.votes = ∅ ∧ s.outbox = []⌝ }}

end spec

end EtcdGrove
end Perennial
