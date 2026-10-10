/-
Port of `election_proof/spec_RawNode__Ready.v` (857d09190), made client-facing on
2026-10-09.

Until 2026-10-09 the spec was stated on the node's states: `ownRawNode cfg rn id s rs`
at the `NState` `s`, with `ownRaftGhost`, `NStateRel` and the `Step.drain` it takes in
the postcondition; the committed entries as `∃ pre, isCommitted γ (pre ++ ce)` with
`pre` as long as `s.logst.applying`, and `ce` a prefix of `logCommittedEnts s.logst`;
the messages' abstractions in the protocol outbox `ps.outbox`; and the values of
`HardState`, `SoftState` and `MustSync` against the previous ones. Those are gone: the
committed entries extend `rs.delivered`, the messages are `isRaftMsg`, and nothing is
said of `HardState`/`SoftState`/`MustSync`, which only a durability argument (phase 2)
would need.

Lean notes: As for `raft.Step.spec`, the section fixes `hlc := HasLC.hasLC` and has
`[AllG GF]` (`ownRawNode` holds ghost state); `zero_val _` is written at its type.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- `rn.Ready()` (`rawnode.go:133`) is `readyWithoutAccept` then `acceptReady`.

Premises: `Advance` ran since the last `Ready` (`acceptReady` `Panicf`s on a non-empty
`stepsOnAdvance`), and the application appended the previous `Ready`'s entries to the
storage (and handed the receipt back, `ownRawNode_appended`).

The `Ready` it returns:
- `CommittedEntries`: `ce`, read-only, the committed entries right after the ones
  handed out so far -- `rs.delivered ++ ce` is a prefix of the global committed log
  (`isCommitted`, `Protocol`): the entries the application applies are the cluster's,
  in order and without gaps (`ce` may be empty, e.g. while applying is paused);
- `Entries`: `es`, read-only, the entries the application must append to the storage
  before the next `Ready` (`RNState.unpersisted`), with the right to do so
  (`appendRight`, 2026-10-10: the storage's hand-out law, `InvStorage.lean`), which an
  implementation's `Append` turns into the receipt `ownRawNode_appended` takes back --
  on the application's goroutine, while the node keeps reading the storage;
- `Messages`: the application's slice, to send; each message is `isRaftMsg`;
- `Snapshot` empty and `ReadStates` nil (no snapshot pending, no read-index request in
  scope).

The node's new state: `delivered` grows by `ce`, `unpersisted` is `es`, and the local
messages for `Advance` are queued (`steps`), which `Advance` takes whatever they are.
(Until 2026-10-10 the postcondition also returned a flag `advanceable`, whether
`Advance` was proved for the queue: not when it held a self-addressed response, which
no client could rule out.) -/
abbrev RawNode.Ready.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState),
  rs.steps = [] →
  rs.unpersisted = [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Ready")) (Val #()))
  {{ (rd : Ready) (ce es : List raftpb.Entry) (ms : List raftpb.Message)
      (steps : List Pending), RET #rd;
      "Hrn" ∷ ownRawNode γ rn id
        { rs with delivered := rs.delivered ++ ce, unpersisted := es, steps := steps } ∗
      "#Hce" ∷ rd.CommittedEntries' ↦*□ ce ∗
      "#Hcommitted" ∷ isCommitted γ (rs.delivered ++ ce) ∗
      "#Hents" ∷ rd.Entries' ↦*□ es ∗
      "Hmsgs" ∷ rd.Messages' ↦* ms ∗
      "Hmsgs_cap" ∷ ownSliceCap raftpb.Message rd.Messages' (DFrac.own 1) ∗
      "#Hmsgs_ok" ∷ ([∗list] m ∈ ms, isRaftMsg γ m) ∗
      -- every message is of a term at most the node's at the call (2026-10-10)
      "%Hmsgs_term" ∷ ⌜∀ m ∈ ms, uint.Z m.Term' ≤ uint.Z rs.term⌝ ∗
      "%Hsnapz" ∷ ⌜rd.Snapshot' = zero_val raftpb.Snapshot ∧
                   rd.ReadStates' = slice.nil⌝ ∗
      -- the right to append `es` to the node's storage (2026-10-10)
      "Happ" ∷ appendRight rs.storage es }}

end spec

end EtcdGrove
end Perennial
