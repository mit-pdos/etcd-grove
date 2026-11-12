/- Port of election_proof/spec_raft__handleHeartbeat.v (feb5c73d4).

`r.handleHeartbeat(m)` (`raft.handleHeartbeat.impl`,
`Code/go_etcd_io/raft/v3.lean`; `raft.go:1822`):

    r.raftLog.commitTo(m.Commit)
    r.send(pb.Message{To: m.From, Type: pb.MsgHeartbeatResp, Context: m.Context})

Two exits that are not `return`: `commitTo` `Panicf`s when `m.Commit > lastIndex()`, and
`send` `Panicf`s on a self-addressed `MsgHeartbeatResp` (it goes onto `r.msgs`). Each is
ruled out by a premise: the first is the protocol fact `heartbeat_commit_le_last`
(`Protocol/Facts.lean`) that `Step` supplies, stated on the log as `ownRaftPhys`
records it; the second is that the sender is not this node.

The postcondition is the follower's half of `Step.heartbeat`: `committed` becomes
`plogCommitTo committed m.Commit` (it never moves back) and the outbox grows by exactly
the `HeartbeatResp` the model's rule names, `Msg.plain .heartbeatResp id m.From s.term
false`. That is what `SendOk`'s clause (b) makes of the literal: `send` stamps `From :=
r.id` and `Term := r.Term`; the literal sets only `To`/`Type`/`Context`, so `Reject` is
`false`, `Index`/`LogTerm`/`Commit`/`RejectHint` are `0`, and `Entries` is the nil
slice, whose list is `[]`; the response's `Context` is `m`'s, whose list `cl` the abstract
response carries (2026-10-12). Adopting the
leader (`lead := m.From`, `becomeFollower`) is the caller's business
(`stepFollower`/`stepCandidate`); this function does not do it.

Lean notes: Rocq's `heartbeat_result` is `heartbeatResult`.

raft v3.7 (2026-10-15, stage R4): `m` is a `*pb.Message` (`ml`) read through its getters, at any
fraction (`msgPtsC ml dq dqe cap`, given back: `stepFollower`/`stepCandidate` pass their `msgIn`);
the response `&pb.Message{To: m.From, ..., Context: m.GetContext()}` shares `m`'s `From` cell and
`Context` slice, both read-only (`cellRO`, `↦*□`), and is the caller's no longer (`send`). The
context's list `cl` is the message state's `ctx`.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- `MsgBeat = 1` (`raftpb`): the local tick that makes a leader `bcastHeartbeat`.
`Defs.lean` names the types the model describes; `MsgBeat` is not one of them, and
lives here, beside the heartbeat handler, because all three `stepX` specs mention it
(until 2026-10-02 it was local to `Spec/stepLeader.lean`). -/
def MsgBeat : w32 := W32 1

section heartbeat_result
variable [GooseExts]

/-- The state after `handleHeartbeat`: `committed` moved by `commitTo`, and the
`HeartbeatResp` queued. Named because `stepFollower` and `stepCandidate` state their
`MsgHeartbeat` results with it. -/
def heartbeatResult (id : w64) (s : NState) (m : MessageM) (cl : List w8 := []) :
    NState :=
  sendMsgs
    { s with logst :=
        { s.logst with committed := plogCommitTo s.logst.committed m.Commit' } }
    [{ Msg.plain .heartbeatResp id m.From' s.term false with ctx := cl }]

end heartbeat_result

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev raft.handleHeartbeat.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (dq dqe : DFrac) (cap : Bool)
    (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (cl : List w8) (rs : List Loc),
  uint.Z m.Commit' ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) →
  m.From' ≠ id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hm" ∷ msgPtsC ml dq dqe cap ⟨m, ents, sn, cl, rs⟩ }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"handleHeartbeat")) (Val #ml))
  {{ RET #(); ownRaftPhysCV c c.voters r id (heartbeatResult id s m cl) ∗
      msgPtsC ml dq dqe cap ⟨m, ents, sn, cl, rs⟩ }}

end spec

end EtcdGrove
end Perennial
