/- Port of election_proof/spec_raft__handleHeartbeat.v (feb5c73d4).

`r.handleHeartbeat(m)` (`raft.handleHeartbeat.impl`,
`EtcdRaft/Code/go_etcd_io/raft/v3.lean`; `raft.go:1822`):

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
slice, whose list is `[]`. (`Context` is not part of the abstraction.) Adopting the
leader (`lead := m.From`, `becomeFollower`) is the caller's business
(`stepFollower`/`stepCandidate`); this function does not do it.

Lean notes: Rocq's `heartbeat_result` is `heartbeatResult`.
-/
import EtcdGrove.Raft.InvRaftPhys

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
variable [FfiSyntax]

/-- The state after `handleHeartbeat`: `committed` moved by `commitTo`, and the
`HeartbeatResp` queued. Named because `stepFollower` and `stepCandidate` state their
`MsgHeartbeat` results with it. -/
def heartbeatResult (id : w64) (s : NState) (m : raftpb.Message) : NState :=
  sendMsgs
    { s with logst :=
        { s.logst with committed := plogCommitTo s.logst.committed m.Commit' } }
    [Msg.plain .heartbeatResp id m.From' s.term false]

end heartbeat_result

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev raft.handleHeartbeat.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message),
  uint.Z m.Commit' ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) →
  m.From' ≠ id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"handleHeartbeat")) (Val #m))
  {{ RET #(); ownRaftPhys cfg r id (heartbeatResult id s m) }}

end spec

end EtcdGrove
end Perennial
