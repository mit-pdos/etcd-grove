/- Port of election_proof/spec_raft__handleHeartbeat.v (feb5c73d4).

`r.handleHeartbeat(m)` (`raft.handleHeartbeat.impl`,
`Code/go_etcd_io/raft/v3.lean`; `raft.go:1829`), **with etcd-io/raft#140 applied**:

    if r.logSynced {
        r.raftLog.commitTo(min(m.Commit, r.raftLog.lastIndex()))
    }
    r.send(pb.Message{To: m.From, Type: pb.MsgHeartbeatResp, Context: m.Context})

(Before #140: `r.raftLog.commitTo(m.Commit)`, unconditionally, with the premise
`m.Commit ≤ lastIndex()` -- the protocol fact `heartbeat_commit_le_last`, which `Step`
supplied from the leader's `Commit ≤ pr.Match` -- ruling out `commitTo`'s `Panicf`.)

No premise on `m.Commit` any more: `commitTo` is given at most `lastIndex()`, so its
`Panicf` is dead for every message -- the PR's "defence in depth". The other `Panicf`,
`send`'s on a self-addressed `MsgHeartbeatResp`, is ruled out by the premise that the
sender is not this node.

The postcondition is `heartbeatResult`: `committed` becomes `plogCommitTo committed
(min m.Commit lastIndex)` (it never moves back) **if `r.logSynced`**, and is unchanged
otherwise; the outbox grows by exactly the `HeartbeatResp` the model's rule names,
`Msg.plain .heartbeatResp id m.From s.term false`. That is what `SendOk`'s clause (b) makes
of the literal: `send` stamps `From := r.id` and `Term := r.Term`; the literal sets only
`To`/`Type`/`Context`, so `Reject` is `false`, `Index`/`LogTerm`/`Commit`/`RejectHint` are
`0`, and `Entries` is the nil slice, whose list is `[]`; the response's `Context` is `m`'s,
whose list `cl` the abstract response carries (2026-10-12). Adopting the leader (`lead :=
m.From`, `becomeFollower`) is the caller's business (`stepFollower`/`stepCandidate`); this
function does not do it.

That the new commit index is *safe* -- that the entries up to `min(m.Commit, lastIndex())`
are the leader's when `logSynced` holds -- is not this function's business either: it is a
protocol fact, and one the protocol model does not have (`notes/pr-verify/raft-140.md`).

Lean notes: Rocq's `heartbeat_result` is `heartbeatResult`.

raft v3.7 (2026-10-15, stage R4): `m` is a `*pb.Message` (`ml`) read through its getters, at any
fraction (`msgPtsC ml dq dqe cap`, given back: `stepFollower`/`stepCandidate` pass their `msgIn`);
the response `&pb.Message{To: m.From, ..., Context: m.GetContext()}` shares `m`'s `From` cell and
`Context` slice, both read-only (`cellRO`, `↦*□`), and is the caller's no longer (`send`). The
context's list `cl` is the message state's `ctx`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

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
variable [FfiSyntax]

/-- The state after `handleHeartbeat`: `committed` moved by `commitTo`, and the
`HeartbeatResp` queued. Named because `stepFollower` and `stepCandidate` state their
`MsgHeartbeat` results with it. -/
def heartbeatResult (id : w64) (s : NState) (m : MessageM) (cl : List w8 := []) :
    NState :=
  sendMsgs
    { s with logst :=
        { s.logst with committed :=
            if s.logSynced then plogCommitTo s.logst.committed (w64Min m.Commit' (logLast s.logst))
            else s.logst.committed } }
    [{ Msg.plain .heartbeatResp id m.From' s.term false with ctx := cl }]

/-- The result before raft#140: `commitTo(m.Commit)`, unconditionally. -/
def heartbeatResultOld (id : w64) (s : NState) (m : MessageM) (cl : List w8 := []) :
    NState :=
  sendMsgs
    { s with logst :=
        { s.logst with committed := plogCommitTo s.logst.committed m.Commit' } }
    [{ Msg.plain .heartbeatResp id m.From' s.term false with ctx := cl }]

/-- On a synced follower, for a heartbeat within the log (the old premise, `m.Commit ≤
lastIndex()`), the new result is the old one: raft#140 changes nothing for the heartbeats
the old leader sent to a follower that has accepted a `MsgApp` of the term. On an unsynced
follower it does not commit at all. -/
theorem heartbeatResult_synced (id : w64) (s : NState) (m : MessageM) (cl : List w8)
    (Hs : s.logSynced = true) (Hc : uint.Z m.Commit' ≤ uint.Z (logLast s.logst)) :
    heartbeatResult id s m cl = heartbeatResultOld id s m cl := by
  have Hm : w64Min m.Commit' (logLast s.logst) = m.Commit' := by
    unfold w64Min
    split
    · rfl
    · rename_i Hn
      apply uint_Z_inj.1
      omega
  unfold heartbeatResult heartbeatResultOld
  rw [Hs]
  simp only [ite_true]
  rw [Hm]

/-- On an unsynced follower the commit index stays. -/
theorem heartbeatResult_unsynced (id : w64) (s : NState) (m : MessageM) (cl : List w8)
    (Hs : s.logSynced = false) :
    (heartbeatResult id s m cl).logst.committed = s.logst.committed := by
  unfold heartbeatResult sendMsgs
  rw [Hs]
  rfl

end heartbeat_result

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev raft.handleHeartbeat.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (dq dqe : DFrac) (cap : Bool)
    (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (cl : List w8) (rs : List Loc),
  m.From' ≠ id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hm" ∷ msgPtsC ml dq dqe cap ⟨m, ents, sn, cl, rs⟩ }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"handleHeartbeat")) (Val #ml))
  {{ RET #(); ownRaftPhysCV c c.voters r id (heartbeatResult id s m cl) ∗
      msgPtsC ml dq dqe cap ⟨m, ents, sn, cl, rs⟩ }}

/-- The statement on `ownRaftPhys` (the simple configuration `cfg`) until 2026-10-13,
derived from `raft.handleHeartbeat.spec` by `raft.handleHeartbeat.spec_simple`. -/
abbrev raft.handleHeartbeat.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (ml : Loc) (dq dqe : DFrac) (cap : Bool)
    (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (cl : List w8) (rs : List Loc),
  m.From' ≠ id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "Hm" ∷ msgPtsC ml dq dqe cap ⟨m, ents, sn, cl, rs⟩ }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"handleHeartbeat")) (Val #ml))
  {{ RET #(); ownRaftPhys cfg r id (heartbeatResult id s m cl) ∗
      msgPtsC ml dq dqe cap ⟨m, ents, sn, cl, rs⟩ }}

open Iris.ProofMode in
theorem raft.handleHeartbeat.spec_simple
    (H : raft.handleHeartbeat.spec (GF := GF) (hG := hG)) :
    raft.handleHeartbeat.specS (GF := GF) (hG := hG) := by
  intro cfg r id s ml dq dqe cap m ents sn cl rs Hfrom
  iintro %Φ ⟨#Hpkg, Hphys, Hm⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H _ r id s ml dq dqe cap m ents sn cl rs Hfrom $$ [$Hpkg $Hphys $Hm]
  inext
  iintro ⟨Hphys, Hm⟩
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  iapply HΦ
  iframe Hphys Hm

end spec

end EtcdGrove
end Perennial
