/-
Port of `election_proof/spec_releasePendingReadIndexMessages.v` (feb5c73d4).
-/
module

public import Spec.go_etcd_io.raft.v3.sendMsgReadIndexResponse

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [GooseExts]

/-- The pending requests released at the commit index (before the heartbeats). -/
def releasedState (id : w64) (s : NState) : NState :=
  { s with rd := { s.rd with pend := [], ro := readonlyRelease s.rd.ro id s.logst.committed s.rd.pend } }

/-- The pending requests, read at the commit index (2026-10-14). -/
def pendReqs (s : NState) : List ReadReq :=
  s.rd.pend.map (fun p => ⟨s.logst.committed, p.1.From', p.2⟩)

/-- What releasing the pending requests does at the configuration `c` (2026-10-14, the
single-voter read-index fix): at a configuration whose only voter is the leader itself, each is
answered at once at the commit index (`sendMsgReadIndexResponse`'s first branch); otherwise each
arrives (`readonlyRelease`) and heartbeats are broadcast, each with the position after one of
them. -/
def ReleaseResult (c : CfgM) (id : w64) (s s' : NState) : Prop :=
  (CfgSingle c id ∧
     s' = readRespondAll id { s with rd := { s.rd with pend := [] } } (pendReqs s)) ∨
  (¬ CfgSingle c id ∧ ∃ (ms : List Msg) (pvs : GMap w64 Progress),
     s' = { sendMsgs (releasedState id s) ms with prvals := pvs } ∧
     (∀ m' ∈ ms, HeartbeatOk id (toPState s) m' ∧
       ∃ k, 0 < k ∧ k ≤ s.rd.pend.length ∧
         m'.ctx = hbCtx (readonlyRelease s.rd.ro id s.logst.committed (s.rd.pend.take k))) ∧
     prvalsMatch pvs = prvalsMatch s.prvals)

end results

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `releasePendingReadIndexMessages(r)` (`releasePendingReadIndexMessages.impl`,
`Code/go_etcd_io/raft/v3.lean`; Rocq new/code/go_etcd_io/raft/v3.v:5423;
`raft.go:2115`):

    if len(r.pendingReadIndexMessages) == 0 { return }
    if !r.committedEntryInCurrentTerm() { r.logger.Error(...); return }
    msgs := r.pendingReadIndexMessages
    r.pendingReadIndexMessages = nil
    for _, m := range msgs { sendMsgReadIndexResponse(r, m) }

Each pending request arrives as `sendMsgReadIndexResponse` makes it, read at the commit
index (2026-10-12; until then none was ever pending, the phase-1 scope): the queue holds
them in order (`readonlyRelease`), and each arrival broadcasts heartbeats with the position
after it -- or (2026-10-14, the single-voter fix) at a configuration whose only voter is the
leader itself, each is answered at once (`ReleaseResult`). Each has entries (`req.Entries[0]`
in that branch; the read-only state keeps them so, `RdOk`). The `Error` arm is dead: `stepLeader` calls this only after a successful
`maybeCommit`, which commits an entry of the leader's term (the premise).

**One spec for both trace modes** (2026-11-09, trace-check Q8 stage 1 slice 6): the caller's `G`
through the hook gates of what is sent, back to `G` (persistent: one per request), as
`sendMsgReadIndexResponse.spec`'s: at a single voter, each forwarded response's (at no event);
otherwise each request's heartbeats', the `k`-th request's at the state with the first `k` released
(registered) and with that position as their context. Until slice 6 the premise `s.gh.tr = none`
(stage 0), now `releasePendingReadIndexMessages.untraced`'s (`TracedUntracedSend.lean`). -/
abbrev releasePendingReadIndexMessages.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (G : List Msg → IProp GF),
  s.role = .leader →
  s.term ≠ W64 0 →
  (s.rd.pend ≠ [] →
     plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) s.logst.committed
       = some s.term) →
  (∀ p ∈ s.rd.pend, p.2 ≠ []) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      -- (2026-11-09, Q8 stage 1 slice 6; until then, stage 0, the premise `s.gh.tr = none`) the
      -- caller's resource, through the gates below
      -- (2026-11-10, slice 14) indexed by the outbox, as `sendMsgReadIndexResponse.spec`'s
      "HG" ∷ G s.outbox ∗
      -- each forwarded response's hook gate (a single voter), at no event: a `MsgReadIndexResp`
      "#Hgresp" ∷ □ (⌜CfgSingle c id⌝ -∗ ∀ (mm : Msg) (o : List Msg), ⌜mm.ty = .readIndexResp⌝ -∗ G o -∗
        HookGateOpt s.gh.tr r none (G (o ++ [mm]))) ∗
      -- the `k`-th request's heartbeats' hook gates (otherwise), at the state with the first `k`
      -- requests released ((2026-11-10, slice 17) at the exact commit, `min(committed, Match of to)`)
      "#Hgate" ∷ □ (⌜¬ CfgSingle c id⌝ -∗ ∀ (k : Nat) (to cm : w64) (o : List Msg), ⌜0 < k ∧ k ≤ s.rd.pend.length⌝ -∗
          ⌜to ≠ id ∧ to ∈ domSet s.progress⌝ -∗
          ⌜uint.Z cm = min (uint.Z s.logst.committed)
            (uint.Z ((prvalsMatch s.prvals !! to).getD (W64 0)))⌝ -∗ G o -∗
        HookGateOpt s.gh.tr r (sendOutGate id
            { s with rd := { s.rd with pend := [],
                                       ro := readonlyRelease s.rd.ro id s.logst.committed (s.rd.pend.take k) } }
            c MsgHeartbeat
          [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] []
            (hbCtx (readonlyRelease s.rd.ro id s.logst.committed (s.rd.pend.take k)))])
          (G (o ++ [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] []
            (hbCtx (readonlyRelease s.rd.ro id s.logst.committed (s.rd.pend.take k)))]))) }}
    (App (Val #(functions releasePendingReadIndexMessages [])) (Val #r))
  {{ (s' : NState), RET #();
      ownRaftPhysCV c c.voters r id s' ∗ ⌜ReleaseResult c id s s'⌝ ∗ G s'.outbox }}

end spec

end EtcdGrove
end Perennial
