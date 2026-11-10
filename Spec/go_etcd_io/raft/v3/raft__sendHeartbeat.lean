/-
Port of election_proof/spec_raft__sendHeartbeat.v (feb5c73d4).

Lean notes:
* `send_msgs`, `prvals_match` are `sendMsgs`, `prvalsMatch` (`Defs.lean`);
  `msg.mk mtype.Heartbeat …` is `Msg.mk .heartbeat …` (`Protocol/Model.lean`);
  `s <| nstate.prvals := pvs |>` is `{ … with prvals := pvs }`;
  `default (W64 0) (m !! to)` is `(m !! to).getD (W64 0)`. Rocq's untyped `pvs` is a
  `GMap w64 Progress`.
* The reference `raft__sendHeartbeatⁱᵐᵖˡ, new/code/go_etcd_io/raft/v3.v:3240` is to
  the Lean generated code `raft.sendHeartbeat.impl`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.TracedMsg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.sendHeartbeat(to, ctx)` (`raft.sendHeartbeat.impl`; `raft.go:692`):

    pr := r.trk.Progress[to]
    commit := min(pr.Match, r.raftLog.committed)
    r.send(pb.Message{To: to, Type: pb.MsgHeartbeat, Commit: commit, Context: ctx})
    pr.SentCommit(commit)

`to ∈ domSet s.progress` (a voter or a learner; `to ∈ cfg` until 2026-10-13) makes the
lookup hit (otherwise `pr` is nil and `pr.Match` faults);
`to ≠ id` rules out `send`'s self-addressed `Panicf`.

The outbox grows by one `heartbeat` to `to` at the current term whose `Commit` is
`min(Match of to, committed)`; the two bounds the model's `heartbeat_ok` asks for are
exposed as pure facts, against `prvalsMatch` (what `toPstate`'s `matched` is for a
leader) and the log's `committed`. `ctx` is not owned: it is only copied into
`Context`; the abstract message carries the list it holds (`cl`, read-only; since
2026-10-12, when `Msg` gained `ctx`). `SentCommit` writes `sentCommit` and nothing
else, so `Match` is untouched.

**One spec for both trace modes** (2026-11-09, trace-check Q8 stage 1 slice 5): the caller gives
`send`'s hook's gate (`raft.send.spec`'s `HookGateOpt`), at the heartbeat as queued, for whichever
commit `cm` the function computes (with its two bounds), and gets `Q` back. Until slice 5 the premise
`s.gh.tr = none` (stage 0), now `raft.sendHeartbeat.untraced`'s (`TracedUntraced.lean`). (2026-11-10,
slice 14) `Q` is indexed by the heartbeat's commit `cm`, which the gate is given and the postcondition
names: a broadcast's caller indexes its resource by the messages queued so far (`notes/decisions.md`,
"Q8 stage 1 (slice 14)"). -/
abbrev raft.sendHeartbeat.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (to : w64) (ctx : GoSlice)
    (cl : List w8) (Q : w64 → IProp GF),
  to ≠ id →
  to ∈ domSet s.progress →
  -- (2026-10-29, stage U7) the term past `0` that `send` stamps (`SentMsgShape`)
  s.term ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "#Hctx" ∷ ctx ↦*□ cl ∗
      -- (2026-11-09, Q8 stage 1 slice 5) `send`'s hook's gate, at the heartbeat's commit `cm` (its
      -- two bounds)
      "Hgate" ∷ (∀ cm : w64, ⌜uint.Z cm ≤ uint.Z s.logst.committed ∧
          uint.Z cm ≤ uint.Z ((prvalsMatch s.prvals !! to).getD (W64 0))⌝ -∗
        HookGateOpt s.gh.tr r (sendOutGate id s c MsgHeartbeat
          [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl]) (Q cm)) }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"sendHeartbeat"))
      (Val #to)) (Val #ctx))
  {{ (cm : w64) (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c c.voters r id
        { sendMsgs s [Msg.mkV .heartbeat id to s.term false
                        (W64 0) (W64 0) cm (W64 0) [] [] cl] with prvals := pvs } ∗
      ⌜uint.Z cm ≤ uint.Z s.logst.committed⌝ ∗
      ⌜uint.Z cm ≤ uint.Z ((prvalsMatch s.prvals !! to).getD (W64 0))⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ ∗ Q cm }}

end spec

end EtcdGrove
end Perennial
