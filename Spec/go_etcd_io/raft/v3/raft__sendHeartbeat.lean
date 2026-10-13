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

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
else, so `Match` is untouched. -/
abbrev raft.sendHeartbeat.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (to : w64) (ctx : GoSlice)
    (cl : List w8),
  to ≠ id →
  to ∈ domSet s.progress →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "#Hctx" ∷ ctx ↦*□ cl }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"sendHeartbeat"))
      (Val #to)) (Val #ctx))
  {{ (c : w64) (pvs : GMap w64 Progress), RET #();
      ownRaftPhys cfg r id
        { sendMsgs s [Msg.mkV .heartbeat id to s.term false
                        (W64 0) (W64 0) c (W64 0) [] [] cl] with prvals := pvs } ∗
      ⌜uint.Z c ≤ uint.Z s.logst.committed⌝ ∗
      ⌜uint.Z c ≤ uint.Z ((prvalsMatch s.prvals !! to).getD (W64 0))⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

end spec

end EtcdGrove
end Perennial
