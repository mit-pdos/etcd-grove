/-
Port of `election_proof/spec_raft__bcastHeartbeatWithCtx.v` (feb5c73d4).

Lean notes: the type of Rocq's untyped binder `pvs` is written out
(`GMap w64 Progress`, as `NState.prvals` forces it); `prole.Leader` is `.leader`;
`send_msgs s ms <| nstate.prvals := pvs |>` is `{ sendMsgs s ms with prvals := pvs }`;
`Forall (heartbeat_ok id ps) ms` is `∀ m ∈ ms, HeartbeatOk id ps m`; `to_pstate`,
`prvals_match` are `toPState`, `prvalsMatch` (`Defs.lean`).
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

/-- `r.bcastHeartbeatWithCtx(ctx)` (`raft.bcastHeartbeatWithCtx.impl`,
`Code/go_etcd_io/raft/v3.lean`; Rocq new/code/go_etcd_io/raft/v3.v:3293;
`raft.go:726`):

    r.trk.Visit(func(id uint64, _ *tracker.Progress) {
      if id == r.id { return }
      r.sendHeartbeat(id, ctx)
    })

One heartbeat per peer other than the leader itself, each with
`Commit = min(Match, committed)` (`Spec/raft__sendHeartbeat.lean`). The postcondition
is what the model's `Step.beat` asks of the broadcast: every message sent is one
`HeartbeatOk` allows at the protocol reading of the state the call started in.
`HeartbeatOk` bounds `Commit` by `matchOf`, i.e. by `toPState`'s `matched`, which is
the `Progress` `Match` values only for a leader -- hence the premise
`s.role = .leader`. That the list has exactly one heartbeat per peer is true but not
stated: the model does not need it. `SentCommit` moves no `Match`. Each carries the
context's list `cl` (2026-10-12). -/
abbrev raft.bcastHeartbeatWithCtx.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (ctx : GoSlice) (cl : List w8),
  s.role = .leader →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "#Hctx" ∷ ctx ↦*□ cl }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"bcastHeartbeatWithCtx"))
      (Val #ctx))
  {{ (ms : List Msg) (pvs : GMap w64 Progress), RET #();
      ownRaftPhys cfg r id { sendMsgs s ms with prvals := pvs } ∗
      ⌜∀ m ∈ ms, HeartbeatOk id (toPState s) m ∧ m.ctx = cl⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

end spec

end EtcdGrove
end Perennial
