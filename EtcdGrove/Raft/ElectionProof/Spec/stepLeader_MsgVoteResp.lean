/-
Port of `election_proof/spec_stepLeader_MsgVoteResp.v`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `stepLeader` on a `MsgVoteResp`: nothing observable.

`stepLeader.impl` (`Perennial/Code/go_etcd_io/raft/v3.lean`) is *two* type switches
with a progress-map lookup in between:

    switch m.Type {                 // MsgBeat, MsgCheckQuorum, MsgProp,
    ...                             // MsgReadIndex, MsgForgetLeader
    }
    pr := r.trk.Progress[m.From]
    if pr == nil {
        r.logger.Debugf("%x no progress available for %x", r.id, m.From)
        return nil
    }
    switch m.Type {                 // MsgAppResp, MsgHeartbeatResp,
    ...                             // MsgSnapStatus, MsgUnreachable,
    }                               // MsgTransferLeader
    return nil

`MsgVoteResp` appears in neither switch, so it falls off the end of both. The code in
between reads `r.trk.Progress`, `r.id` and `r.logger` and may log, but it writes
nothing, so the raft struct -- outbox included -- is left exactly as it was.

Hence the same trivial postcondition as `stepFollower`'s: state unchanged, `nil`
error. Note in particular that no `m.From ∈ cfg` premise is needed: the lookup's result
is only compared against `nil`, and *both* outcomes return `nil` without touching the
state, so the proof never has to know whether the sender is a voter.

The lookup reads the progress map, which is owned by the tracker. (Until 2026-09-23
`ownRaftPhys` held a second copy of the map's points-to outside the tracker, and this
spec read that; until 2026-09-29 it needed the tracker not to be on loan,
`nstate.lent`.) -/
abbrev stepLeader_MsgVoteResp.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message),
  m.Type' = MsgVoteResp →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #m))
  {{ (err : GoInterface), RET #err;
      ownRaftPhys cfg r id s ∗ ⌜err = interface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
