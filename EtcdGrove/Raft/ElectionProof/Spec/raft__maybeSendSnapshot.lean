/- Port of election_proof/spec_raft__maybeSendSnapshot.v. -/
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

/-- `r.maybeSendSnapshot(to, pr)` -- the fallback when the log no longer has what a peer
needs (`raft.maybeSendSnapshot.impl`, `Perennial/Code/go_etcd_io/raft/v3.lean`).

    if !pr.RecentActive        { Debugf; return false }
    snapshot, err := r.raftLog.snapshot()
    if err == ErrSnapshotTemporarilyUnavailable { Debugf; return false }
    if err != nil              { panic(err) }
    if IsEmptySnap(snapshot)   { panic("need non-empty snapshot") }
    Debugf; pr.BecomeSnapshot(sindex); Debugf
    r.send(pb.Message{To: to, Type: MsgSnap, Snapshot: snapshot})
    return true

**The model sees nothing.** `MsgSnap` has no `mtypeOf`, so it falls under the third
clause of `send_ok` (`Spec/raft__send.lean`) and contributes nothing to the abstract
outbox -- which is why the postcondition is at the *same* `s`. `Term` is unset in the
literal and `to ≠ id` (the only caller, `maybeSendAppend`, is reached from
`bcastAppend`, which skips the leader itself), so that clause applies.

`pr` moves to `StateSnapshot`, which is why the `Progress` comes back existentially
quantified rather than at its old value.

**Resources.** The struct arrives whole, as `ownRaftPhys`, and `pr` is *named* rather
than owned: it is the peer's `Progress` in the progress map `s.progress`, and the proof
borrows it out of the tracker itself and puts it back before the `send`. From
2026-09-21 to 2026-09-22 this was stated on a variant predicate, `own_raft_notrk` -- the
struct with the tracker cut out -- plus `own_progress pr`, because
`ownRaftPhys cfg r id s ∗ own_progress pr` is contradictory at the only call site (the
`Progress` is already inside `ownTracker`; notes/false-statements.md, 2026-09-21).
Recording the progress map in `NState` removes the need for the variant: the caller
hands `pr` back to the tracker before the call and borrows it again after, at the same
key.

Reaching `Storage.Snapshot` is what forced the `HSnapshot` triple into `isStorage`
(`InvStorage.lean`). This branch is genuinely reachable from `ownRaftPhys`: nothing in
`ownProgress` bounds `pr.Next` against the log, so `r.raftLog.term(pr.Next-1)` may
legitimately return `ErrCompacted`. -/
abbrev raft.maybeSendSnapshot.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (to : w64) (pr : Loc),
  to ≠ id →
  s.progress !! to = some pr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"maybeSendSnapshot"))
      (Val #to)) (Val #pr))
  {{ (b : Bool) (pvs : GMap w64 (tracker.Progress × tracker.Inflights)), RET #b;
      ownRaftPhys cfg r id { s with prvals := pvs } }}

end spec

end EtcdGrove
end Perennial
