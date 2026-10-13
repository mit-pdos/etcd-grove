/-
Port of election_proof/proof_raft__maybeSendSnapshot.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__maybeSendSnapshot
public import Spec.go_etcd_io.raft.v3.raftLog__snapshot
public import Spec.go_etcd_io.raft.v3.raftLog__firstIndex
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.tracker.Progress__BecomeSnapshot
public import Spec.go_etcd_io.raft.v3.raft__send

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Returning without sending: the state the caller expects. -/
private theorem ownRaftPhys_nosend (c : CfgM) (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysC (GF := GF) c r id { s with prvals := s.prvals } -∗
      ownRaftPhysC c r id { sendMsgs s [] with prvals := s.prvals } := by
  iintro H
  iapply ownRaftPhysC_eq c r id _ _ (by cases s; simp [sendMsgs]) $$ H

/-- Three exits, and the two `panic`s are both killed by `isStorage`'s
`HSnapshot` (`InvStorage.lean`), whose postcondition is the disjunction
"`ErrSnapshotTemporarilyUnavailable`, or a snapshot with
`Metadata.Index ≠ 0`":

- `!pr.RecentActive`: log, `false`. Nothing is touched.
- `err = ErrSnapshotTemporarilyUnavailable`: log, `false`. This is
  where the `panic(err)` below would be, and the disjunction says the
  error is either this one or `nil`.
- otherwise the snapshot is non-empty, so `IsEmptySnap` answers
  `false` and the `panic("need non-empty snapshot")` is dead; the
  `MsgSnap` goes out and the answer is `true`.

**Comparing two non-`nil` errors is not free.** `err ==
ErrSnapshotTemporarilyUnavailable` does not reduce to a
`decide`: Goose's interface equality first runs `CheckComparable`
on the dynamic type, which has no reduction for an unknown type, so
the proof is *stuck* until it knows the error's representation. That
is what `Base.lean`'s `IsNewError` clause on
`ErrSnapshotTemporarilyUnavailable` supplies -- an interface holding a
pointer, which is what `errors.New` builds. `raftLog.slice`
compares against `ErrCompacted`/`ErrUnavailable` and does not need it
only because there the error is `interface.nil`, which the
`nil`/`ok` case answers outright.

The `send` is `SendOk`'s `MsgSnap` clause (c'): `Term` is unset in
the literal and `To = to ≠ id` (the premise; the caller chain
`bcastAppend` -> `maybeSendAppend` skips the leader itself). The
outbox grows by `absSnapFrom` of the snapshot `raftLog.snapshot`
returned, which `SnapOk` accepts because its index is non-zero.
(This paragraph described `SendOk`'s third clause, with the
outbox unchanged, until 2026-10-01.)

**Resources.** The struct arrives as `ownRaftPhys`, and stays
whole except around the two accesses to `*pr`: the
`pr.RecentActive` load and `pr.BecomeSnapshot`. Each borrows `pr`
out of the tracker by its key (`ownTrackerC_lookup_same`, resp.
`ownRaftPhysC_pr_upd`; the premise puts it at `to` in `s.progress`) and gives it back at
once -- the first at the same value, the second at whatever
`BecomeSnapshot` leaves, which the postcondition's `pvs` records.
In between, the log lines read raft fields and the `raftLog` calls
take the log out with `ownRaftPhysC_log_same`. (Until 2026-09-29
the tracker was lent out of the struct for the whole body,
`nstate.lent`.) -/
theorem raft.maybeSendSnapshot.wp_proof
    (wp_raftLog_snapshot : raftLog.snapshot.spec (GF := GF) (hG := hG))
    (wp_raftLog_firstIndex : raftLog.firstIndex.spec (GF := GF) (hG := hG))
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG))
    (wp_Progress_BecomeSnapshot : tracker.Progress.BecomeSnapshot.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG)) :
    raft.maybeSendSnapshot.spec (GF := GF) (hG := hG) := by
  intro c r id s to pr Hto Hprto
  wp_start as H
  iNamed H
  -- `isInitialized_access` hands the globals out; the `raftLog.snapshot` call below
  -- consumes `ErrSnapUnavail`'s points-to, and the
  -- `err == ErrSnapshotTemporarilyUnavailable` test afterwards needs it again: it is
  -- persistent, and `iNamed` puts it in the intuitionistic context.
  ihave Hinit := isInitialized_access $$ Hpkg
  unfold isInitialized
  iNamed Hinit
  -- `pr.RecentActive`: borrow `pr` for the load, and give it back
  icases ownRaftPhysC_tracker_same c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTrackerC_lookup_same c tv ⟨s.votes, s.progress, s.prvals⟩ to pr Hprto $$ Htrk
    with ⟨%pp, %Hpl, Hpr, Htrkback⟩
  iunfold ownProgress at Hpr
  iNamed Hpr
  wp_auto
  ihave Hpr : ownProgress (GF := GF) pr pp $$ [Hpv Hinfl]
  · unfold ownProgress
    iexists pv
    iframe Hpv Hinfl
    ipureintro; exact Habs
  ihave Htrk := Htrkback $$ Hpr
  ihave Hphys := Hback $$ %tv Htrkf Htrk
  -- nothing below writes a `Progress` until `BecomeSnapshot`
  ihave Hphys : ownRaftPhysC (GF := GF) c r id { s with prvals := s.prvals } $$ [Hphys]
  · iapply ownRaftPhysC_eq c r id _ _ (by cases s; rfl) $$ Hphys
  cases Hra : pv.RecentActive' <;> wp_auto
  · -- not recently active: log and return `false`
    wp_raft_logC
    iapply HΦ $$ %false %([] : List Msg) %s.prvals
    isplitl [Hphys]
    · iapply ownRaftPhys_nosend $$ Hphys
    ipureintro
    exact ⟨fun _ h => (nomatch h), rfl⟩
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
  wp_apply wp_raftLog_snapshot _ _ _ $$ [$Hlog $ErrSnapUnavail] as %snap %err ⟨Hlog, Herr⟩
  ihave Hphys := Hlogback $$ Hlog
  icases Herr with (%Herr | ⟨%Herr, %voters, #Hvoters⟩)
  · -- `ErrSnapshotTemporarilyUnavailable`: log and return `false`. The
    -- `panic(err)` that follows the inner `if` is never reached.
    subst Herr
    obtain ⟨t, p, rfl⟩ := HErrSnapUnavail_new
    wp_auto
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_raft_logC
    iapply HΦ $$ %false %([] : List Msg) %s.prvals
    isplitl [Hphys]
    · iapply ownRaftPhys_nosend $$ Hphys
    ipureintro
    exact ⟨fun _ h => (nomatch h), rfl⟩
  · -- a real snapshot: `Metadata.Index ≠ 0` kills `IsEmptySnap`'s panic
    obtain ⟨rfl, Hnz, Hsle, Hsterm⟩ := Herr
    wp_auto
    wp_apply wp_IsEmptySnap as %b %Hb
    subst Hb
    simp only [Hnz, decide_false]
    wp_auto
    -- the third `Debugf`'s argument list calls `firstIndex` and then
    -- reads `r.raftLog.committed` directly: the log's struct, for the
    -- read
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
    wp_apply wp_raftLog_firstIndex _ _ $$ [$Hlog] as %fi ⟨Hlog, %Hfi⟩
    ihave Hphys := Hlogback $$ Hlog
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, -, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    wp_raft_logC
    -- `pr.BecomeSnapshot(sindex)`: borrow `pr` again, give it back at
    -- the new value
    icases ownRaftPhysC_pr_upd c r id s to pr pp $$ Hphys %Hprto %Hpl with ⟨Hpr, Hback⟩
    wp_apply wp_Progress_BecomeSnapshot $$ [$Hpr] as Hpr
    ihave Hphys := Hback $$ %(progressBecomeSnapshot pp snap.Metadata'.Index') Hpr %rfl
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_raft_logC
    -- `send_ok`'s `MsgSnap` clause, with no entries. `Snapshot:
    -- &snapshot` queues the address of the local variable, which nothing
    -- writes again: persist it, and the abstract message is the
    -- snapshot `raftLog.snapshot` returned, with the voters it handed
    -- out (`msgAbs`, `InvRaftPhys.lean`).
    ipersist snapshot
    let m : raftpb.Message :=
      { Type' := W32 7, To' := to, From' := 0, Term' := 0, LogTerm' := 0, Index' := 0,
        Entries' := slice.nil, Commit' := 0, Vote' := 0, Snapshot' := snapshot_ptr,
        Reject' := false, RejectHint' := 0, Context' := slice.nil, Responses' := slice.nil }
    wp_apply wp_raft_send c r id _ m [] [] [absSnapFrom m id s.term snap voters] ?_ ?_
      $$ [$Hphys]
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl, Hto⟩)))
    · isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSlice_nil
      imodintro
      iintro _
      iexists snap, voters
      iframe # 
      ipureintro; rfl
    iintro Hphys
    wp_auto
    iapply HΦ $$ %true %([absSnapFrom m id s.term snap voters] : List Msg)
      %(<[to := progressBecomeSnapshot pp snap.Metadata'.Index']> s.prvals)
    isplitl [Hphys]
    · iapply ownRaftPhysC_eq c r id _ _ (by cases s; rfl) $$ Hphys
    ipureintro
    constructor
    · -- `SnapOk`: the snapshot's index is non-zero, at or below the
      -- commit index, and an entry id of the log (`raftLog.snapshot`)
      intro m' Hm'
      rw [List.mem_singleton] at Hm'
      subst Hm'
      right
      exact ⟨rfl, rfl, rfl, Hto, Hnz, Hsle, Hsterm⟩
    · exact prvalsMatch_insert_same _ _ pp _ Hpl rfl

end proof

end EtcdGrove
end Perennial
