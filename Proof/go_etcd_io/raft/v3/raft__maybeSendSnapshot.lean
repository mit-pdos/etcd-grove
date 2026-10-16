/-
Port of election_proof/proof_raft__maybeSendSnapshot.v.

raft v3.7 (stage R4): `raftLog.snapshot` returns a fresh clone, owned (`ownSnapM snap 1 sv`); its
index and term are read through `GetMetadata().GetIndex()/GetTerm()`, `IsEmptySnap` takes it as
`snapOpt`, and the message `&pb.Message{To: new(to), Type: MsgSnap.Enum(), Snapshot: snapshot}`
owns it (`msgOwn_of_struct`); `send`'s `SnapOut` is the snapshot at its own conf-state lists.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__maybeSendSnapshot
public import Spec.go_etcd_io.raft.v3.raftLog__snapshot
public import Spec.go_etcd_io.raft.v3.raftLog__firstIndex
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.tracker.Progress__BecomeSnapshot
public import Spec.go_etcd_io.raft.v3.raft__send
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasSendR

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
    ⊢ ownRaftPhysCV (GF := GF) c c.voters r id { s with prvals := s.prvals } -∗
      ownRaftPhysCV c c.voters r id { sendMsgs s [] with prvals := s.prvals } := by
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
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (wp_Snapshot_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_SnapshotMetadata_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_SnapshotMetadata_GetTerm : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
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
  ihave Hphys : ownRaftPhysCV (GF := GF) c c.voters r id { s with prvals := s.prvals } $$ [Hphys]
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
  -- (stage R8a) the commit index is within the log: `BecomeSnapshot`'s index is at most it
  icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hcmb, Hlog⟩
  ihave Hphys := Hlogback $$ Hlog
  icases Herr with (%Herr | ⟨%Herr, %sv, Hsnap, %Hsv⟩)
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
    obtain ⟨Hnz, Hsle, Hsterm, Hksn⟩ := Hsv
    subst Herr
    wp_auto
    wp_apply wp_IsEmptySnap snap (DFrac.own 1) (some sv) $$ [Hsnap] as %b ⟨%Hb, Hsnap⟩
    · simp only [named, snapOpt]; iexact Hsnap
    simp only [snapOpt] at *
    subst Hb
    simp only [Option.elim, Hnz, _root_.decide_false]
    wp_auto
    wp_apply wp_Snapshot_GetMetadata.1 snap _ sv $$ [$Hsnap] as %pm ⟨Hm, Hsback⟩
    wp_apply wp_SnapshotMetadata_GetIndex pm _ _ $$ [$Hm] as Hm
    ispecialize Hsback $$ Hm
    try wp_auto
    wp_apply wp_Snapshot_GetMetadata.1 snap _ sv $$ [$Hsback] as %pm ⟨Hm, Hsback⟩
    wp_apply wp_SnapshotMetadata_GetTerm pm _ _ $$ [$Hm] as Hm
    ispecialize Hsback $$ Hm
    try wp_auto
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
    icases ownRaftPhysC_pr_upd c r id s to pr pp $$ Hphys %Hprto %Hpl with ⟨%Hok, %Hnw, Hpr, Hback⟩
    wp_apply wp_Progress_BecomeSnapshot $$ [$Hpr] as Hpr
    ihave Hphys := Hback $$ %(progressBecomeSnapshot pp sv.Metadata'.Index') Hpr %rfl
      %(fun Hl => (Hok Hl).becomeSnapshot Hnw (by
          obtain ⟨⟨-, -, Hcle⟩, -⟩ := Hcmb
          rw [Hnw.logLast_Z]; omega))
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_raft_logC
    -- `&pb.Message{To: new(to), Type: pb.MsgSnap.Enum(), Snapshot: snapshot}`: the message owns
    -- the fresh clone `raftLog.snapshot` returned (stage R4)
    rw [show raftpb.MsgSnap = #((W32 7 : raftpb.MessageType)) from rfl]
    haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
    wp_apply wp_MessageType_Enum (W32 7)
    iintro %pty Hpty
    imod cellRO_alloc $$ Hpty with #cTy
    imod cellRO_alloc $$ «$v0» with #cTo
    wp_auto
    ihave Hnil : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod ownSlice_persist $$ Hnil with #Hnil
    ihave Hnilb : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod ownSlice_persist $$ Hnilb with #Hnilb
    ihave Hnilr : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
    · iapply ownSlice_nil
    let mm : MessageM := ⟨W32 7, to, 0, 0, 0, 0, 0, 0, false, 0⟩
    imod msgOwn_of_struct «$a0_ptr»
      { state' := zeroValDef, Type' := pty, To' := «$v0_ptr», From' := null, Term' := null,
        LogTerm' := null, Index' := null, Entries' := slice.nil, Commit' := null, Vote' := null,
        Snapshot' := snap, Reject' := null, RejectHint' := null, Context' := slice.nil,
        Responses' := slice.nil, unknownFields' := slice.nil, sizeCache' := 0 }
      [] ⟨mm, [], some sv, [], []⟩ ⊤ rfl
      $$ [«$a0» Hsback Hnilr] with Hm
    · iframe «$a0» cTy cTo Hnil Hnilb Hnilr
      simp only [snapOpt]
      iframe Hsback
      msg_nulls
      iapply BigSepL2.bigSepL2_nil.2; itrivial
    have Hok : SendOk id { s with prvals := <[to := progressBecomeSnapshot pp sv.Metadata'.Index']> s.prvals }
        mm [] [] [absSnapFrom mm id s.term sv sv.Metadata'.ConfState'.lists] :=
      Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl, Hto⟩)))
    wp_apply wp_raft_send c r id _ «$a0_ptr» mm [] (some sv) [] []
        [absSnapFrom mm id s.term sv sv.Metadata'.ConfState'.lists] (Or.inl rfl) Hok
        (fun _ => ⟨sv, rfl, rfl⟩) $$ [$Hphys $Hm] as Hphys
    iapply HΦ $$ %true %([absSnapFrom mm id s.term sv sv.Metadata'.ConfState'.lists] : List Msg)
      %(<[to := progressBecomeSnapshot pp sv.Metadata'.Index']> s.prvals)
    isplitl [Hphys]
    · iapply ownRaftPhysC_eq c r id _ _ (by cases s; rfl) $$ Hphys
    ipureintro
    constructor
    · -- `SnapOk`: the snapshot's index is non-zero, at or below the
      -- commit index, and an entry id of the log (`raftLog.snapshot`)
      intro m' Hm'
      rw [List.mem_singleton] at Hm'
      subst Hm'
      refine ⟨?_, fun h => absurd h (by simp [absSnapFrom])⟩
      right
      exact ⟨rfl, rfl, rfl, Hto, Hnz, Hsle, Hsterm⟩
    · exact prvalsMatch_insert_same _ _ pp _ Hpl rfl

end proof

end EtcdGrove
end Perennial
