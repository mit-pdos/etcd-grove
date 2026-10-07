/-
Port of `election_proof/inv_readylog.v` (at 857d09190).

**What `Ready`/`Advance` need of the log (2026-10-05)**

Pure functions of `LogState` -- the next unstable entries, the committed entries to
apply, `acceptUnstable`, `stableTo`, `appliedTo` -- and the facts about the persistence
invariant they need. In a file of their own, below `Spec/raft__Step.lean` (whose
`MsgStorageAppendResp` premise is `StableOk`) and apart from `InvRawnode.lean`, so that
an edit to the `RawNode` predicate does not rebuild `Step`'s proof; and not in
`Defs.lean`/`InvRaftlog.lean`, whose every edit rebuilds the whole cone.

Lean notes: `log_offset`, `log_end`, `next_unstable`, `log_accept_unstable`,
`log_committed_ents`, `log_accept_applying`, `log_applied_to`, `log_stable_to` are
`logOffset`, `logEnd`, `nextUnstable`, `logAcceptUnstable`, `logCommittedEnts`,
`logAcceptApplying`, `logAppliedTo`, `logStableTo`; the Prop-valued `stable_hit`,
`stable_ok` are `StableHit`, `StableOk`. stdpp's `list.last` is `List.getLast?`.
`to_pstate_log_stable_to`, `to_pstate_log_applied_to`, `own_tracker_autoleave` are
`toPState_logStableTo`, `toPState_logAppliedTo`, `ownTracker_autoleave`.
-/
import EtcdGrove.Raft.InvRaftPhys

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

def MsgStorageApplyResp : w32 := W32 22
def LocalAppendThread : w64 := W64 18446744073709551615
def LocalApplyThread : w64 := W64 18446744073709551614

/-! ## The log, as `Ready` and `Advance` see it -/

section readylog
variable [FfiSyntax]

/-- `unstable.offset`, which `ownRaftLog` pins to the end of the stable part
(`Hoffset`). -/
def logOffset (ls : LogState) : Int :=
  uint.Z ls.prev.index' + (ls.sents.length : Int) + 1

/-- One past the last index. -/
def logEnd (ls : LogState) : w64 := logLast ls + W64 1

/-- `nextUnstableEnts()`: the unstable entries not yet handed out by a `Ready`
(`u.entries[offsetInProgress-offset:]`). -/
def nextUnstable (ls : LogState) : List raftpb.Entry :=
  ls.uents.drop (uint.Z ls.inprogress - logOffset ls).toNat

/-- `acceptUnstable()`: every unstable entry is in progress (`offsetInProgress` at the
end), and the ones just handed out are now the application's to persist
(`LogState.unpersisted`). -/
def logAcceptUnstable (ls : LogState) : LogState :=
  { ls with inprogress := logEnd ls, unpersisted := nextUnstable ls }

/-- The committed entries not yet handed out for applying: `(applying, committed]` --
what `nextCommittedEnts(true)` slices, before `maxSize` cuts it short. -/
def logCommittedEnts (ls : LogState) : List raftpb.Entry :=
  (plogFrom ls.prev (ls.sents ++ ls.uents) (ls.applying + W64 1)).take
    (uint.Z ls.committed - uint.Z ls.applying).toNat

/-- `acceptApplying` after a `Ready` that handed out `ce`: `applying` moves to `ce`'s
last index and the applying budget grows by `sz` (`entsSize(ce)`, whose value no spec
pins); nothing changes for an empty `ce`, which `acceptReady` does not accept. -/
def logAcceptApplying (ls : LogState) (ce : List raftpb.Entry) (sz : w64) : LogState :=
  match ce.getLast? with
  | some e => { ls with applying := e.Index', apsize := ls.apsize + sz }
  | none => ls

/-- `raft.appliedTo(index, size)`: `applied` moves to `max(index, applied)`
(`raftLog.appliedTo` then moves `applying` up to it and releases `size` of the applying
budget). -/
def logAppliedTo (ls : LogState) (index size : w64) : LogState :=
  let na := w64Max index ls.applied
  { ls with applied := na,
            applying := w64Max ls.applying na,
            apsize := if uint.Z size < uint.Z ls.apsize then ls.apsize - size else W64 0 }

/-- When `unstable.stableTo(id)` moves entries stable: `id` is an index of the unstable
suffix (`offset ≤ index ≤ last`) whose term there is `id.term`; otherwise it logs and
returns. -/
def StableHit (ls : LogState) (id : entryID) : Prop :=
  (logOffset ls ≤ uint.Z id.index' ∧
   uint.Z id.index' ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
     + (ls.uents.length : Int)) ∧
  plogTermAt ls.prev (ls.sents ++ ls.uents) id.index' = some id.term'

instance StableHit.decidable (ls : LogState) (id : entryID) : Decidable (StableHit ls id) := by
  unfold StableHit; infer_instance

/-- `stableTo(id)`: on a hit, the entries up to `id.index` move from the unstable
suffix to the stable part, and `offsetInProgress` is at least the new offset. The
protocol log (`sents ++ uents`) does not change. -/
def logStableTo (ls : LogState) (id : entryID) : LogState :=
  if StableHit ls id then
    let k := (uint.Z id.index' + 1 - logOffset ls).toNat
    { ls with sents := ls.sents ++ ls.uents.take k,
              uents := ls.uents.drop k,
              inprogress := w64Max ls.inprogress (id.index' + W64 1) }
  else ls

/-- What makes a `stableTo(id)` that hits correct: the entries it moves stable are
persisted -- they are in progress (`id.index < offsetInProgress`) and the application
has appended what it was handed (`unpersisted = []`) -- and no snapshot is pending (the
stable part is then empty, `LogStoreOk`). Not checkable by Go, which compares only the
term at `id.index`: an entry handed out, then truncated away by a conflicting `MsgApp`,
then replaced by one *of the same term* would be moved stable unpersisted. The protocol
rules that out (Log Matching); it is a premise here, discharged by whoever knows the log
was not truncated below `id` since the `Ready` that handed it out. -/
def StableOk (ls : LogState) (id : entryID) : Prop :=
  StableHit ls id →
  ls.snap = none ∧
  uint.Z id.index' < uint.Z ls.inprogress ∧
  ls.unpersisted = []

/-- The persistence invariant (`LogPersistOk`, `InvRaftlog.lean`) across
`acceptUnstable`: with nothing unpersisted, handing out the rest of the unstable suffix
makes all of it in progress, and once the application appends what was handed out the
storage holds exactly the log (`storApp` cuts the storage at the first handed-out
index, which the indices put right after the in-progress prefix). -/
theorem persist_accept (prev sprev : entryID) (stored sents uents : List raftpb.Entry)
    (ipo : Int)
    (Hidx : LogIndicesOk prev (sents ++ uents))
    (Hsp : sprev = prev)
    (Hipo : 0 ≤ ipo ∧ ipo ≤ (uents.length : Int))
    (H : LogPersistOk sprev stored sents uents ipo []) :
    LogPersistOk sprev stored sents uents (uents.length : Int) (uents.drop ipo.toNat) := by
  subst sprev
  obtain ⟨Hpre, Heq, _⟩ := H
  simp only [storApp] at Hpre Heq
  unfold LogPersistOk
  rw [Int.toNat_natCast, List.take_of_length_le (Nat.le_refl _)]
  cases Hdrop : uents.drop ipo.toNat with
  | nil =>
    have Hall : ipo.toNat = uents.length := by
      have := congrArg List.length Hdrop
      simp only [List.length_drop, List.length_nil] at this
      omega
    have Hs := Heq Hall
    simp only [storApp]
    exact ⟨Hs ▸ List.prefix_refl _, fun _ => Hs, by simp⟩
  | cons e0 rest =>
    have Hlk : uents[ipo.toNat]? = some e0 := by
      have := congrArg (fun l => l[0]?) Hdrop
      simpa [List.getElem?_drop] using this
    have Hlk' : (sents ++ uents)[sents.length + ipo.toNat]? = some e0 := by
      rw [List.getElem?_append_right (by omega)]
      simpa using Hlk
    have He0 := Hidx _ _ Hlk'
    have Hlen : ipo.toNat ≤ uents.length := by omega
    obtain ⟨k, Hk⟩ := Hpre
    have Hst : storApp prev stored (e0 :: rest) = sents ++ uents := by
      simp only [storApp]
      rw [← Hk,
        show (uint.Z e0.Index' - uint.Z prev.index' - 1).toNat
          = (sents ++ uents.take ipo.toNat).length by
          simp only [List.length_append, List.length_take]; omega,
        List.take_left, ← Hdrop, List.append_assoc, List.take_append_drop]
    rw [Hst]
    refine ⟨List.prefix_refl _, fun _ => rfl, ?_⟩
    intro Hu
    subst Hu
    simp at Hdrop

/-- ... and across `stableTo` of `k` entries that are in progress: the stable part
grows by them, the in-progress part of the suffix shrinks by them, the storage is
unchanged. -/
theorem persist_stable (sprev : entryID) (stored sents uents : List raftpb.Entry)
    (ipo k : Int)
    (Hk : 0 ≤ k ∧ k ≤ ipo ∧ ipo ≤ (uents.length : Int))
    (H : LogPersistOk sprev stored sents uents ipo []) :
    LogPersistOk sprev stored (sents ++ uents.take k.toNat) (uents.drop k.toNat)
      (ipo - k) [] := by
  obtain ⟨Hpre, Heq, _⟩ := H
  simp only [LogPersistOk, storApp] at Hpre Heq ⊢
  have Hsplit : uents.take k.toNat ++ (uents.drop k.toNat).take (ipo - k).toNat
      = uents.take ipo.toNat := by
    rw [← List.take_add, show k.toNat + (ipo - k).toNat = ipo.toNat by omega]
  refine ⟨?_, ?_, fun _ => trivial⟩
  · rw [List.append_assoc, Hsplit]; exact Hpre
  · intro Hfull
    rw [List.length_drop] at Hfull
    rw [List.append_assoc, List.take_append_drop]
    exact Heq (by omega)

/-- `stableTo` and `appliedTo` are invisible to the protocol: the protocol log is
`sents ++ uents`, which `stableTo` only re-splits, and `applied`/`applying`/the applying
budget are not protocol state. -/
theorem toPState_logStableTo (s : NState) (id : entryID) :
    toPState { s with logst := logStableTo s.logst id } = toPState s := by
  unfold logStableTo
  split
  · simp only [toPState, List.append_assoc, List.take_append_drop]
  · rfl

theorem toPState_logAppliedTo (s : NState) (index size : w64) :
    toPState { s with logst := logAppliedTo s.logst index size } = toPState s := rfl

end readylog

section tracker
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable (cfg : GSet w64)

/-- The tracker's configuration is not a joint one on its way out (`ownTracker`'s
`Hautoleave`), read without consuming the tracker: `raft.appliedTo`'s auto-leave branch
is dead. -/
theorem ownTracker_autoleave (tv : tracker.ProgressTracker) (t : Trk) :
    ⊢ ownTracker (GF := GF) cfg tv t -∗
      ⌜tv.Config'.AutoLeave' = false⌝ ∗
      ownTracker cfg tv t := by
  iintro Hown
  iunfold ownTracker at Hown
  icases Hown with ⟨%voters_ref, %voters, %learners, %learnersNext, Hown⟩
  iNamed Hown
  isplitr
  · ipureintro; exact Hautoleave
  iapply ownTracker_intro cfg tv t.votes t.prs t.peers voters_ref voters learners learnersNext
    Hprs_dom Hvoters_arr Hautoleave Hvoters_dom Hno_learners Hcfg_size HmaxInfl
    $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext

end tracker

end EtcdGrove
end Perennial
