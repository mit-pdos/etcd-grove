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
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

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

/-- One past the last index. -/
def logEnd (ls : LogState) : w64 := logLast ls + W64 1

/-- `acceptUnstable()`: every unstable entry is in progress (`offsetInProgress` at the
end), and the ones just handed out are now the application's to persist
(`LogState.unpersisted`); once it has, the storage holds the whole log (`stored`,
2026-10-10). -/
def logAcceptUnstable (ls : LogState) : LogState :=
  { ls with inprogress := logEnd ls, unpersisted := nextUnstable ls,
            stored := ls.sents ++ ls.uents }

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
persisted -- the application has appended what it was handed (`unpersisted = []`) and
the storage then holds exactly the log up to `id` (`stored`, 2026-10-10) -- and no
snapshot is pending (the stable part is then empty, `LogStoreOk`). Not checkable by
Go, which compares only the term at `id.index`. Until 2026-10-10 the second fact was
`id.index < offsetInProgress` (the entries are in progress), which a `MsgApp` between
the `Ready` and the `Advance` breaks: it truncates the log at or below `id.index`
(`offsetInProgress` moves back to the truncation), and a later one, from the leader of
a higher term, puts the very entry `id` back -- the acknowledgement then hits with
`id.index ≥ offsetInProgress`, and is still right, because the storage (which holds
the log of the `Ready`, up to `id`) agrees with the log up to `id` by Log Matching.
The `RawNode` discharges it so (`stored_agree`, `InvRawnode.lean`). -/
def StableOk (ls : LogState) (id : entryID) : Prop :=
  StableHit ls id →
  ls.snap = none ∧
  ls.unpersisted = [] ∧
  ls.stored = (ls.sents ++ ls.uents).take (uint.Z id.index' - uint.Z ls.prev.index').toNat

/-! What `acceptApplying` and `stableTo` leave alone (2026-10-09): the fields the
`RawNode` predicate (`InvRawnode.lean`) states its facts on. Both functions branch, so
`proj_simps` does not apply. -/

theorem logAcceptApplying_fields (ls : LogState) (ce : List raftpb.Entry) (sz : w64) :
    (logAcceptApplying ls ce sz).committed = ls.committed ∧
    (logAcceptApplying ls ce sz).inprogress = ls.inprogress ∧
    (logAcceptApplying ls ce sz).unpersisted = ls.unpersisted ∧
    (logAcceptApplying ls ce sz).snap = ls.snap ∧
    (logAcceptApplying ls ce sz).prev = ls.prev ∧
    (logAcceptApplying ls ce sz).stored = ls.stored := by
  unfold logAcceptApplying; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Neither changes the storage (2026-10-10). -/
theorem logAcceptApplying_storage (ls : LogState) (ce : List raftpb.Entry) (sz : w64) :
    (logAcceptApplying ls ce sz).storage = ls.storage := by
  unfold logAcceptApplying; split <;> rfl

theorem logStableTo_storage (ls : LogState) (id : entryID) :
    (logStableTo ls id).storage = ls.storage := by
  unfold logStableTo; split <;> rfl

theorem logAcceptApplying_applying (ls : LogState) (ce : List raftpb.Entry) (sz : w64)
    (e : raftpb.Entry) (He : ce.getLast? = some e) :
    (logAcceptApplying ls ce sz).applying = e.Index' := by
  unfold logAcceptApplying; rw [He]

theorem logStableTo_fields (ls : LogState) (id : entryID) :
    (logStableTo ls id).applying = ls.applying ∧
    (logStableTo ls id).unpersisted = ls.unpersisted ∧
    (logStableTo ls id).snap = ls.snap ∧
    uint.Z ls.inprogress ≤ uint.Z (logStableTo ls id).inprogress ∧
    (logStableTo ls id).prev = ls.prev ∧
    (logStableTo ls id).stored = ls.stored := by
  unfold logStableTo
  split
  · refine ⟨rfl, rfl, rfl, ?_, rfl, rfl⟩
    simp only [w64Max_spec]; omega
  · exact ⟨rfl, rfl, rfl, Int.le_refl _, rfl, rfl⟩

/-- The persistence invariant (`LogPersistOk`, `InvRaftlog.lean`) across
`acceptUnstable`: with nothing unpersisted, handing out the rest of the unstable suffix
makes all of it in progress, and once the application appends what was handed out the
storage holds exactly the log (`storApp` cuts the storage at the first handed-out
index, which the indices put right after the in-progress prefix). -/
theorem persist_accept (prev : entryID) (σ : StorState) (sents uents : List raftpb.Entry)
    (ipo : Int)
    (Hidx : LogIndicesOk prev (sents ++ uents))
    (Hsp : σ.prev = prev)
    (Hipo : 0 ≤ ipo ∧ ipo ≤ (uents.length : Int))
    (st : List raftpb.Entry)
    (H : LogPersistOk σ sents uents ipo [] st) :
    LogPersistOk σ sents uents (uents.length : Int) (uents.drop ipo.toNat)
      (sents ++ uents) := by
  subst prev
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
    exact ⟨Hs ▸ List.prefix_refl _, fun _ => Hs, by simp, Hs.symm⟩
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
    have Hst : storApp σ (e0 :: rest) = sents ++ uents := by
      simp only [storApp]
      rw [← Hk,
        show (uint.Z e0.Index' - uint.Z σ.prev.index' - 1).toNat
          = (sents ++ uents.take ipo.toNat).length by
          simp only [List.length_append, List.length_take]; omega,
        List.take_left, ← Hdrop, List.append_assoc, List.take_append_drop]
    rw [Hst]
    refine ⟨List.prefix_refl _, fun _ => rfl, ?_, rfl⟩
    intro Hu
    subst Hu
    simp at Hdrop

/-- ... and across `stableTo` of `k` entries: the stable part grows by them, the
in-progress part of the suffix is what is left of it (`max ipo k - k`), the storage is
unchanged. The `k` entries are in progress (`k ≤ ipo`) or (2026-10-10) the storage
holds exactly the log up to them (`Hst`); either way, once the suffix is empty, the
stable part is what the storage holds (the second conjunct, `LogStoreOk`'s). -/
theorem persist_stable (σ : StorState) (sents uents stored : List raftpb.Entry)
    (ipo k : Int)
    (Hk : 0 ≤ k ∧ k ≤ (uents.length : Int) ∧ 0 ≤ ipo ∧ ipo ≤ (uents.length : Int))
    (H : LogPersistOk σ sents uents ipo [] stored)
    (Hst : ipo < k → stored = sents ++ uents.take k.toNat) :
    LogPersistOk σ (sents ++ uents.take k.toNat) (uents.drop k.toNat)
      (max ipo k - k) [] stored ∧
    (uents.drop k.toNat = [] → sents ++ uents.take k.toNat = σ.ents) := by
  obtain ⟨Hpre, Heq, _, Hsto⟩ := H
  simp only [LogPersistOk, storApp] at Hpre Heq Hsto ⊢
  by_cases Hle : k ≤ ipo
  · have Hsplit : uents.take k.toNat ++ (uents.drop k.toNat).take (max ipo k - k).toNat
        = uents.take ipo.toNat := by
      rw [← List.take_add, show k.toNat + (max ipo k - k).toNat = ipo.toNat by omega]
    refine ⟨⟨?_, ?_, fun _ => trivial, Hsto⟩, ?_⟩
    · rw [List.append_assoc, Hsplit]; exact Hpre
    · intro Hfull
      rw [List.length_drop] at Hfull
      rw [List.append_assoc, List.take_append_drop]
      exact Heq (by omega)
    · intro Hnil
      have Hk' : uents.length ≤ k.toNat := List.drop_eq_nil_iff.mp Hnil
      rw [List.take_of_length_le Hk']
      exact Heq (by omega)
  · have Hs := Hst (by omega)
    rw [← Hsto] at Hs
    have H0 : (max ipo k - k).toNat = 0 := by omega
    refine ⟨⟨?_, ?_, fun _ => trivial, Hsto⟩, ?_⟩
    · rw [H0, List.take_zero, List.append_nil, Hs]; exact List.prefix_refl _
    · intro Hfull
      rw [H0, List.length_drop] at Hfull
      rw [List.append_assoc, List.take_append_drop, Hs,
        List.take_of_length_le (by omega : uents.length ≤ k.toNat)]
    · intro _; exact Hs.symm

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
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



/-! ## The storage's hand-out, ahead of `acceptUnstable` (2026-10-10)

`logHanded ls` is the log at `ls` (nothing unpersisted) once the storage has handed out the
entries a `Ready` hands out (`nextUnstable ls`): they are recorded as unpersisted and as
what the storage holds once appended, while `offsetInProgress` has not moved yet.
`ownRaftLog_handout` takes the log there, with the storage's ghost hand-out law, which
gives the application the right to append; `acceptUnstable` then moves `offsetInProgress`
(to `logAcceptUnstable ls`). `node.go` needs the two apart: the application receives the
right with the `Ready` (`readyc <- rd`, in the channel's atomic update), and `run` calls
`acceptReady` only afterwards. -/

section handed
variable [FfiSyntax]

def logHanded (ls : LogState) : LogState :=
  { ls with unpersisted := nextUnstable ls, stored := ls.sents ++ ls.uents }

/-- The persistence invariant after the hand-out: the batch handed out continues the
in-progress prefix the storage holds (`persist_accept`, which this follows). -/
theorem persist_handed (prev : entryID) (σ : StorState) (sents uents : List raftpb.Entry)
    (ipo : Int)
    (Hidx : LogIndicesOk prev (sents ++ uents))
    (Hsp : σ.prev = prev)
    (Hipo : 0 ≤ ipo ∧ ipo ≤ (uents.length : Int))
    (st : List raftpb.Entry)
    (H : LogPersistOk σ sents uents ipo [] st) :
    LogPersistOk σ sents uents ipo (uents.drop ipo.toNat) (sents ++ uents) := by
  obtain ⟨-, -, H3, H4⟩ := persist_accept prev σ sents uents ipo Hidx Hsp Hipo st H
  refine ⟨?_, fun _ => H4.symm, H3, H4⟩
  rw [H4]
  exact (List.prefix_append_right_inj sents).mpr (List.take_prefix _ _)

end handed

section handout
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The storage's hand-out law for the entries a `Ready` hands out (the first half of what
`acceptUnstable` did until 2026-10-10). -/
theorem ownRaftLog_handout (l : Loc) (ls : LogState) (Hunp0 : ls.unpersisted = [])
    (Hs0 : ls.snap = none) :
    ⊢ ownRaftLog (GF := GF) l ls ==∗
      ownRaftLog l (logHanded ls) ∗ appendRight ls.storage (nextUnstable ls) := by
  iintro Hlog
  iNamed Hlog
  have Hcontig : ∀ (k : Nat) (e : raftpb.Entry), ls.uents[k]? = some e →
      uint.Z e.Index' = uint.Z lv.unstable'.offset' + (k : Int) := by
    intro k e Hk
    have Hk' : (ls.sents ++ ls.uents)[ls.sents.length + k]? = some e := by
      rw [List.getElem?_append_right (by omega)]
      simpa using Hk
    have := Hidx _ _ Hk'
    push_cast at this
    omega
  obtain ⟨Hsp, -, -⟩ : LogStoreOk none σ ls.prev ls.sents ls.uents := Hs0 ▸ Hstore
  have Hhead : ∀ e0, (nextUnstable ls).head? = some e0 →
      uint.Z e0.Index' = uint.Z ls.inprogress ∧
      uint.Z ls.inprogress - uint.Z lv.unstable'.offset' < (ls.uents.length : Int) := by
    intro e0 He0
    simp only [nextUnstable, List.head?_drop] at He0
    have Hlt := (List.getElem?_eq_some_iff.1 He0).1
    have Hc := Hcontig _ _ He0
    simp only [logOffset] at Hc Hlt
    constructor <;> omega
  have Hp0 := Hpersist Hs0
  rw [Hunp0] at Hp0
  have Hplen := Hp0.1.length_le
  simp only [storApp, List.length_append, List.length_take] at Hplen
  have Hpo : σ.pend = [] ∧ (nextUnstable ls ≠ [] → PendOk σ (nextUnstable ls)) := by
    refine ⟨Hpend.1.trans Hunp0, fun Hne => ⟨Hne, fun e0 He0 => ?_⟩⟩
    obtain ⟨Hi, Hlt⟩ := Hhead e0 He0
    rw [Hsp]
    constructor <;> omega
  imod isStorage_handout lv.storage' σ (nextUnstable ls) Hpo $$ HisStorage HStorage
    with ⟨HStorage, Happ⟩
  have Hstore' : LogStoreOk (logHanded ls).snap { σ with pend := nextUnstable ls }
      (logHanded ls).prev (logHanded ls).sents (logHanded ls).uents := Hstore
  have Hssnap' : (logHanded ls).snap = none →
      StoredSnapOk { σ with pend := nextUnstable ls } (logHanded ls).committed
        (logHanded ls).prev ((logHanded ls).sents ++ (logHanded ls).uents) := Hssnap
  have HpendN : PendLogOk { σ with pend := nextUnstable ls } (logHanded ls) := by
    refine ⟨rfl, fun _ e0 He0 => ?_⟩
    obtain ⟨Hi, Hlt⟩ := Hhead e0 He0
    simp only [logHanded] at He0 ⊢
    word
  have HpersistN : (logHanded ls).snap = none →
      LogPersistOk { σ with pend := nextUnstable ls } (logHanded ls).sents (logHanded ls).uents
        (uint.Z (logHanded ls).inprogress - uint.Z lv.unstable'.offset')
        (logHanded ls).unpersisted (logHanded ls).stored := by
    intro _
    simp only [LogPersistOk, storApp_pend, logHanded]
    simp only [nextUnstable, logOffset, ← Hoffset]
    exact persist_handed ls.prev σ ls.sents ls.uents _ Hidx Hsp (by omega) ls.stored Hp0
  imodintro
  isplitr [Happ]
  · iapply ownRaftLog_intro l lv lv.storage' { σ with pend := nextUnstable ls } ls.snap ls.uents
      (logHanded ls) rfl Hcm Hap Hidx Hnowrap Hstore' Hoffset Happlied Hpapplied
      Hcommitted Hssnap' Hapg Hip Hipb HpersistN Happlying Hpaused Hasz Hamx Hstor HpendN rfl rfl
      $$ Hl HisStorage HStorage Husnap Huents Huents_cap Hl_logger Hu_logger
  rw [← Hstor]; iexact Happ

end handout

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean).
proj_simps Perennial.EtcdGrove.logAcceptUnstable Perennial.EtcdGrove.logAppliedTo
  Perennial.EtcdGrove.logHanded
