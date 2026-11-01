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

raft v3.7 (stage R3 of the retarget, 2026-10-15): the log-level part only (the sections on the
log's state and `ownRaftLog_handout`), the entries `EntryM`; the tracker lemma comes with the raft
layer (R4).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftlog
import Proof.go_etcd_io.raft.v3.InvStorageLaws

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

-- `MsgStorageApplyResp`, `LocalAppendThread`, `LocalApplyThread` are in `SpecResults.lean`
-- (stage R1).

section readylog
variable [GooseExts]

/-- One past the last index. -/
def logEnd (ls : LogState) : w64 := logLast ls + W64 1

/-- `acceptUnstable()`: every unstable entry is in progress (`offsetInProgress` at the
end), and the ones just handed out are now the application's to persist
(`LogState.unpersisted`); once it has, the storage holds the whole log (`stored`,
2026-10-10). -/
def logAcceptUnstable (ls : LogState) : LogState :=
  { ls with inprogress := logEnd ls, unpersisted := nextUnstable ls,
            stored := ls.sents ++ ls.uents,
            -- (D22 S-d1) a pending snapshot is in progress
            sip := ls.sip || ls.snap.isSome,
            -- (D22 S-d2) and the storage, to be given what is now stored, no longer at it
            sat := false }

/-- The committed entries not yet handed out for applying: `(applying, committed]` --
what `nextCommittedEnts(true)` slices, before `maxSize` cuts it short. -/
def logCommittedEnts (ls : LogState) : List EntryM :=
  (plogFrom ls.prev (ls.sents ++ ls.uents) (ls.applying + W64 1)).take
    (uint.Z ls.committed - uint.Z ls.applying).toNat

/-- `acceptApplying` after a `Ready` that handed out `ce`: `applying` moves to `ce`'s
last index and the applying budget grows by `sz` (`entsSize(ce)`, whose value no spec
pins); nothing changes for an empty `ce`, which `acceptReady` does not accept. -/
def logAcceptApplying (ls : LogState) (ce : List EntryM) (sz : w64) : LogState :=
  match ce.getLast? with
  | some e => { ls with applying := e.Index', apsize := ls.apsize + sz }
  | none => ls

/-- `raft.appliedTo(index, size)`: `applied` moves to `max(index, applied)`
(`raftLog.appliedTo` then moves `applying` up to it and releases `size` of the applying
budget). (D22 S-d1b) `appliedSnap`'s window (`aps`) ends once `applied` reaches the boundary. -/
def logAppliedTo (ls : LogState) (index size : w64) : LogState :=
  let na := w64Max index ls.applied
  { ls with applied := na,
            applying := w64Max ls.applying na,
            apsize := if uint.Z size < uint.Z ls.apsize then ls.apsize - size else W64 0,
            aps := ls.aps && decide (uint.Z na < uint.Z ls.prev.index') }

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

/-- (2026-10-25, T-M M2b) `stableTo` moves entries from the unstable part to the stable one: their
concatenation, the log, is unchanged. -/
theorem logStableTo_concat (ls : LogState) (id : entryID) :
    (logStableTo ls id).sents ++ (logStableTo ls id).uents = ls.sents ++ ls.uents := by
  unfold logStableTo
  split
  · simp only [List.append_assoc, List.take_append_drop]
  · rfl

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
  -- (D22 S-d1b) or the storage holds the pending snapshot (the acknowledgement of a snapshot's
  -- `Ready`, after the absorption of the application's receipt: `ownRaftLogW`'s `sapp`)
  (ls.snap = none ∨ ls.sapp = true) ∧
  ls.unpersisted = [] ∧
  ls.stored = (ls.sents ++ ls.uents).take (uint.Z id.index' - uint.Z ls.prev.index').toNat

/-! What `acceptApplying` and `stableTo` leave alone (2026-10-09): the fields the
`RawNode` predicate (`InvRawnode.lean`) states its facts on. Both functions branch, so
`proj_simps` does not apply. -/

theorem logAcceptApplying_fields (ls : LogState) (ce : List EntryM) (sz : w64) :
    (logAcceptApplying ls ce sz).committed = ls.committed ∧
    (logAcceptApplying ls ce sz).inprogress = ls.inprogress ∧
    (logAcceptApplying ls ce sz).unpersisted = ls.unpersisted ∧
    (logAcceptApplying ls ce sz).snap = ls.snap ∧
    (logAcceptApplying ls ce sz).prev = ls.prev ∧
    (logAcceptApplying ls ce sz).stored = ls.stored := by
  unfold logAcceptApplying; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Neither changes the storage (2026-10-10). -/
theorem logAcceptApplying_storage (ls : LogState) (ce : List EntryM) (sz : w64) :
    (logAcceptApplying ls ce sz).storage = ls.storage := by
  unfold logAcceptApplying; split <;> rfl

theorem logStableTo_storage (ls : LogState) (id : entryID) :
    (logStableTo ls id).storage = ls.storage := by
  unfold logStableTo; split <;> rfl

/-- (U8 v2) ... and the storage names. -/
theorem logStableTo_sn (ls : LogState) (id : entryID) : (logStableTo ls id).sn = ls.sn := by
  unfold logStableTo; split <;> rfl

theorem logAcceptApplying_applying (ls : LogState) (ce : List EntryM) (sz : w64)
    (e : EntryM) (He : ce.getLast? = some e) :
    (logAcceptApplying ls ce sz).applying = e.Index' := by
  unfold logAcceptApplying; rw [He]

/-- A `Ready`'s acceptance keeps the last index (2026-10-16, stage R8a): what `ownRaftPhysC_view`'s
close asks of a leader. -/
theorem logLast_acceptUnstable (ls : LogState) : logLast (logAcceptUnstable ls) = logLast ls := rfl

theorem logLast_acceptApplying (ls : LogState) (ce : List EntryM) (sz : w64) :
    logLast (logAcceptApplying ls ce sz) = logLast ls := by
  unfold logAcceptApplying; split <;> rfl

/-- `stableTo` keeps the last index (2026-10-16, stage R8a): what `ownRaftPhysC_log_at` asks of a
leader. -/
theorem logLast_stableTo (ls : LogState) (id : entryID) :
    logLast (logStableTo ls id) = logLast ls := by
  unfold logStableTo
  split
  · simp only [logLast, List.length_append, List.length_take, List.length_drop]
    congr 1; push_cast; omega
  · rfl

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
theorem persist_accept (prev : entryID) (σ : StorState) (sents uents : List EntryM)
    (ipo : Int)
    (Hidx : LogIndicesOk prev (sents ++ uents))
    (Hsp : σ.prev = prev)
    (Hipo : 0 ≤ ipo ∧ ipo ≤ (uents.length : Int))
    (st : List EntryM)
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
theorem persist_stable (σ : StorState) (sents uents stored : List EntryM)
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

-- (`ownTracker_autoleave`, on the tracker, comes with the raft layer, stage R4.)

section handed
variable [GooseExts]

def logHanded (ls : LogState) : LogState :=
  { ls with unpersisted := nextUnstable ls, stored := ls.sents ++ ls.uents }

/-- (U8 v2 step 4) The end of what a `Ready` hands out frozen (`ownRaftLog_handout`): its committed
entries below the batch it hands out (`offsetInProgress`). -/
def frozenEnd (ls : LogState) : Nat :=
  min (uint.nat ls.committed) (uint.nat ls.inprogress - 1)

/-- (U8 v2 step 4) Raft's log entries at the indices `applying + 1 .. frozenEnd ls`: the committed
entries a `Ready` hands out frozen, before `acceptReady` moves `applying` (`ownRaftLog_handout`). -/
def frozenRdy (ls : LogState) : List EntryM :=
  ((ls.sents ++ ls.uents).drop (uint.nat ls.applying - uint.nat ls.prev.index')).take
    (frozenEnd ls - uint.nat ls.applying)

/-- The persistence invariant after the hand-out: the batch handed out continues the
in-progress prefix the storage holds (`persist_accept`, which this follows). -/
theorem persist_handed (prev : entryID) (σ : StorState) (sents uents : List EntryM)
    (ipo : Int)
    (Hidx : LogIndicesOk prev (sents ++ uents))
    (Hsp : σ.prev = prev)
    (Hipo : 0 ≤ ipo ∧ ipo ≤ (uents.length : Int))
    (st : List EntryM)
    (H : LogPersistOk σ sents uents ipo [] st) :
    LogPersistOk σ sents uents ipo (uents.drop ipo.toNat) (sents ++ uents) := by
  obtain ⟨-, -, H3, H4⟩ := persist_accept prev σ sents uents ipo Hidx Hsp Hipo st H
  refine ⟨?_, fun _ => H4.symm, H3, H4⟩
  rw [H4]
  exact (List.prefix_append_right_inj sents).mpr (List.take_prefix _ _)

end handed

/-- (U8 v2 step 4) A range of a frozen prefix `d0 :: ents[..F]` inside a prefix `P` the storage's
log `ents` shares with the log `L`: the log's entries there. -/
theorem frozen_sub_eq [GooseExts] (L ents P : List EntryM) (d0 : EntryM) (a n F : Nat)
    (hP1 : P <+: ents) (hP2 : P <+: L) (hn : a + n ≤ F) (hF : a + n ≤ P.length) :
    ((d0 :: ents.take F).drop (a + 1)).take n = (L.drop a).take n := by
  rw [List.drop_succ_cons]
  have hl := hP1.length_le
  rw [← take_drop_prefix (List.take_prefix F ents) a n (by rw [List.length_take]; omega),
    take_drop_prefix hP1 a n hF, take_drop_prefix hP2 a n hF]

section handout
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The storage's hand-out law for the entries a `Ready` hands out (the first half of what
`acceptUnstable` did until 2026-10-10). (U8 v2 step 4) The storage's log is also frozen up to
`frozenEnd ls` (the committed entries below the batch), and the committed entries from
`applying + 1` to there are given, frozen (`frozenRdy`: persistent). -/
theorem ownRaftLog_handout (l : Loc) (ls : LogState) (Hunp0 : ls.unpersisted = [])
    (Hs0 : ls.snap = none) :
    ⊢ ownRaftLog (GF := GF) l ls ==∗
      ownRaftLog l (logHanded ls) ∗ appendRight ls.storage (nextUnstable ls) ∗
      storLog ls.storage (uint.nat ls.applying + 1) DFrac.discard (frozenRdy ls) := by
  iintro Hlog
  iNamed Hlog
  have Hcontig : ∀ (k : Nat) (e : EntryM), ls.uents[k]? = some e →
      uint.Z e.Index' = uint.Z lv.unstable'.offset' + (k : Int) := by
    intro k e Hk
    have Hk' : (ls.sents ++ ls.uents)[ls.sents.length + k]? = some e := by
      rw [List.getElem?_append_right (by omega)]
      simpa using Hk
    have := Hidx _ _ Hk'
    push_cast at this
    omega
  obtain ⟨Hsp, -, -⟩ : LogStoreOk none σ ls.prev ls.sents ls.uents := Hs0 ▸ Hstore
  have Hlnt : ls.lent = false := by
    cases h : ls.lent
    · rfl
    · exact absurd Hs0 (Hlent h)
  ihave HStorage := lentStor_open Hlnt _ _ _ $$ HStorage
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
  have Hpo : σ.pend = [] ∧ (nextUnstable ls ≠ [] →
      PendOk σ (nextUnstable ls) ∧ PendAbove σ (nextUnstable ls)) := by
    refine ⟨Hpend.1.trans Hunp0, fun Hne => ⟨⟨Hne, fun e0 He0 => ?_⟩, fun e0 He0 => ?_⟩⟩
    · obtain ⟨Hi, Hlt⟩ := Hhead e0 He0
      refine ⟨by rw [Hsp]; omega, by rw [Hsp]; omega, fun k e Hk => ?_⟩
      -- (D19i part 1) the batch is numbered consecutively, as the unstable entries are
      simp only [nextUnstable, List.head?_drop, List.getElem?_drop] at He0 Hk
      have h1 := Hcontig _ _ He0
      have h2 := Hcontig _ _ Hk
      push_cast at h1 h2
      omega
    · obtain ⟨Hi, -⟩ := Hhead e0 He0
      have := Hfl.2.2.1
      have := Hfl.2.1
      rw [Hfl.1]; omega
  -- (U8 v2 step 4) freeze the storage's log up to `frozenEnd ls`, below the batch
  obtain ⟨Hfr1, Hfr2, -⟩ := Hfr.1 Hlnt
  have e1 := uint_nat_eq ls.committed; have e2 := uint_nat_eq ls.inprogress
  have e3 := uint_nat_eq ls.applying; have e4 := uint_nat_eq ls.prev.index'
  have e5 := uint_nat_eq σ.prev.index'
  have Hoff := Hoffset; have Hipb' := Hipb
  have Hpa := Hpapplied Hs0; have Hapl := Happlying; have Hlt := Hfl.2.2.1
  have HkOut : σ.kOut = uint.nat σ.prev.index' + 1 + σ.ents.length := by
    unfold StorState.kOut; rw [Hpend.1.trans Hunp0]; rfl
  have HP := Hp0.1
  simp only [storApp] at HP
  have HPlen : (ls.sents ++ ls.uents.take (uint.Z ls.inprogress - uint.Z lv.unstable'.offset').toNat).length
      = uint.nat ls.inprogress - uint.nat ls.prev.index' - 1 := by
    simp only [List.length_append, List.length_take]; omega
  have HPl := HP.length_le
  rw [HPlen] at HPl
  have HfE : frozenEnd ls ≤ uint.nat ls.inprogress - 1 := Nat.min_le_right _ _
  have HfC : frozenEnd ls ≤ uint.nat ls.committed := Nat.min_le_left _ _
  have HaE : uint.nat ls.applying ≤ frozenEnd ls := Nat.le_min.2 ⟨by omega, by omega⟩
  imod ownStorage_freeze ls.sn lv.storage' σ (max σ.fr (frozenEnd ls)) (Nat.le_max_left _ _)
    (by rw [HkOut, Hsp]; exact Nat.max_lt.2 ⟨by omega, by omega⟩) $$ HStorage with HStorage
  ihave ⟨⟨%d0, %-, #HF⟩, HStorage⟩ := ownStorage_frozen_keep _ _ _ $$ HStorage
  have Hpo' : σ.pend = [] ∧ (nextUnstable ls ≠ [] → PendOk σ (nextUnstable ls) ∧
      ∀ e0, (nextUnstable ls).head? = some e0 →
        max σ.fr (frozenEnd ls) < uint.nat e0.Index') := by
    refine ⟨Hpo.1, fun Hne => ⟨(Hpo.2 Hne).1, fun e0 He0 => ?_⟩⟩
    obtain ⟨Hi, -⟩ := Hhead e0 He0
    have := uint_nat_eq e0.Index'
    exact Nat.max_lt.2 ⟨by omega, by omega⟩
  imod ownStorage_handout_opt ls.sn lv.storage' { σ with fr := max σ.fr (frozenEnd ls) }
    (nextUnstable ls) Hpo' $$ HStorage with ⟨HStorage, Happ⟩
  -- the committed entries from `applying + 1` on, out of the frozen prefix
  ihave #HR : storLog ls.storage (uint.nat ls.applying + 1) DFrac.discard (frozenRdy ls) $$ []
  · rw [← Hstor]
    iapply (storLog_sub lv.storage' (uint.nat σ.prev.index')
      (uint.nat ls.applying - uint.nat ls.prev.index' + 1) (frozenEnd ls - uint.nat ls.applying)
      _ _ _ (by rw [Hsp]; omega) ?_) $$ HF
    show ((d0 :: σ.ents.take (max σ.fr (frozenEnd ls) - uint.nat σ.prev.index')).drop
      (uint.nat ls.applying - uint.nat ls.prev.index' + 1)).take
        (frozenEnd ls - uint.nat ls.applying) = frozenRdy ls
    unfold frozenRdy
    rw [Hsp]
    exact frozen_sub_eq _ _ _ d0 _ _ _ HP
      ((List.prefix_append_right_inj ls.sents).mpr (List.take_prefix _ _)) (by omega) (by omega)
  have Hstore' : LogStoreOk (logHanded ls).snap
      { σ with fr := max σ.fr (frozenEnd ls), pend := nextUnstable ls }
      (logHanded ls).prev (logHanded ls).sents (logHanded ls).uents := Hstore
  have HpendN : PendLogOk { σ with fr := max σ.fr (frozenEnd ls), pend := nextUnstable ls }
      (logHanded ls) := by
    refine ⟨rfl, fun _ e0 He0 => ?_⟩
    obtain ⟨Hi, Hlt⟩ := Hhead e0 He0
    simp only [logHanded] at He0 ⊢
    word
  have HpersistN0 : (logHanded ls).snap = none →
      LogPersistOk { σ with pend := nextUnstable ls } (logHanded ls).sents (logHanded ls).uents
        (uint.Z (logHanded ls).inprogress - uint.Z lv.unstable'.offset')
        (logHanded ls).unpersisted (logHanded ls).stored := by
    intro _
    simp only [LogPersistOk, storApp_pend, logHanded]
    simp only [nextUnstable, logOffset, ← Hoffset]
    exact persist_handed ls.prev σ ls.sents ls.uents _ Hidx Hsp (by omega) ls.stored Hp0
  have HpersistN : (logHanded ls).snap = none →
      LogPersistOk { σ with fr := max σ.fr (frozenEnd ls), pend := nextUnstable ls }
        (logHanded ls).sents (logHanded ls).uents
        (uint.Z (logHanded ls).inprogress - uint.Z lv.unstable'.offset')
        (logHanded ls).unpersisted (logHanded ls).stored := HpersistN0
  have HfrN : FrOk { σ with fr := max σ.fr (frozenEnd ls), pend := nextUnstable ls }
      (logHanded ls) := by
    refine ⟨fun _ => ⟨?_, ?_, fun sid h => absurd h (by simp [logHanded, Hs0])⟩, Hfr.2.1, Hfr.2.2⟩
    · show max σ.fr (frozenEnd ls) ≤ uint.nat ls.committed
      exact Nat.max_le.2 ⟨Hfr1, HfC⟩
    · show max σ.fr (frozenEnd ls) < uint.nat ls.inprogress
      exact Nat.max_lt.2 ⟨Hfr2, by omega⟩
  have HflN : FlOk { σ with fr := max σ.fr (frozenEnd ls), pend := nextUnstable ls }
      (logHanded ls) := by
    refine ⟨Hfl.1, Hfl.2.1, ?_, fun e0 He0 => ?_, fun h _ => (h Hs0).elim,
      StorTermsOk.of_none Hs0⟩
    · have := Hfl.2.2.1
      have := Hipb
      simp only [logHanded]
      word
    · obtain ⟨Hi, -⟩ := Hhead e0 He0
      have := Hfl.2.2.1
      have := Hfl.2.1
      show uint.Z σ.fl < _
      rw [Hfl.1]; omega
  imodintro
  iframe HR
  isplitr [Happ]
  · iapply ownRaftLog_intro (K := ls.ksn) (sn := ls.sn) l lv lv.storage'
      { σ with fr := max σ.fr (frozenEnd ls), pend := nextUnstable ls } ls.snap ls.uents
      (logHanded ls) rfl Hcm Hap Hidx Hnowrap Hstore' Hoffset Happlied Hpapplied
      Hcommitted Hapg Hip Hipb HpersistN Happlying Hpaused Hasz Hamx Hstor HpendN HflN Hsip Hsipn
      Hlent Hq ⟨(fun h => by
        have := Hsipn Hs0; simp only [logHanded] at h; rw [this] at h; cases h),
        (fun h => absurd Hs0 h)⟩
      (fun h => absurd (Hsat h).1 (by rw [Hs0]; simp)) HfrN rfl rfl rfl rfl rfl
      $$ Hl HisStorage [HStorage] Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger
    iapply lentStor_close (b := (logHanded ls).lent) Hlnt; iexact HStorage
  rw [← Hstor]; iexact Happ

end handout

/-! ### The snapshot's storage (D22 S-d1b, 2026-10-21)

A `Ready` that hands out a snapshot (`rd.Snapshot`) hands the application **the storage itself**
(`ownRaftLog_lend`) rather than the right to append a batch (`ownRaftLog_handout`): raft reads no
storage while a snapshot is pending, and the application needs the whole storage for
`ApplySnapshot` and the `Append` of the entries after the snapshot. It returns the storage at the
snapshot holding those entries, which the log absorbs (`ownRaftLog_absorb_snap`) before the
acknowledgement's `stableTo`; that absorption opens the `sapp` window (`ownRaftLogW`), which the
acknowledgement's `appliedSnap` closes (`stableSnapTo`, `logStableSnap`). -/

section snapdefs
variable [GooseExts]

/-- (D22 S-d1b) `raftLog.stableSnapTo(i)` (`log.go:369`, `unstable.stableSnapTo`): on a hit the
pending snapshot is dropped and no longer in progress, the storage (which holds it, `sapp`) is
the log's boundary, and `appliedSnap`'s window opens (`aps`: `applied` is still below it). -/
def logStableSnap (ls : LogState) (i : w64) : LogState :=
  if snapHit ls.snap i then
    { ls with snap := none, sip := false, sapp := false, aps := true, sat := false }
  else ls

/-- (U8 v2) `stableSnapTo` keeps the storage names. -/
theorem logStableSnap_sn (ls : LogState) (i : w64) : (logStableSnap ls i).sn = ls.sn := by
  unfold logStableSnap; split <;> rfl

theorem logStableSnap_fields (ls : LogState) (i : w64) :
    (logStableSnap ls i).prev = ls.prev ∧ (logStableSnap ls i).sents = ls.sents ∧
    (logStableSnap ls i).uents = ls.uents ∧ (logStableSnap ls i).committed = ls.committed ∧
    (logStableSnap ls i).applied = ls.applied ∧ (logStableSnap ls i).applying = ls.applying ∧
    (logStableSnap ls i).inprogress = ls.inprogress ∧
    (logStableSnap ls i).unpersisted = ls.unpersisted ∧ (logStableSnap ls i).stored = ls.stored ∧
    (logStableSnap ls i).storage = ls.storage ∧ (logStableSnap ls i).ksn = ls.ksn ∧
    (logStableSnap ls i).fl = ls.fl ∧ (logStableSnap ls i).lent = ls.lent ∧
    (logStableSnap ls i).apsize = ls.apsize ∧ (logStableSnap ls i).apmax = ls.apmax := by
  unfold logStableSnap; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl⟩

theorem logStableSnap_none (ls : LogState) (i : w64) (h : ls.snap = none) :
    logStableSnap ls i = ls := by
  unfold logStableSnap; rw [h]; rfl

theorem logStableSnap_miss (ls : LogState) (i : w64) (h : snapHit ls.snap i = false) :
    logStableSnap ls i = ls := by
  unfold logStableSnap; rw [h]; rfl

/-- (D22 S-d3a) `SnpOk` after `stableSnapTo`: on a hit the snapshot is gone, nothing is in progress
or absorbed. -/
theorem SnpOk.stableSnap {g : NGhost} {ls : LogState} (i : w64) (H : SnpOk g ls) :
    SnpOk g (logStableSnap ls i) := by
  unfold logStableSnap
  split
  · obtain ⟨H1, H2, -, -, -, H6⟩ := H
    refine ⟨H1, fun k hk => ?_, fun h => by simp at h, fun h => by simp at h,
      fun k hk hl => ⟨fun h => by simp at h, fun _ h => by simp at h⟩, H6⟩
    obtain ⟨-, Hb, Hc⟩ := H2 k hk
    exact ⟨fun h => by simp at h, Hb, Hc⟩
  · exact H

/-- (D22 S-d4 item 3) `SnpExt` of a log whose `applying` grew (past the snapshot handed out if it
was in `appliedSnap`'s window), the rest it reads kept. -/
theorem SnpExt.raise {g : NGhost} {ls ls' : LogState} (h : SnpExt g ls)
    (hlt : ls'.lent = ls.lent) (hsn : ls'.snap = ls.snap) (hsx : ls'.sxt = ls.sxt)
    (hap : uint.Z ls.applying ≤ uint.Z ls'.applying)
    (haps : ls.aps = true → ∀ k, g.snp = some k → uint.Z k.sid.index' ≤ uint.Z ls'.applying) :
    SnpExt g ls' := by
  intro k hk hl
  rw [hlt] at hl
  obtain ⟨h1, h2⟩ := h k hk hl
  refine ⟨fun hs => ?_, fun hs _ => ?_⟩
  · rw [hsx]; exact h1 (hsn ▸ hs)
  · rcases Bool.eq_false_or_eq_true ls.aps with Ha | Ha
    · exact haps Ha k hk
    · have := h2 (hsn ▸ hs) Ha; omega

/-- (D22 S-d3a) ... and after `appliedTo`, which keeps every field `SnpOk` reads but `applying`,
which grows, and (D22 S-d4 item 3) `appliedSnap`'s window, which it may end: past the snapshot
handed out (`Hk`). -/
theorem SnpOk.appliedTo {g : NGhost} {ls : LogState} (i sz : w64) (H : SnpOk g ls)
    (Hk : ls.aps = true → ∀ k, g.snp = some k → uint.Z k.sid.index' ≤ uint.Z i) :
    SnpOk g (logAppliedTo ls i sz) :=
  H.of_fields rfl rfl rfl rfl rfl (Int.le_refl _) (fun h k hk hl => by
    obtain ⟨h1, h2⟩ := h k hk hl
    refine ⟨h1, fun hs _ => ?_⟩
    show uint.Z k.sid.index' ≤ uint.Z (w64Max ls.applying (w64Max i ls.applied))
    rw [w64Max_spec, w64Max_spec]
    rcases Bool.eq_false_or_eq_true ls.aps with Ha | Ha
    · have := Hk Ha k hk; omega
    · have := h2 hs Ha; omega)

/-- (D22 S-d1b) The absorption of the application's receipt for the snapshot `sid` (its storage
at `sid`): the storage is no longer lent, nothing is unpersisted, and the storage holds the
pending snapshot (`sat`) when `sid` is the one in progress -- otherwise (a second restore
between the `Ready` and its acknowledgement) it is shadowed again. -/
def logAbsorbSnap (ls : LogState) (sid : entryID) : LogState :=
  { ls with lent := false, unpersisted := [],
            sat := @decide (ls.snap = some sid ∧ ls.sip = true) (Classical.propDecidable _),
            sxt := sid.index',
            -- (2026-10-28, stage U4a) the storage at the snapshot: nothing after it to record
            stb := sid.index', sdt := [] }

theorem logAbsorbSnap_sat (ls : LogState) (sid : entryID) :
    (logAbsorbSnap ls sid).sat = true ↔ ls.snap = some sid ∧ ls.sip = true := by
  simp only [logAbsorbSnap, decide_eq_true_eq]

end snapdefs

section snapstor
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (U8 v2) The log once a snapshot `Ready` lent its ranges (before the batch's hand-out). (raft-final
phase 2, 2026-10-30: the snapshot handed out is the lent one, `sg := prev.index`; until then
`max sg prev.index`, the same, since `sg` is below the frozen end, below the pending snapshot, but
not recorded: `SnpSg`.) -/
def lendLog (ls : LogState) : LogState :=
  { ls with lent := true, sat := false, sg := uint.nat ls.prev.index' }

/-- (U8 v2) Raft's view once a snapshot `Ready` lent its ranges. -/
def lendView (σ : StorState) (ls : LogState) : StorState :=
  { σ with pend := nextUnstable ls, sg := uint.nat ls.prev.index' }

/-- (raft-final phase 2, 2026-10-30) The view's snapshot handed out at most its boundary, which is at
most its frozen end (`ownStorage`'s pure part), kept with the view. -/
private theorem ownStorage_sg (sn : StorNames) (st : Storage) (σ : StorState) :
    ownStorage (GF := GF) sn st σ ⊢
      ⌜σ.sg ≤ uint.nat σ.prev.index' ∧ uint.nat σ.prev.index' ≤ σ.fr⌝ ∗ ownStorage sn st σ := by
  unfold ownStorage
  iintro ⟨%e0, #Hcomp, #HFr, HO, Hend, Hau, %Hw⟩
  isplitr
  · ipureintro; exact ⟨Hw.2.2.2.2, Hw.2.1⟩
  iexists e0
  iframe Hcomp HFr HO Hend Hau
  ipureintro; exact Hw


/-- (D22 S-d1b; U8 v2) **The ranges lent** with a snapshot `Ready`: with a snapshot pending at
`s`, nothing unpersisted and nothing lent yet, the application gets every range above raft's frozen
prefix, with the end, and the right to install the snapshot (`storGiven`, the API's `snapGiven`);
the log records the batch the `Ready` hands out as the application's (`logHanded`), the ranges as
lent, and the snapshot as handed out (`sg`). Raft keeps its authorities (`lentStor`). -/
theorem ownRaftLog_lend (l : Loc) (ls : LogState) (Hunp0 : ls.unpersisted = [])
    (Hs0 : ls.snap ≠ none) (Hlt0 : ls.lent = false)
    -- (U8 v2 step 4) the snapshot not yet handed out
    (Hsip0 : ls.sip = false) :
    ⊢ ownRaftLog (GF := GF) l ls ==∗
      ownRaftLog l (logHanded (lendLog ls)) ∗
      (∃ (k : Nat) (old : List EntryM), storLog ls.storage k (DFrac.own 1) old ∗
        storEnd ls.storage (k + old.length) ∗ ⌜k ≤ uint.nat ls.prev.index'⌝) ∗
      storGiven ls.sn (uint.nat ls.prev.index') := by
  iintro Hlog
  iNamed Hlog
  -- (U8 v2 step 4) the lend starts at or below the snapshot (`FrOk`)
  have Hk : σ.fr + 1 ≤ uint.nat ls.prev.index' := by
    obtain ⟨sid, Hs⟩ := Option.ne_none_iff_exists'.1 Hs0
    have Hpv : ls.prev = sid := (Hs ▸ Hstore : LogStoreOk (some sid) σ ls.prev ls.sents ls.uents).1
    have := (Hfr.1 Hlt0).2.2 sid Hs Hsip0
    rw [Hpv]; omega
  ihave HStorage := lentStor_open Hlt0 _ _ _ $$ HStorage
  -- (raft-final phase 2) the snapshot last handed out below the lent one
  icases ownStorage_sg _ _ _ $$ HStorage with ⟨%Hsg0, HStorage⟩
  have Hsgle : σ.sg ≤ uint.nat ls.prev.index' := by omega
  have Hcontig : ∀ (k : Nat) (e : EntryM), ls.uents[k]? = some e →
      uint.Z e.Index' = uint.Z lv.unstable'.offset' + (k : Int) := by
    intro k e Hk
    have Hk' : (ls.sents ++ ls.uents)[ls.sents.length + k]? = some e := by
      rw [List.getElem?_append_right (by omega)]
      simpa using Hk
    have := Hidx _ _ Hk'
    push_cast at this
    omega
  have Hhead : ∀ e0, (nextUnstable ls).head? = some e0 →
      uint.Z e0.Index' = uint.Z ls.inprogress := by
    intro e0 He0
    simp only [nextUnstable, List.head?_drop] at He0
    have Hc := Hcontig _ _ He0
    simp only [logOffset] at Hc
    have := (List.getElem?_eq_some_iff.1 He0).1
    omega
  have Hstore' : LogStoreOk ls.snap (lendView σ ls) ls.prev ls.sents ls.uents := by
    cases Hs : ls.snap with
    | none => exact absurd Hs Hs0
    | some sid => rw [Hs] at Hstore; exact Hstore
  have Hpersist' : ls.snap = none →
      LogPersistOk (lendView σ ls)
        ls.sents ls.uents (uint.Z ls.inprogress - uint.Z lv.unstable'.offset') (nextUnstable ls)
        (ls.sents ++ ls.uents) := fun h => absurd h Hs0
  have Hpend' : PendLogOk (lendView σ ls)
      (logHanded (lendLog ls)) :=
    ⟨rfl, fun h => absurd h Hs0⟩
  have Hfl' : FlOk (lendView σ ls)
      (logHanded (lendLog ls)) := by
    refine ⟨Hfl.1, Hfl.2.1, Hfl.2.2.1, fun e0 He0 => ?_,
      fun _ h => by simp [logHanded, lendLog] at h,
      StorTermsOk.lent (by simp [logHanded, lendLog])⟩
    have := Hhead e0 He0
    have := Hfl.2.2.1
    have := Hfl.2.1
    show uint.Z σ.fl < _
    rw [Hfl.1]; omega
  have Hfr' : FrOk (lendView σ ls)
      (logHanded (lendLog ls)) :=
    ⟨fun h => by simp [logHanded, lendLog] at h,
      show uint.nat ls.prev.index' = uint.nat ls.prev.index' from rfl,
      DtOk.of_eq Hfr.2.2 rfl rfl rfl⟩
  have Hprel' : SipOk (logHanded (lendLog ls)) lv.unstable'.offset' :=
    ⟨fun _ => LogPersistRel_full _ _ _, Hprel.2⟩
  imod ownStorage_lend ls.sn lv.storage' σ (uint.nat ls.prev.index')
    (Hpend.1.trans Hunp0) Hsgle $$ HStorage with ⟨Hau, HO, Hend, #Hgiv⟩
  imodintro
  isplitl [Hl Hau Huents Huents_cap]
  · iapply ownRaftLog_intro (K := ls.ksn) (sn := ls.sn) l lv lv.storage'
      (lendView σ ls)
      ls.snap ls.uents (logHanded (lendLog ls)) rfl Hcm Hap Hidx Hnowrap Hstore'
      Hoffset Happlied Hpapplied Hcommitted Hapg Hip Hipb Hpersist' Happlying Hpaused Hasz
      Hamx Hstor Hpend' Hfl' Hsip Hsipn (fun _ => Hs0) Hq Hprel' (fun h => by cases h)
      Hfr' rfl rfl rfl rfl rfl
      $$ Hl HisStorage [Hau] Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger
    iapply (lentStor_lent (b := (logHanded (lendLog ls)).lent) rfl _ _ _).2
    iapply (storAuths_eq ls.sn { σ with sg := uint.nat ls.prev.index' } (lendView σ ls) rfl rfl)
    iexact Hau
  isplitl [HO Hend]
  · iexists σ.fr + 1, σ.ents.drop (σ.fr - uint.nat σ.prev.index')
    rw [← Hstor]
    iframe HO Hend
    ipureintro; exact Hk
  unfold storGiven
  iapply (monoNatLbOwn_le (uint.nat ls.prev.index') (Nat.le_refl _))
  iexact Hgiv

/-- (D22 S-d3a, 2026-10-21) A pending snapshot not yet handed out: the log starts at it, with no
stable part, and every unstable entry is still to be handed out (`SipOk`): what a snapshot `Ready`
hands out after the snapshot is the whole log after it, which the storage then holds (`stored`). -/
theorem ownRaftLog_snap_next (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜∀ sid, ls.snap = some sid → ls.sip = false →
        ls.prev = sid ∧ ls.sents = [] ∧ nextUnstable ls = ls.sents ++ ls.uents ∧
        0 < uint.Z sid.index' ∧ uint.Z sid.index' < 2^61 ∧ uint.Z ls.applying < uint.Z sid.index'⌝ ∗
      ownRaftLog l ls := by
  iintro H
  iNamed H
  isplitr
  · ipureintro
    intro sid Hs Hsp
    have Hst : LogStoreOk (some sid) σ ls.prev ls.sents ls.uents := Hs ▸ Hstore
    obtain ⟨Hp, Hse, Hb⟩ := Hst
    obtain ⟨Hio, Hapl⟩ := Hprel.2 (by rw [Hs]; simp) Hsp
    refine ⟨Hp, Hse, ?_, Hb.1, Hb.2, by rw [← Hp]; exact Hapl⟩
    unfold nextUnstable logOffset
    rw [Hse, List.nil_append]
    have h1 : uint.Z ls.inprogress = uint.Z lv.unstable'.offset' := by rw [Hio]
    rw [Hse] at Hoffset
    simp only [List.length_nil, Int.natCast_zero, Int.add_zero] at Hoffset ⊢
    have : (uint.Z ls.inprogress - (uint.Z ls.prev.index' + 1)).toNat = 0 := by omega
    rw [this, List.drop_zero]
  iapply ownRaftLog_intro (sn := ls.sn) l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
    Happlied Hpapplied Hcommitted Hapg Hip Hipb Hpersist Happlying
    Hpaused Hasz Hamx Hstor Hpend Hfl Hsip Hsipn Hlent Hq Hprel Hsat Hfr rfl rfl rfl rfl rfl $$ Hl
    HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger

/-- (D22 S-d3a) The log's ghost fields `SnpOk` mirrors, read out. -/
theorem ownRaftLog_snap_facts (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜(ls.lent = true → ls.snap ≠ none) ∧ (ls.sat = true → ls.snap = some ls.prev ∧ ls.sip = true ∧
        ls.lent = false ∧ ls.unpersisted = []) ∧ (ls.snap = none → ls.sip = false) ∧
        (∀ sid, ls.snap = some sid → ls.prev = sid ∧ ls.sents = [] ∧ 0 < uint.Z sid.index')⌝ ∗
      ownRaftLog l ls := by
  iintro H
  iNamed H
  isplitr
  · ipureintro
    refine ⟨Hlent, fun h => ?_, Hsipn, fun sid hs => ?_⟩
    · obtain ⟨H1, H2, H3, H4, -⟩ := Hsat h; exact ⟨H1, H2, H3, H4⟩
    · have Hst : LogStoreOk (some sid) σ ls.prev ls.sents ls.uents := hs ▸ Hstore
      exact ⟨Hst.1, Hst.2.1, Hst.2.2.1⟩
  iapply ownRaftLog_intro (sn := ls.sn) l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
    Happlied Hpapplied Hcommitted Hapg Hip Hipb Hpersist Happlying
    Hpaused Hasz Hamx Hstor Hpend Hfl Hsip Hsipn Hlent Hq Hprel Hsat Hfr rfl rfl rfl rfl rfl $$ Hl
    HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger

/-- (D22 S-d1b; S-d2, 2026-10-21; U8 v2) **The snapshot's ranges back**: the application returns
the compaction point at the snapshot `sid`, the dummy there (of its term) and the entries the
`Ready` asked to be stored (`ls.stored`) after it, owned, with the end. The log takes them back
(`logAbsorbSnap`), its view the snapshot's (`snapView`), quiet: when `sid` is the snapshot in
progress, the storage is recorded as at the pending snapshot (`sat`, `SatOk`), which the
acknowledgement's arm turns into the `sapp` window (`ownRaftLog_sapp`); otherwise (a second restore
since the `Ready`) it is shadowed again. -/
theorem ownRaftLog_absorb_snap (l : Loc) (ls : LogState) (sid : entryID) (e : EntryM)
    (Hlt : ls.lent = true) (He : e.Term' = sid.term') (Hsg : ls.sg ≤ uint.nat sid.index')
    -- (D22 S-d4 item 3) `applying` at most the snapshot the storage is at (the loan's, `LoanOk`)
    (Happ : uint.Z ls.applying ≤ uint.Z sid.index')
    -- (U8 v2 step 4) the snapshot the storage is at is at most the pending one, strictly unless
    -- the pending one is in progress (otherwise restored after the loan: past the commit index,
    -- which was at least the lent snapshot's), so that the view's frozen end keeps `FrOk`
    (Hsid : uint.nat sid.index' ≤ uint.nat ls.prev.index' ∧
      (ls.sip = false → uint.nat sid.index' < uint.nat ls.prev.index')) :
    ⊢ ownRaftLog (GF := GF) l ls -∗ storCompacted ls.storage (uint.nat sid.index') -∗
      storLog ls.storage (uint.nat sid.index') DFrac.discard [e] -∗
      storLog ls.storage (uint.nat sid.index' + 1) (DFrac.own 1) ls.stored -∗
      storEnd ls.storage (uint.nat sid.index' + 1 + ls.stored.length) -∗
      ownRaftLog l (logAbsorbSnap ls sid) := by
  iintro Hlog #Hcomp #HF HO Hend
  iNamed Hlog
  rw [← Hstor]
  ihave Hau := (lentStor_lent Hlt _ _ _).1 $$ HStorage
  ihave HSt := ownStorage_absorb_snap ls.sn lv.storage' σ sid e ls.stored He
    (by rw [Hfr.2.1]; exact Hsg) $$ Hau Hcomp HF HO Hend
  have Hsn : ls.snap ≠ none := Hlent Hlt
  have Hpend' : PendLogOk (snapView σ sid ls.stored) (logAbsorbSnap ls sid) :=
    ⟨rfl, fun h => absurd h Hsn⟩
  have Hfl' : FlOk (snapView σ sid ls.stored) (logAbsorbSnap ls sid) :=
    have Hext : StorExtOk (snapView σ sid ls.stored) (logAbsorbSnap ls sid) := fun _ _ => by
      show uint.Z sid.index' ≤ uint.Z sid.index' + ((storApp (snapView σ sid ls.stored) []).length : Int) ∧
        uint.Z ls.applying ≤ uint.Z sid.index'
      exact ⟨by have := Happ; word, Happ⟩
    have Hterms : StorTermsOk (snapView σ sid ls.stored) (logAbsorbSnap ls sid) := fun _ _ =>
      ⟨by show uint.Z sid.index' ≤ uint.Z sid.index'; omega,
       by show uint.Z sid.index' ≤ uint.Z sid.index' + (([] : List w64).length : Int)
          simp only [List.length_nil, Int.natCast_zero, Int.add_zero]; omega,
       TermsFrom.nil _ _⟩
    ⟨Hfl.1, Hfl.2.1, Hfl.2.2.1, (fun e0 He0 => by cases He0), Hext, Hterms⟩
  have Hstore' : LogStoreOk (logAbsorbSnap ls sid).snap (snapView σ sid ls.stored)
      (logAbsorbSnap ls sid).prev (logAbsorbSnap ls sid).sents
      (logAbsorbSnap ls sid).uents := by
    show LogStoreOk ls.snap (snapView σ sid ls.stored) ls.prev ls.sents ls.uents
    cases Hs : ls.snap with
    | none => exact absurd Hs Hsn
    | some sid' => rw [Hs] at Hstore; exact Hstore
  have Hsat' : (logAbsorbSnap ls sid).sat = true → SatOk (snapView σ sid ls.stored)
      (logAbsorbSnap ls sid) := by
    intro h
    obtain ⟨Hsid, Hsipt⟩ := (logAbsorbSnap_sat _ _).1 h
    obtain ⟨Hpv, -, -⟩ : LogStoreOk (some sid) σ ls.prev ls.sents ls.uents := Hsid ▸ Hstore
    refine ⟨show ls.snap = some ls.prev by rw [Hpv]; exact Hsid, Hsipt, rfl, rfl,
      show sid = ls.prev from Hpv.symm, show uint.nat sid.index' = uint.nat ls.prev.index' by
        rw [Hpv], rfl, rfl⟩
  have Hfr' : FrOk (snapView σ sid ls.stored) (logAbsorbSnap ls sid) := by
    refine ⟨fun _ => ?_, Hfr.2.1, DtOk.of_eq Hfr.2.2 rfl rfl rfl⟩
    have e1 := uint_nat_eq ls.committed; have e2 := uint_nat_eq ls.inprogress
    have e4 := uint_nat_eq ls.prev.index'
    have := Happlied.1; have := Hipb.1; have Hoff := Hoffset
    show uint.nat sid.index' ≤ uint.nat ls.committed ∧ uint.nat sid.index' < uint.nat ls.inprogress ∧
      ∀ s, ls.snap = some s → ls.sip = false → uint.nat sid.index' < uint.nat s.index'
    refine ⟨by omega, by omega, fun s Hs Hsp => ?_⟩
    have Hpv : ls.prev = s := (Hs ▸ Hstore : LogStoreOk (some s) σ ls.prev ls.sents ls.uents).1
    rw [← Hpv]; exact Hsid.2 Hsp
  iapply ownRaftLog_intro (K := ls.ksn) (sn := ls.sn) l lv lv.storage' (snapView σ sid ls.stored) ls.snap ls.uents
    (logAbsorbSnap ls sid) rfl Hcm Hap Hidx Hnowrap Hstore' Hoffset Happlied
    Hpapplied Hcommitted Hapg Hip Hipb
    (fun h => absurd h Hsn) Happlying Hpaused Hasz Hamx Hstor Hpend' Hfl' Hsip Hsipn
    (fun h => absurd h (by simp [logAbsorbSnap])) Hq Hprel Hsat' Hfr' rfl rfl rfl rfl rfl
    $$ Hl HisStorage [HSt] Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger
  iapply lentStor_close (b := (logAbsorbSnap ls sid).lent) rfl; iexact HSt

end snapstor

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean).
proj_simps Perennial.EtcdGrove.logAcceptUnstable Perennial.EtcdGrove.logAppliedTo
  Perennial.EtcdGrove.logHanded Perennial.EtcdGrove.logAbsorbSnap
