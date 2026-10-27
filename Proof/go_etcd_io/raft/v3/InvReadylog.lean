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

section handout
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  ihave HStorage := lentStor_open Hlnt _ _ $$ HStorage
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
  have HflN : FlOk { σ with pend := nextUnstable ls } (logHanded ls) := by
    refine ⟨Hfl.1, Hfl.2.1, ?_, fun e0 He0 => ?_, fun h _ => (h Hs0).elim⟩
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
  isplitr [Happ]
  · iapply ownRaftLog_intro (K := ls.ksn) l lv lv.storage' { σ with pend := nextUnstable ls } ls.snap ls.uents
      (logHanded ls) rfl Hcm Hap Hidx Hnowrap Hstore' Hoffset Happlied Hpapplied
      Hcommitted Hssnap' Hapg Hip Hipb HpersistN Happlying Hpaused Hasz Hamx Hstor HpendN HflN Hsksn Hsip Hsipn
      Hlent Hq ⟨(fun h => by
        have := Hsipn Hs0; simp only [logHanded] at h; rw [this] at h; cases h),
        (fun h => absurd Hs0 h)⟩
      (fun h => absurd (Hsat h).1 (by rw [Hs0]; simp)) rfl rfl rfl rfl
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
  · obtain ⟨H1, H2, -, -, -⟩ := H
    refine ⟨H1, fun k hk => ?_, fun h => by simp at h, fun h => by simp at h,
      fun k hk hl => ⟨fun h => by simp at h, fun _ h => by simp at h⟩⟩
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
            sxt := sid.index' }

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

/-- (D22 S-d1b) **The storage lent** with a snapshot `Ready`: with a snapshot pending, nothing
unpersisted and the storage not yet lent, the application gets the storage, at a state with
nothing pending, the log's floor and a snapshot the node may send; the log records the batch the
`Ready` hands out as the application's to append (`logHanded`) and the storage as lent, keeping
the facts of the state it was lent at. -/
theorem ownRaftLog_lend (l : Loc) (ls : LogState) (Hunp0 : ls.unpersisted = [])
    (Hs0 : ls.snap ≠ none) (Hlt0 : ls.lent = false) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ownRaftLog l (logHanded { ls with lent := true, sat := false }) ∗
      ∃ σ, ownStorage ls.storage σ ∗
        ⌜σ.pend = [] ∧ σ.fl = ls.fl ∧
          (σ.ss.index' ≠ W64 0 → SnapTrip.mk σ.ss σ.scs σ.sal σ.sdat ∈ ls.ksn)⌝ := by
  iintro Hlog
  iNamed Hlog
  ihave HStorage := lentStor_open Hlt0 _ _ $$ HStorage
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
  have Hstore' : LogStoreOk ls.snap { σ with pend := nextUnstable ls } ls.prev ls.sents ls.uents := by
    cases Hs : ls.snap with
    | none => exact absurd Hs Hs0
    | some sid => rw [Hs] at Hstore; exact Hstore
  have Hssnap' : ls.snap = none →
      StoredSnapOk { σ with pend := nextUnstable ls } ls.committed ls.prev (ls.sents ++ ls.uents) :=
    fun h => absurd h Hs0
  have Hpersist' : ls.snap = none →
      LogPersistOk { σ with pend := nextUnstable ls } ls.sents ls.uents
        (uint.Z ls.inprogress - uint.Z lv.unstable'.offset') (nextUnstable ls)
        (ls.sents ++ ls.uents) := fun h => absurd h Hs0
  have Hpend' : PendLogOk { σ with pend := nextUnstable ls } (logHanded { ls with lent := true, sat := false }) :=
    ⟨rfl, fun h => absurd h Hs0⟩
  have Hfl' : FlOk { σ with pend := nextUnstable ls } (logHanded { ls with lent := true, sat := false }) := by
    refine ⟨Hfl.1, Hfl.2.1, Hfl.2.2.1, fun e0 He0 => ?_, fun _ h => by simp [logHanded] at h⟩
    have := Hhead e0 He0
    have := Hfl.2.2.1
    have := Hfl.2.1
    show uint.Z σ.fl < _
    rw [Hfl.1]; omega
  have Hprel' : SipOk (logHanded { ls with lent := true, sat := false }) lv.unstable'.offset' :=
    ⟨fun _ => LogPersistRel_full _ _ _, Hprel.2⟩
  isplitr [HStorage]
  · iapply ownRaftLog_intro (K := ls.ksn) l lv lv.storage' { σ with pend := nextUnstable ls }
      ls.snap ls.uents (logHanded { ls with lent := true, sat := false }) rfl Hcm Hap Hidx Hnowrap Hstore'
      Hoffset Happlied Hpapplied Hcommitted Hssnap' Hapg Hip Hipb Hpersist' Happlying Hpaused Hasz
      Hamx Hstor Hpend' Hfl' Hsksn Hsip Hsipn (fun _ => Hs0) Hq Hprel' (fun h => by cases h)
      rfl rfl rfl rfl
      $$ Hl HisStorage [] Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger
    iapply lentStor_lent (b := (logHanded { ls with lent := true, sat := false }).lent) rfl
  iexists σ
  rw [← Hstor]
  iframe HStorage
  ipureintro
  exact ⟨Hpend.1.trans Hunp0, Hfl.1, Hsksn⟩

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
  iapply ownRaftLog_intro l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
    Happlied Hpapplied Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying
    Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn Hsip Hsipn Hlent Hq Hprel Hsat rfl rfl rfl rfl $$ Hl
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
  iapply ownRaftLog_intro l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
    Happlied Hpapplied Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying
    Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn Hsip Hsipn Hlent Hq Hprel Hsat rfl rfl rfl rfl $$ Hl
    HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger

/-- (D22 S-d1b; S-d2, 2026-10-21) **The receipt absorbed**: the application returns the lent
storage at the state `σr` -- at a snapshot (`σr.prev = σr.ss`, a snapshot the node may send)
holding what the `Ready` asked to be stored (`ls.stored`), nothing pending, the log's floor. The
log takes it back (`logAbsorbSnap`), quiet: when `σr` is at the snapshot in progress, the storage
is recorded as at the pending snapshot (`sat`, `SatOk`), which the acknowledgement's arm turns
into the `sapp` window (`ownRaftLog_sapp`); otherwise (a second restore since the `Ready`) it is
shadowed again. (S-d1b put the log in the `sapp` window here, which would have had the raft
struct outside the quiet predicate between `RawNode.Advance`'s absorption and its step.) -/
theorem ownRaftLog_absorb_snap (l : Loc) (ls : LogState) (σr : StorState)
    (Hlt : ls.lent = true)
    (Hr : σr.prev = σr.ss ∧ σr.ents = ls.stored ∧ σr.pend = [] ∧ σr.fl = ls.fl)
    (Hk : σr.ss.index' ≠ W64 0 → SnapTrip.mk σr.ss σr.scs σr.sal σr.sdat ∈ ls.ksn)
    -- (D22 S-d4 item 3) `applying` at most the snapshot the storage is at (the loan's, `LoanOk`)
    (Happ : uint.Z ls.applying ≤ uint.Z σr.prev.index') :
    ⊢ ownRaftLog (GF := GF) l ls -∗ ownStorage ls.storage σr -∗
      ownRaftLog l (logAbsorbSnap ls σr.ss) := by
  iintro Hlog HSt
  iNamed Hlog
  iclear HStorage
  rw [← Hstor]
  obtain ⟨Hrp, Hre, Hrpend, Hrfl⟩ := Hr
  have Hsn : ls.snap ≠ none := Hlent Hlt
  have Hpend' : PendLogOk σr (logAbsorbSnap ls σr.ss) :=
    ⟨Hrpend, fun h => absurd h Hsn⟩
  have Hfl' : FlOk σr (logAbsorbSnap ls σr.ss) :=
    have Hext : StorExtOk σr (logAbsorbSnap ls σr.ss) := fun _ _ => by
      show uint.Z σr.ss.index' ≤ uint.Z σr.prev.index' + ((storApp σr σr.pend).length : Int) ∧
        uint.Z ls.applying ≤ uint.Z σr.ss.index'
      rw [← Hrp]
      exact ⟨by have := Happ; word, Happ⟩
    ⟨Hrfl, Hfl.2.1, Hfl.2.2.1, (fun e0 He0 => by rw [Hrpend] at He0; cases He0), Hext⟩
  have Hstore' : LogStoreOk (logAbsorbSnap ls σr.ss).snap σr
      (logAbsorbSnap ls σr.ss).prev (logAbsorbSnap ls σr.ss).sents
      (logAbsorbSnap ls σr.ss).uents := by
    show LogStoreOk ls.snap σr ls.prev ls.sents ls.uents
    cases Hs : ls.snap with
    | none => exact absurd Hs Hsn
    | some sid => rw [Hs] at Hstore; exact Hstore
  have Hsat' : (logAbsorbSnap ls σr.ss).sat = true → SatOk σr (logAbsorbSnap ls σr.ss) := by
    intro h
    obtain ⟨Hsid, Hsipt⟩ := (logAbsorbSnap_sat _ _).1 h
    obtain ⟨Hpv, -, -⟩ : LogStoreOk (some σr.ss) σ ls.prev ls.sents ls.uents := Hsid ▸ Hstore
    refine ⟨show ls.snap = some ls.prev by rw [Hpv]; exact Hsid, Hsipt, rfl, rfl,
      show σr.prev = ls.prev by rw [Hrp, Hpv], show σr.ss = ls.prev from Hpv.symm, Hre, Hrpend⟩
  iapply ownRaftLog_intro (K := ls.ksn) l lv lv.storage' σr ls.snap ls.uents
    (logAbsorbSnap ls σr.ss) rfl Hcm Hap Hidx Hnowrap Hstore' Hoffset Happlied
    Hpapplied Hcommitted (fun h => absurd h Hsn) Hapg Hip Hipb
    (fun h => absurd h Hsn) Happlying Hpaused Hasz Hamx Hstor Hpend' Hfl' Hk Hsip Hsipn
    (fun h => absurd h (by simp [logAbsorbSnap])) Hq Hprel Hsat' rfl rfl rfl rfl
    $$ Hl HisStorage [HSt] Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger
  iapply lentStor_close (b := (logAbsorbSnap ls σr.ss).lent) rfl; iexact HSt

end snapstor

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean).
proj_simps Perennial.EtcdGrove.logAcceptUnstable Perennial.EtcdGrove.logAppliedTo
  Perennial.EtcdGrove.logHanded Perennial.EtcdGrove.logAbsorbSnap
