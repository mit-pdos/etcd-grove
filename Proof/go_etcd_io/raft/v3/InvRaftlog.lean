/-
Port of `election_proof/inv_raftlog.v` (at 857d09190): the raft log.

`ownRaftLog l` is full ownership of the `raftLog` struct at `l`, together with
everything that hangs off it: the `unstable` suffix's entry slice and the `Storage`
behind the stable prefix.

### What the predicate guarantees

It exposes the log as an **entry list** -- a compaction boundary `prev` (an `entryID`,
the last index the log has discarded the payload of but still knows the term of) plus
the entries after it, split into the stable prefix `sents` (in `storage`) and the
unstable suffix `uents` (in `unstable.entries`). The whole log is `sents ++ uents` at
indices `prev.index+1 ...`, and:

- `LogIndicesOk`: the indices are contiguous from `prev.index+1`, and
  `prev.index + |sents| + |uents| + 1 < 2^64` so nothing wraps. Both are needed to show
  `lastEntryID` cannot hit its `Panicf`: the `Panicf` fires when `term(lastIndex())`
  errors, and an index that wrapped would come back `ErrCompacted`.

  **The constant may not be tightened.** On 2026-09-20 this was changed to `2^63` --
  `raftLog.slice` wants `|sents| + |uents| < 2^63` so that `extend`'s
  `need := len(dst) + len(vals)` cannot overflow a Go `int` -- and changed back the
  same day, because `2^63` makes `raft.wp_appendEntry` **unprovable**. The argument is
  worth keeping, since it applies to any tightening:

  `append` grows `uents`, so this conjunct has to be *re-established* at the longer
  length. A bound that the predicate merely *carries* can never do that: from
  `last + 1 < C` one has to conclude `last + |ents| + 1 < C`, which is false for any
  `C`. So after an append the bound can only be *derived*, from facts that survive the
  append, and there are exactly two:

    - `prev.index + |sents|`, which `append` does not touch, is bounded by
      `isStorage`'s `Hbounded` clause (`InvStorage.lean`): `< 2^61`.
    - `|uents|` is the length of a Go slice, and Perennial's `ownSlice_len` gives
      `< 2^63` for *whatever slice the `append` returns* -- this is the only bound on
      the suffix, and it is a free one, re-derived rather than carried.

  Their sum gives `last < 2^61 + 2^63`, which clears `2^64` with room for a batch of up
  to `2^61` entries (the premise `appendEntry` takes) and does **not** clear `2^63`. A
  "the log fits in memory" assumption below `2^63` would therefore have to be carried,
  which is exactly what cannot be preserved. If `extend` needs one, it has to come from
  the slice `slice` returns (`hi - lo` at the `slice` call, plus `Hbounded`) or from a
  Perennial-level bound on slice lengths -- not from here. See
  `spec_raft__appendEntry.v`, "The no-wrap gap, and how it is closed".
- `unstable.offset = prev.index + |sents| + 1` -- the unstable suffix starts exactly
  where storage ends. This is what makes `lastIndex()` agree with itself in both of its
  branches (the `unstable` one and the `storage` fallback).
- (until 2026-10-13) no entry anywhere in the log was a configuration change
  (`HnoConfChange`, `∀ e ∈ sents ++ uents, e.Type' = EntryNormal`), the scope assumption
  that no configuration change is ever requested. Since reconfiguration stage D the log
  holds conf-change entries as data (`hasUnappliedConfChanges` looks for them), and only
  the configuration in use is fixed (`ownRaftPhys cfg`).
- `prev.index <= committed`, `applied <= committed <= prev.index + |sents| + |uents|`,
  and `prev.index <= applied` when no snapshot is pending: raft compacts only up to
  `applied` and commits only what it has. A received snapshot moves `prev` and
  `committed` to its index and leaves `applied` below it until the application applies
  it.
- **a pending snapshot** (`LogState.snap`, since 2026-10-02): when `unstable.snapshot`
  is set, the log starts at the snapshot's id with no stable part, and the `Storage` is
  shadowed (`LogStoreOk`).

### raft v3.7 (stage R3 of the retarget, 2026-10-15)

The shapes are the old ones with the entries' element type changed (`notes/raft-retarget-plan.md`,
D2; `notes/decisions.md`, "The log layer over read-only entries: the storage contract of raft
v3.7"): `unstable.entries` is a `[]*pb.Entry`, held as `entsRO uv.entries' us.ents`
(`InvPbLog.lean`: the pointers `↦*□` and each pointer a persistent `entRO` log entry, where the
old proof had `uv.entries' ↦*□ us.ents` of gogoproto values) with its capacity `ownSliceCap Loc`
owned as before; `LogState`, `UnstableSt` keep their `List EntryM` and every pure fact. The
pending snapshot (`unstable.snapshot`) is a fresh clone (`unstable.restore`, `log_unstable.go:196`)
that nothing writes after -- `nextSnapshot` and `raftLog.snapshot` clone it again
(`log_unstable.go:114`, `log.go:295`) -- so the log holds it read-only, `ownSnapM p □ sv`
(`ownSnap`, `pendKsn`, persistent as before; until the retarget `p ↦□ sv` of a value with its
`ConfState` slices `ownCSL`). Since an entry is read-only once appended and a page `slice`
returns is the caller's for good, the "page out" shapes need no wand.

### Scope assumptions written into the predicate

None since 2026-10-13. (Until then: no configuration change is ever requested,
`HnoConfChange`; until 2026-10-02 also no snapshot is ever received,
`unstable.snapshot = nil`, which `LogState.snap` replaced when `MsgSnap` came into
scope.)

Note what is **not** assumed: that `term(lastIndex())` succeeds. That is the fact
`lastEntryID` needs, and it is *proved* here from the conjuncts above plus the
`Storage` contract. Assuming it directly would be the `raft.wp_appendEntry` mistake
again -- an assumption about raft's own code in a place where it can be derived.

### Structure

`ownRaftLog l ls` is the one predicate, indexed by `ls : LogState` (below): the entry
list, `committed`, `applied` and the pending snapshot. The entry list is in the index
rather than existential inside because `raftLog.term` calls `firstIndex` and
`lastIndex` on itself, so the proof has to re-seal and re-open the predicate
mid-function and needs the split to come back unchanged. `ownUnstable` is the predicate
for the embedded `unstable` struct.

The `Storage` interface contract lives in `InvStorage.lean`.

Lean notes: the Rocq `Ltac split_unstable l lv` is `raftLog_split_unstable` (until
2026-10-08 a tactic macro `split_unstable`; see that lemma), which `raftLog_lend_unstable`
and the macro `lend_unstable` use. The Rocq `own_raftLog_core` (until 2026-10-09
`ownRaftLogCore`) is inlined into `ownRaftLog`, and its five state arguments are `ls`'s
fields. Rocq `Forall P l`
is `∀ e ∈ l, P e`, so `Forall_sublist_of` is `forall_sublist_of`; `own_slice_same_ptr_len`
is `ownSlice_same_ptr_len`. A Rocq lemma `P -∗ Q -∗ R` is `⊢ P -∗ Q -∗ R`. The Rocq
`seal` of `own_snap` is an `@[irreducible]` definition with `ownSnap_unseal`. The Rocq
`Ltac reseal_raftLog` is the tactic macro `reseal_raftLog` (same hypothesis names).
`plog_term_at_truncate_append_below` is `plogTermAt_truncateAppend_below`.
`ownRaftLog_pure` (no Rocq counterpart) is the common proof of the `ownRaftLog_*`
read-out lemmas. `stor_app`, `log_persist_ok`, `log_trunc_inprogress` are `storApp`,
`LogPersistOk`, `logTruncInprogress`. In Rocq `a ≤ b ≤ c` is `a ≤ b ∧ b ≤ c`, written
out here.
-/
module

public import Proof.go_etcd_io.raft.v3.InvStorage
public import Proof.go_etcd_io.raft.v3.InvPbSnapSet
public import Proof.go_etcd_io.raft.v3.InvLogger
public import Proof.go_etcd_io.raft.v3.SpecResults

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! `LogState`, the log's abstract state, is defined in `Defs.lean`: the physical raft
state `NState` contains one. -/

/-- The log's entries are numbered consecutively from `prev.index + 1`. -/
def LogIndicesOk [FfiSyntax] (prev : entryID) (ents : List EntryM) : Prop :=
  ∀ (k : Nat) (e : EntryM), ents[k]? = some e →
    uint.Z e.Index' = uint.Z prev.index' + ((k + 1 : Nat) : Int)

def EntryNormal : w32 := W32 0

/-- The state of an `unstable` struct as its specs speak of it (`ownUnstable`): the
suffix's entries `ents`, which start at index `offset`; `inprogress`
(`u.offsetInProgress`), below which they have been handed to the application; and the
pending snapshot's id `snap` (`ownSnap`). -/
structure UnstableSt [FfiSyntax] where
  ents : List EntryM
  offset : w64
  inprogress : w64
  snap : Option entryID
  /-- (2026-10-15, stage S) the log's `ksn`, ghost: the pending snapshot is in it (`pendKsn`) -/
  ksn : List SnapTrip
  /-- (D22 S-d1, 2026-10-20) `u.snapshotInProgress` -/
  sip : Bool := false

/-- (D22 S-d1, 2026-10-20) Whether `stableSnapTo(i)` hits: a snapshot is pending at index `i`
(`u.snapshot != nil && u.snapshot.Metadata.Index == i`). -/
def snapHit [FfiSyntax] (snap : Option entryID) (i : w64) : Bool :=
  match snap with
  | some sid => decide (sid.index' = i)
  | none => false

theorem snapHit_none [FfiSyntax] (i : w64) : snapHit none i = false := rfl

/-- (D22 S-d1) `unstable.stableSnapTo(i)`: on a hit the snapshot is dropped and no longer in
progress; otherwise nothing changes. -/
def unstableSnapTo [FfiSyntax] (us : UnstableSt) (i : w64) : UnstableSt :=
  if snapHit us.snap i then { us with snap := none, sip := false } else us

/-- The state at which a `raftLog` at struct value `lv` and state `ls` hands its
`unstable` field to an `unstable` method: the suffix `ls.uents`, starting at the
field's `offset`, with `ls.inprogress` and the pending snapshot `ls.snap`. Named, with
projection lemmas (`proj_simps`, end of file), so that call sites pass a variable-built
record rather than a literal (since 2026-10-09; until then each call wrote
`⟨uents, lv.unstable'.offset', lv.unstable'.offsetInProgress', snap⟩`). Reducible, so
that the reducible `rfl`/`assumption` of `reseal_raftLog` see through it to the log's
fields; `omega` does not, and a proof hands it projections rewritten by `simp only
[unstableOf]` (or uses `word`, which rewrites them with the projection lemmas). -/
abbrev unstableOf [FfiSyntax] (lv : raftLog) (ls : LogState) : UnstableSt :=
  { ents := ls.uents, offset := lv.unstable'.offset', inprogress := ls.inprogress,
    snap := ls.snap, ksn := ls.ksn, sip := ls.sip }

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## The log -/

/-- A `Logger` interface value that is non-nil and satisfies `isLogger`. One persistent
assertion (rather than `∃ lg, ⌜x = ok lg⌝ ∗ isLogger lg` spread over the predicate) so
that `iframe` re-seals it as a unit: with two loggers' `isLogger`s in context it
otherwise picks the wrong one. -/
def isLoggerVal (x : GoInterface) : IProp GF :=
  iprop(∃ lg, ⌜x = interface.ok lg⌝ ∗ isLogger lg)

instance isLoggerVal_pers (x : GoInterface) : Persistent (isLoggerVal (GF := GF) x) := by
  unfold isLoggerVal; infer_instance

theorem isLoggerVal_open (x : GoInterface) :
    isLoggerVal (GF := GF) x ⊢ ∃ lg, ⌜x = interface.ok lg⌝ ∗ isLogger lg := by
  unfold isLoggerVal; exact .rfl

/-! Besides the struct itself, `ownRaftLog l ls` (below) owns the `Storage` behind the
log, at a state `σ : StorState` it keeps existential, and the unstable entries. (Until
2026-10-09 these were a separate `ownRaftLogCore lv snap prev sents uents pend`, with
the storage as three existentials `sprev stored ss`; notes/decisions.md, "Predicate
indices".) The unstable entries are held read-only, as in `ownUnstable` and for the same
reason.

**`sents` is the *visible* stable part** (since 2026-10-01). The `Storage` holds
`σ.ents`, of which `sents` is a prefix: when `unstable.truncateAndAppend` takes its
`fromIndex <= u.offset` arm (a `MsgApp` that conflicts with an entry already handed to
storage), the new unstable suffix starts at `fromIndex` and *shadows* the tail of
`σ.ents` from there on -- Go never deletes it from storage, it is just no longer read:
every read of the stable part (`term`, `slice`) is below `unstable.offset`.
`LogStoreOk` says the shadowing needs a non-empty suffix: with `uents = []`,
`lastIndex()` falls back to `storage.LastIndex()`, which is `prev.index + |σ.ents|`,
so the two must agree.

The two `Logger`s (`l.logger`, and `l.unstable.logger`, which `newLogWithSize` sets to
the same value) are carried so that the `Infof`s of `findConflict` and
`unstable.truncateAndAppend` can be stepped.

### A pending snapshot (since 2026-10-02)

`unstable.restore(s)` (`log_unstable.go:188`) stores `&s` in `u.snapshot`, the address
of `restore`'s by-value parameter -- a fresh heap cell nothing else points to. Nothing
writes through it until `stableSnapTo` clears the field (`MsgStorageAppendResp`, out of
scope), and `raftLog.snapshot()` reads it by value, so the log holds it read-only.
`ownSnap p snap` says what `p = u.snapshot` is: `nil` for `none`, and for `some sid` a
pointer to a `Snapshot` whose metadata is `sid`, with its `ConfState.Voters` slice held
read-only too (since 2026-10-03: `raftLog.snapshot()` returns the snapshot by value, so
the slice it hands `maybeSendSnapshot` is this one). -/
def ownSnapDef (p : Loc) (snap : Option entryID) : IProp GF :=
  match snap with
  | none => iprop(⌜p = null⌝)
  | some sid =>
      iprop(∃ (sv : SnapshotM), ownSnapM p DFrac.discard sv ∗
        ⌜sv.Metadata'.Index' = sid.index' ∧ sv.Metadata'.Term' = sid.term'⌝)

/-- Sealed: unfolded, a `none`/`some` instance reduces to its body, and the re-seal
lemmas (`ownRaftLog_intro`) can then no longer infer `snap` from the hypothesis.
`ownSnap_None`/`ownSnap_Some` open it. -/
@[irreducible] def ownSnap (p : Loc) (snap : Option entryID) : IProp GF := ownSnapDef p snap

theorem ownSnap_unseal (p : Loc) (snap : Option entryID) :
    ownSnap (GF := GF) p snap = ownSnapDef p snap := by
  with_unfolding_all rfl

theorem ownSnap_None (p : Loc) : ownSnap (GF := GF) p none ⊣⊢ ⌜p = null⌝ := by
  rw [ownSnap_unseal]; exact .rfl

theorem ownSnap_Some (p : Loc) (sid : entryID) :
    ownSnap (GF := GF) p (some sid) ⊣⊢
    ∃ (sv : SnapshotM), ownSnapM p DFrac.discard sv ∗
      ⌜sv.Metadata'.Index' = sid.index' ∧ sv.Metadata'.Term' = sid.term'⌝ := by
  rw [ownSnap_unseal]; exact .rfl

/-- The case split on a record's `snap` field that leaves the goal alone (`cases Hs :
us.snap` would rewrite `us.snap` in it, and the `ownSnap` re-sealing `ownUnstable u us`
then no longer matches); `ownSnap_of_eq_none`/`ownSnap_of_eq_some` open `ownSnap` at the
equation. So the record `us` stays a variable. -/
theorem snap_some_or_none (snap : Option entryID) : (∃ sid, snap = some sid) ∨ snap = none := by
  cases snap <;> simp

theorem ownSnap_of_eq_none {p : Loc} {snap : Option entryID} (Hs : snap = none) :
    ownSnap (GF := GF) p snap ⊢ ⌜p = null⌝ := by
  subst Hs; exact (ownSnap_None p).1

theorem ownSnap_of_eq_some {p : Loc} {snap : Option entryID} {sid : entryID}
    (Hs : snap = some sid) :
    ownSnap (GF := GF) p snap ⊢
    ∃ (sv : SnapshotM), ownSnapM p DFrac.discard sv ∗
      ⌜sv.Metadata'.Index' = sid.index' ∧ sv.Metadata'.Term' = sid.term'⌝ := by
  subst Hs; exact (ownSnap_Some p sid).1

instance ownSnap_pers (p : Loc) (snap : Option entryID) :
    Persistent (ownSnap (GF := GF) p snap) := by
  rw [ownSnap_unseal]; cases snap <;> unfold ownSnapDef <;> infer_instance

/-- The snapshots a log built on the storage at `σ` may send at first (2026-10-15, stage S): the
storage's, unless it is the empty one. -/
def initKsn (σ : StorState) : List SnapTrip :=
  if σ.ss.index' = W64 0 then [] else [SnapTrip.mk σ.ss σ.scs σ.sal σ.sdat]

theorem initKsn_mem (σ : StorState) (h : σ.ss.index' ≠ W64 0) :
    SnapTrip.mk σ.ss σ.scs σ.sal σ.sdat ∈ initKsn σ := by
  unfold initKsn; rw [ite_eq_right h]; exact List.mem_singleton_self _

/-- (D22 S-b′3, 2026-10-20) The storage's initial snapshot, if any, is certified in its registry:
what `newLogWithSize` (and so `newRaft`, `NewRawNode`, `RestartNode`, `StartNode`) asks of the
storage it is given, for `ownRaftLog`'s `Hkcert` at `initKsn σ`. -/
def initKsnCert (st : Storage) (σ : StorState) : IProp GF :=
  iprop([∗list] k ∈ initKsn σ, storCert st k)

instance initKsnCert_pers (st : Storage) (σ : StorState) :
    Persistent (initKsnCert (GF := GF) st σ) := by
  unfold initKsnCert; infer_instance

/-- A storage without a snapshot needs no certificate. -/
theorem initKsnCert_zero (st : Storage) (σ : StorState) (h : σ.ss.index' = W64 0) :
    ⊢ initKsnCert (GF := GF) st σ := by
  unfold initKsnCert initKsn
  rw [if_pos h]
  iapply (BigSepL.bigSepL_nil (Φ := fun _ k => storCert (GF := GF) st k)).2
  iempintro

/-- The snapshots the node may send (2026-10-15, stage S): the pending snapshot, if any, is one
of them (`K`, the log's `ksn`) -- what `raftLog.snapshot` returns of it, the snapshot `p`
points to with the lists behind its `ConfState`, is in `K`. -/
def pendKsn (p : Loc) (snap : Option entryID) (K : List SnapTrip) : IProp GF :=
  iprop(□ ∀ (sid : entryID), ⌜snap = some sid⌝ -∗ ∃ (sv : SnapshotM),
    -- (D22 S-d4 item 4) every pointer field set: `raft.restore`'s `EnsureSnapshot`, kept by the
    -- clone (`proto.CloneSnapshot.spec`'s fourth clause)
    ownSnapS p DFrac.discard sv ∗ ⌜snapId sv = sid⌝ ∗
    ⌜snapTrip sv sv.Metadata'.ConfState'.lists ∈ K⌝)

instance pendKsn_pers (p : Loc) (snap : Option entryID) (K : List SnapTrip) :
    Persistent (pendKsn (GF := GF) p snap K) := by
  unfold pendKsn; infer_instance

/-- With no snapshot pending, nothing to say. -/
theorem pendKsn_none (p : Loc) (K : List SnapTrip) : ⊢ pendKsn (GF := GF) p none K := by
  unfold pendKsn
  imodintro
  iintro %sid %h
  cases h

/-! ## The `unstable` struct

`ownUnstable u us` owns the `unstable` at `u` -- in the development always the
`unstable` field of a `raftLog` -- at the state `us : UnstableSt`, together with its
entry slice. The Goose value is existential: `offset` and `offsetInProgress` are the
record's, `snapshot` is `ownSnap` of the record's `snap`, and `logger` is a `Logger`
(`isLoggerVal`) for the `Infof`s of `stableTo` and `truncateAndAppend`. (Until
2026-10-08 it was `ownUnstable u uv uents`, indexed by the Goose value and the entries,
and the specs took the snapshot as a separate `ownSnap uv.snapshot snap` and the logger
as `uv.logger = ok ulg ∗ isLogger ulg`; notes/decisions.md, "Predicate indices".)

**The entries are held read-only** (`↦*□`); only the slice's capacity slack is owned
outright. That is what the Go code guarantees (`log_unstable.go`, upamanyus/etcd-raft
531b20c): no statement ever writes an element of `u.entries` in place. Every assignment
to `u.entries` re-slices it (`stableTo`), copies it into a new array
(`shrinkEntriesArray`), adopts the caller's slice, or appends -- in place only past
`len`, into the slack; the truncating case appends to `u.slice(...)`, which caps its
result "so that an append will reallocate and copy this slice instead of corrupting
the neighbouring u.entries" (`log_unstable.go:228-234`). So a sub-slice
`unstable.slice` hands out is the caller's for good, with nothing to give back.
(`wp_slice_append_persistent`, in `slice.v`, is the `append` this needs.) (Until
2026-09-29 the entries were owned outright and `unstable.slice` *lent* a sub-slice,
tracked by a `page` argument here; until 2026-09-23 the `unstable` specs were stated on
the raw `u ↦ uv ∗ uv.entries ↦* uents`.) -/
def ownUnstable (u : Loc) (us : UnstableSt) : IProp GF :=
  iprop(∃ (uv : unstable),
  "Hu" ∷ u ↦ uv ∗
  "Hents_cap" ∷ ownSliceCap Loc uv.entries' (DFrac.own 1) ∗
  "Hents" ∷ entsRO uv.entries' us.ents ∗
  "#Hsnap" ∷ ownSnap uv.snapshot' us.snap ∗
  -- (2026-10-15, stage S)
  "#Hpksn" ∷ pendKsn uv.snapshot' us.snap us.ksn ∗
  "#Hlogger" ∷ isLoggerVal uv.logger' ∗
  "%Hoff" ∷ ⌜uv.offset' = us.offset⌝ ∗
  "%Hoip" ∷ ⌜uv.offsetInProgress' = us.inprogress⌝ ∗
  -- (D22 S-d1)
  "%Hsip" ∷ ⌜uv.snapshotInProgress' = us.sip⌝)

/-- Close `ownUnstable` at the state the pieces denote. The pure premise is last, so
that `iapply ownUnstable_intro $$ Hu Hents_cap Hents Hsnap Hlogger` fixes the value, the
entries and the snapshot from the hypotheses and leaves the two `offset`s as the
goal. -/
theorem ownUnstable_intro (u : Loc) (uv : unstable) (ents : List EntryM)
    (off ip : w64) (snap : Option entryID) (K : List SnapTrip) (sip : Bool) :
    ⊢ (u ↦ uv : IProp GF) -∗ ownSliceCap Loc uv.entries' (DFrac.own 1) -∗
      entsRO uv.entries' ents -∗ ownSnap uv.snapshot' snap -∗ pendKsn uv.snapshot' snap K -∗
      isLoggerVal uv.logger' -∗
      ⌜uv.offset' = off ∧ uv.offsetInProgress' = ip ∧ uv.snapshotInProgress' = sip⌝ -∗
      ownUnstable u ⟨ents, off, ip, snap, K, sip⟩ := by
  iintro Hu Hents_cap #Hents #Hsnap #Hpksn #Hlogger %H
  unfold ownUnstable
  iexists uv
  simp only [named]
  iframe Hu Hents_cap Hents Hsnap Hpksn Hlogger
  ipureintro
  exact H

/-- Open `ownUnstable u us` in the proof of an `unstable` method with the value's
`offset` and `offsetInProgress` replaced by the record's: the struct is at
`{ uv with offset' := us.offset, offsetInProgress' := us.inprogress }`, so a load of
either field gives `us.offset`/`us.inprogress`, the atoms the spec's premises are
stated in, and `us` stays a variable (CLAUDE.md, "Records"). -/
theorem ownUnstable_open (u : Loc) (us : UnstableSt) :
    ⊢ ownUnstable u us -∗ ∃ (uv : unstable),
      (u ↦ { uv with offset' := us.offset, offsetInProgress' := us.inprogress,
                     snapshotInProgress' := us.sip } : IProp GF) ∗
      ownSliceCap Loc uv.entries' (DFrac.own 1) ∗ entsRO uv.entries' us.ents ∗
      ownSnap uv.snapshot' us.snap ∗ pendKsn uv.snapshot' us.snap us.ksn ∗
      isLoggerVal uv.logger' := by
  iintro Hun
  iunfold ownUnstable at Hun
  iNamed Hun
  iexists uv
  rw [← Hoff, ← Hoip, ← Hsip]
  iframe Hu Hents_cap Hents Hsnap Hpksn Hlogger

/-- How the visible log relates to what `Storage` holds, by whether a snapshot is
pending. The storage holds `σ.ents` after `σ.prev` (`ownStorage`).

- No snapshot: `σ.prev` is the log's `prev`, and `sents` is a prefix of `σ.ents` --
  all of it when the unstable suffix is empty (see `ownRaftLog`).
- A pending snapshot `sid`: the log starts at `sid` with no stable part (`sents = []`);
  the storage is **shadowed**. It still holds its old boundary and entries, and nothing
  reads them while the snapshot is pending: `firstIndex`/`lastIndex` answer from the
  snapshot arms of `unstable.maybeFirstIndex`/`maybeLastIndex`, `term` answers
  `i < sid.index` with `ErrCompacted` (its `firstIndex` test) and `i = sid.index` from
  `maybeTerm`, and `slice`'s range starts at `firstIndex = offset`, above every stored
  index it could ask `Storage.Entries` for. `sid.index` is non-zero (the snapshot's
  index is above the commit index it replaced) and below `2^61`, the bound
  `isStorage`'s `Hbounded` gives an unshadowed storage: once the snapshot is applied it
  becomes the storage's boundary, and `appendEntry`'s no-wrap argument needs it
  meanwhile. -/
def LogStoreOk (snap : Option entryID) (σ : StorState)
    (prev : entryID) (sents uents : List EntryM) : Prop :=
  match snap with
  | none => σ.prev = prev ∧ sents <+: σ.ents ∧ (uents = [] → sents = σ.ents)
  | some sid => prev = sid ∧ sents = [] ∧
      (0 < uint.Z sid.index' ∧ uint.Z sid.index' < 2^61)

/-- The storage's own snapshot `σ.ss` (`ownStorage`'s last index; `Storage.Snapshot`
returns it, `InvStorage.lean`) is of a committed prefix of the log (2026-10-03): its
index is `0` (no snapshot yet), or at or below `committed` with the log having
`ss.term` at `ss.index` (possibly as its base). Kept only while no snapshot is pending
-- a pending one shadows the storage, and `raftLog.snapshot()` then returns it instead.

This is how `maybeSendSnapshot`'s `MsgSnap` gets `SnapOk`'s commit bound and log fact
(`Protocol/Model.lean`). It is raft's invariant, not a `Storage` property: true at
`newLogWithSize` by its premise on the initial storage (`ss` is the boundary, or
empty), and preserved because the storage never changes in scope, `committed` only
grows, and an `append` only rewrites entries above `committed`
(`plogTermAt_truncateAppend_below`). -/
def StoredSnapOk (σ : StorState) (cm : w64) (prev : entryID) (es : List EntryM) :
    Prop :=
  uint.Z σ.ss.index' = 0 ∨
  (uint.Z σ.ss.index' ≤ uint.Z cm ∧ plogTermAt prev es σ.ss.index' = some σ.ss.term')

omit [GoGlobalContext] in
theorem StoredSnapOk_commit (σ : StorState) (cm cm' : w64) (prev : entryID)
    (es : List EntryM) (Hle : uint.Z cm ≤ uint.Z cm') (H : StoredSnapOk σ cm prev es) :
    StoredSnapOk σ cm' prev es := by
  rcases H with H | ⟨H1, H2⟩
  · exact .inl H
  · exact .inr ⟨by omega, H2⟩

omit [GoGlobalContext] in
/-- An `append` keeps the log's terms below the batch. -/
theorem plogTermAt_truncateAppend_below (b : entryID) (es ents : List EntryM)
    (e0 : EntryM) (i t : w64) (H0 : ents[0]? = some e0)
    (Hlt : uint.Z i < uint.Z e0.Index') (Ht : plogTermAt b es i = some t) :
    plogTermAt b (plogTruncateAppend b es ents) i = some t := by
  cases ents with
  | nil => simp at H0
  | cons e0' ents' =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at H0
    subst H0
    unfold plogTermAt at Ht ⊢
    unfold plogTruncateAppend
    by_cases h1 : uint.Z i < uint.Z b.index'
    · simp [h1] at Ht
    by_cases h2 : uint.Z i = uint.Z b.index'
    · simpa [h1, h2] using Ht
    simp only [h1, h2, ite_false] at Ht ⊢
    cases He : es[(uint.Z i - uint.Z b.index' - 1).toNat]? with
    | none => rw [He] at Ht; simp at Ht
    | some e =>
      have Hlen := (List.getElem?_eq_some_iff.1 He).1
      rw [He] at Ht
      rw [List.getElem?_append_left (by rw [List.length_take]; omega),
        List.getElem?_take_of_lt (by omega), He]
      exact Ht

/-! ## The storage handshake (2026-10-05)

`storApp σ pend` (`InvStorage.lean`, since 2026-10-10) is what a `Storage` at `σ`
holds once the entries `pend` are appended to it the way `MemoryStorage.Append` does.
The application appends the entries a `Ready` handed out (`LogState.unpersisted`,
which is the storage's pending batch `σ.pend`); `acceptUnstable` hands the right to do
so out (the storage's hand-out law) and `ownRaftLog_absorb` takes the receipt back. -/

/-- The persistence invariant (`Hpersist` below), with no snapshot pending: the stable
part followed by the unstable entries already handed to the application
(`offsetInProgress - offset` of them) is a prefix of what the storage holds once the
unpersisted entries `pend` are appended -- everything raft has handed out is persisted,
or is exactly `pend` -- *exactly* when all of the unstable suffix has been handed out
(the application's truncating append leaves nothing behind it), and with no unstable
entries nothing is waiting to be persisted. `unstable.stableTo` (an `Advance`) moves
stable exactly entries this says are persisted, and the equality is what gives
`LogStoreOk`'s `sents = stored` when it empties the suffix. And (2026-10-10) what the
storage then holds is the ghost `LogState.stored`: a truncating `MsgApp` lowers
`offsetInProgress` below entries the storage still holds, and the acknowledgement
`Advance` steps next may move them stable because they agree with the log
(`StableOk`, `InvReadylog.lean`). -/
def LogPersistOk (σ : StorState)
    (sents uents : List EntryM) (ipo : Int) (pend stored : List EntryM) : Prop :=
  (sents ++ uents.take ipo.toNat) <+: storApp σ pend ∧
  (ipo.toNat = uents.length → sents ++ uents = storApp σ pend) ∧
  (uents = [] → pend = []) ∧
  storApp σ pend = stored

omit [GoGlobalContext] in
/-- (D19i part 1) An entry of the storage's view below `offsetInProgress` (`ipo` entries past the
stable part) and below the pending batch is the log's: `LogPersistOk` says the storage holds the
log there once the batch is appended, and below the batch the view agrees with that. What makes
a snapshot the application took at or below the floor an entry of the log
(`raftLog.snapshot`). -/
theorem termAt_log_below (σ : StorState) (sents uents : List EntryM) (ipo : Int)
    (pend stored : List EntryM) (idx t : w64)
    (Hp : LogPersistOk σ sents uents ipo pend stored)
    (Hipo : 0 ≤ ipo ∧ ipo ≤ uents.length)
    (Hge : uint.Z σ.prev.index' ≤ uint.Z idx)
    (Hlt : uint.Z idx < uint.Z σ.prev.index' + (sents.length : Int) + ipo + 1)
    (Hab : ∀ e0, pend.head? = some e0 → uint.Z idx < uint.Z e0.Index')
    (Ht : termAt σ.prev σ.ents idx = some t) :
    plogTermAt σ.prev (sents ++ uents) idx = some t := by
  unfold termAt at Ht
  by_cases Hb : uint.Z idx = uint.Z σ.prev.index'
  · rw [if_pos Hb] at Ht
    cases Ht
    unfold plogTermAt
    simp [Hb]
  rw [if_neg Hb] at Ht
  cases He : σ.ents[(uint.Z idx - uint.Z σ.prev.index' - 1).toNat]? with
  | none => rw [He] at Ht; cases Ht
  | some e =>
    rw [He] at Ht
    simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at Ht
    subst Ht
    have Hklt := (List.getElem?_eq_some_iff.1 He).1
    -- the storage, once the batch is appended, has `e` there too
    have Happ : (storApp σ pend)[(uint.Z idx - uint.Z σ.prev.index' - 1).toNat]? = some e := by
      cases pend with
      | nil => exact He
      | cons e0 rest =>
        have := Hab e0 rfl
        simp only [storApp]
        rw [List.getElem?_append_left (by rw [List.length_take]; omega),
          List.getElem?_take_of_lt (by omega)]
        exact He
    -- and so does the log
    have Hpre := Hp.1
    rw [List.prefix_iff_eq_take] at Hpre
    have HL : (sents ++ uents.take ipo.toNat)[(uint.Z idx - uint.Z σ.prev.index' - 1).toNat]?
        = some e := by
      rw [Hpre, List.getElem?_take_of_lt (by simp only [List.length_append, List.length_take]; omega)]
      exact Happ
    have Hlog : (sents ++ uents)[(uint.Z idx - uint.Z σ.prev.index' - 1).toNat]? = some e := by
      rw [← HL]
      by_cases Hs : (uint.Z idx - uint.Z σ.prev.index' - 1).toNat < sents.length
      · rw [List.getElem?_append_left Hs, List.getElem?_append_left Hs]
      · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
          List.getElem?_take_of_lt (by omega)]
    exact plogTermAt_lookup _ _ _ _ e Hlog (by omega)

/-- The storage's pending batch is the log's `unpersisted` (2026-10-10), and with no
snapshot pending it starts at or above `unstable.offset` (`prev.index + |sents| + 1`):
it is the in-progress part of the unstable suffix a `Ready` handed out, and only a
truncating `append` moves the offset, down. Every read of the stable part is below the
offset (`term`, `slice`), so it is below the batch, as the storage's triples ask
(`PendFrom`); `lastIndex()` reads the storage only with no unstable entries, and then
nothing is pending (`LogPersistOk`). -/
def PendLogOk (σ : StorState) (ls : LogState) : Prop :=
  σ.pend = ls.unpersisted ∧
  (ls.snap = none → ∀ e0, ls.unpersisted.head? = some e0 →
     uint.Z ls.prev.index' + (ls.sents.length : Int) + 1 ≤ uint.Z e0.Index')

omit [GoGlobalContext] in
/-- A read below `unstable.offset` is below the pending batch (`PendLogOk`). -/
theorem pendFrom_of_logOk (σ : StorState) (ls : LogState) (Hp : PendLogOk σ ls)
    (Hs : ls.snap = none) (n : Int)
    (Hn : n ≤ uint.Z ls.prev.index' + (ls.sents.length : Int) + 1) : PendFrom σ n := by
  intro e0 He0
  rw [Hp.1] at He0
  have := Hp.2 Hs e0 He0
  omega

/-- (D22 S-d4 item 3, 2026-10-21) The storage's extent with a snapshot pending: unless the storage
is lent, it -- its pending batch absorbed -- holds the log up to `sxt` (`LogState.sxt`), and `applying ≤ sxt`. With no snapshot pending `LogPersistOk` says
more. With one, the storage is the one from before the restore (`restore` changes neither it nor
`applying`, and sets `sxt` to `applying`: the storage held the log up to `offsetInProgress - 1 ≥
applying` then, `storExt_of_inv`), or the one a snapshot `Ready`'s receipt left (at that snapshot,
`sxt` its index). So the floor can be raised to `applying` while a snapshot restored since the
last `Ready` waits (`ownRaftLog_raise_floor`). -/
def StorExtOk (σ : StorState) (ls : LogState) : Prop :=
  ls.snap ≠ none → ls.lent = false →
    uint.Z ls.sxt ≤ uint.Z σ.prev.index' + ((storApp σ σ.pend).length : Int) ∧
    uint.Z ls.applying ≤ uint.Z ls.sxt

/-- (D19i part 1, 2026-10-18) The floor (`StorState.fl`, `LogState.fl`): the storage's is the
log's, at most `applying` (so every read the log makes from `applying + 1` on is above it, and
answers as before; `node.go` raises it to `applying` when the application's `Advance` is handed
over, before `RawNode.Advance` moves `applied` there: `RNState.flw`, and the reads from
`applied + 1`, `hasUnappliedConfChanges`', take `fl ≤ applied` as a premise), below `offsetInProgress` (with no snapshot pending the storage then agrees
with the log up to it: `LogPersistOk`; D22 S-d1b, 2026-10-21: also with one pending, so that the
batch a snapshot's `Ready` hands out is above the floor and `stableSnapTo` keeps it; until then
only with none), and below the storage's pending batch (`PendAbove`: an
append never rewrites what the application may compact). -/
def FlOk (σ : StorState) (ls : LogState) : Prop :=
  σ.fl = ls.fl ∧ uint.Z ls.fl ≤ uint.Z ls.applying ∧
  uint.Z ls.applying < uint.Z ls.inprogress ∧ PendAbove σ σ.pend ∧ StorExtOk σ ls

/-- (D22 S-d1b, 2026-10-21) The storage as the log holds it: `ownStorage`, unless it is lent to
the application (`LogState.lent`: a `Ready` handed out a snapshot, `ownRaftLog_lend`). While it is
lent the log's `σ` is the state the storage was lent at, its facts kept as pure facts of a value. -/
def lentStor (b : Bool) (st : Storage) (σ : StorState) : IProp GF :=
  if b then iprop(True) else ownStorage st σ

theorem lentStor_open {b : Bool} (h : b = false) (st : Storage) (σ : StorState) :
    lentStor (GF := GF) b st σ ⊢ ownStorage st σ := by
  subst h; exact .rfl

theorem lentStor_close {b : Bool} (h : b = false) (st : Storage) (σ : StorState) :
    ownStorage (GF := GF) st σ ⊢ lentStor b st σ := by
  subst h; exact .rfl

/-- With no snapshot pending the storage is not lent (`ownRaftLog`'s `Hlent`). -/
theorem lent_false_of {ls : LogState} (H : ls.lent = true → ls.snap ≠ none)
    (Hs : ls.snap = none) : ls.lent = false := by
  cases h : ls.lent
  · rfl
  · exact absurd Hs (H h)

/-- Lent, the storage is nothing the log holds. -/
theorem lentStor_lent {b : Bool} (h : b = true) (st : Storage) (σ : StorState) :
    ⊢ lentStor (GF := GF) b st σ := by
  subst h; unfold lentStor; exact BI.true_intro

/-- (D22 S-d1b) The persistence relation while a snapshot is in progress (`LogState.sip`), free of
the storage's state, which may be lent: the stable part and the in-progress unstable entries (`ipo`
of them) are a prefix of what the storage holds once the application has done what the `Ready`
asked (`stored`: the snapshot's entries after it), all of the log when all of it is in progress.
`LogPersistOk`'s first two conjuncts with `storApp σ pend` replaced by `stored`, which it implies
(`LogPersistOk.rel`); what the absorption of the application's receipt needs
(`ownRaftLog_absorb_snap`). -/
def LogPersistRel (sents uents : List EntryM) (ipo : Int) (stored : List EntryM) : Prop :=
  (sents ++ uents.take ipo.toNat) <+: stored ∧ (ipo.toNat = uents.length → sents ++ uents = stored)

omit [GoGlobalContext] in
theorem LogPersistOk.rel {σ : StorState} {sents uents : List EntryM} {ipo : Int}
    {pend stored : List EntryM} (H : LogPersistOk σ sents uents ipo pend stored) :
    LogPersistRel sents uents ipo stored := by
  obtain ⟨H1, H2, -, H4⟩ := H
  rw [H4] at H1 H2
  exact ⟨H1, H2⟩

omit [GoGlobalContext] in
/-- The relation holds of a storage that will hold the whole log. -/
theorem LogPersistRel_full (sents uents : List EntryM) (ipo : Int) :
    LogPersistRel sents uents ipo (sents ++ uents) :=
  ⟨(List.prefix_append_right_inj sents).mpr (List.take_prefix _ _), fun _ => rfl⟩

/-- (D22 S-d1b) What the log says of a snapshot in progress (`LogState.sip`): the persistence
relation (`LogPersistRel`), kept from the `Ready` that handed the snapshot out (`acceptUnstable`)
through the appends after it to the absorption of the application's receipt. -/
abbrev SipOk (ls : LogState) (off : w64) : Prop :=
  (ls.sip = true → LogPersistRel ls.sents ls.uents (uint.Z ls.inprogress - uint.Z off) ls.stored) ∧
  -- (D22 S-d3a, 2026-10-21) a pending snapshot not yet handed out: nothing after it is in progress
  -- (`restore` sets `offsetInProgress` to the offset, a truncation keeps it there, only
  -- `acceptUnstable` moves it, and sets `snapshotInProgress`), so a snapshot `Ready` hands out
  -- every entry after the snapshot, which the storage then holds (`stored`); and `applying` is at
  -- most the snapshot's index (`restore` is past the commit index, and nothing is applied while
  -- a snapshot is pending)
  (ls.snap ≠ none → ls.sip = false → ls.inprogress = off ∧ uint.Z ls.applying ≤ uint.Z ls.prev.index')

/-- (D22 S-d3a) `applying` moved to `a`, below `offsetInProgress` (or not past `applying`): with
a pending snapshot not yet handed out, `offsetInProgress` is the offset, right after the
snapshot, so `a` is at most the snapshot's index. -/
theorem SipOk.applying_lt {ls : LogState} {σ : StorState} {off a : w64} (H : SipOk ls off)
    (Hst : LogStoreOk ls.snap σ ls.prev ls.sents ls.uents)
    (Hoff : uint.Z off = uint.Z ls.prev.index' + (ls.sents.length : Int) + 1)
    (Ha : uint.Z a ≤ uint.Z ls.applying ∨ uint.Z a < uint.Z ls.inprogress) :
    ls.snap ≠ none → ls.sip = false → ls.inprogress = off ∧ uint.Z a ≤ uint.Z ls.prev.index' := by
  intro h1 h2
  obtain ⟨Hio, Hapl⟩ := H.2 h1 h2
  refine ⟨Hio, ?_⟩
  obtain ⟨sid, hs⟩ := Option.ne_none_iff_exists'.1 h1
  rw [hs] at Hst
  obtain ⟨-, Hse, -⟩ := Hst
  rw [Hse] at Hoff
  simp only [List.length_nil, Int.natCast_zero, Int.add_zero] at Hoff
  rw [Hio] at Ha
  omega

/-- (D22 S-d2, 2026-10-21) What the log says while the storage is at the pending snapshot
(`LogState.sat`): the application's receipt of the snapshot in progress absorbed -- the storage
not lent, nothing unpersisted, its state at the snapshot (`σ.prev = σ.ss = prev`), holding what
the `Ready` asked it to store (`stored`), nothing pending. -/
abbrev SatOk (σ : StorState) (ls : LogState) : Prop :=
  ls.snap = some ls.prev ∧ ls.sip = true ∧ ls.lent = false ∧ ls.unpersisted = [] ∧
  σ.prev = ls.prev ∧ σ.ss = ls.prev ∧ σ.ents = ls.stored ∧ σ.pend = []

omit [GoGlobalContext] in
/-- (D22 S-d4 item 3) The storage's extent from the log's other facts, whatever the pending
snapshot: with none, from the persistence relation (`LogPersistOk`: the storage holds the log up to
`offsetInProgress - 1 ≥ applying`); with one, from `StorExtOk`. What a restore needs: it makes a
snapshot pending and sets `sxt` to `applying`. -/
theorem storExt_of_inv {σ : StorState} {ls : LogState} {off : w64}
    (Hstore : LogStoreOk ls.snap σ ls.prev ls.sents ls.uents)
    (Hoff : uint.Z off = uint.Z ls.prev.index' + (ls.sents.length : Int) + 1)
    (Hipb : uint.Z off ≤ uint.Z ls.inprogress ∧
      uint.Z ls.inprogress ≤ uint.Z off + (ls.uents.length : Int))
    (Hpersist : ls.snap = none →
      LogPersistOk σ ls.sents ls.uents (uint.Z ls.inprogress - uint.Z off) ls.unpersisted ls.stored)
    (Hpend : PendLogOk σ ls) (Hfl : FlOk σ ls) (Hlnt : ls.lent = false) :
    uint.Z ls.applying ≤ uint.Z σ.prev.index' + ((storApp σ σ.pend).length : Int) := by
  have Hlt := Hfl.2.2.1
  rcases Option.eq_none_or_eq_some ls.snap with Hs | ⟨sid, Hs⟩
  · obtain ⟨Hsp, -, -⟩ : LogStoreOk none σ ls.prev ls.sents ls.uents := Hs ▸ Hstore
    have Hp := (Hpersist Hs).1.length_le
    rw [Hpend.1]
    simp only [List.length_append, List.length_take] at Hp
    rw [Hsp]
    omega
  · have He := Hfl.2.2.2.2 (by rw [Hs]; simp) Hlnt
    omega

/-- The one predicate for a `raftLog`, indexed by its abstract state `ls` (`LogState`,
above): the struct at some value `lv` whose fields are `ls`'s, the `Storage` at some
state `σ`, and the facts above. The facts are stated on `ls` wherever `ls` has the
field (`committed`, `applied`, `applying`, `inprogress`, the applying budget), so that
a proof works on `ls` and uses `Hcm`, `Hap`, ... only where it reads the struct; the
`unstable` field's `offset`, which `ls` does not record, is `lv`'s. (Until 2026-10-09
everything but the struct was `ownRaftLogCore lv ls.snap ls.prev ls.sents ls.uents
ls.unpersisted`, with the storage as `∃ sprev stored ss` and the facts on `lv`.) -/
def ownRaftLog (l : Loc) (ls : LogState) : IProp GF :=
  iprop(∃ (lv : raftLog) (σ : StorState),
  "Hl" ∷ l ↦ lv ∗
  "%Hcm" ∷ ⌜lv.committed' = ls.committed⌝ ∗
  "%Hap" ∷ ⌜lv.applied' = ls.applied⌝ ∗
  "%Hapg" ∷ ⌜lv.applying' = ls.applying⌝ ∗
  "%Hip" ∷ ⌜lv.unstable'.offsetInProgress' = ls.inprogress⌝ ∗
  -- (D22 S-d1, 2026-10-20) `snapshotInProgress`, set only with a snapshot pending
  "%Hsip" ∷ ⌜lv.unstable'.snapshotInProgress' = ls.sip⌝ ∗
  "%Hsipn" ∷ ⌜ls.snap = none → ls.sip = false⌝ ∗
  "%Hasz" ∷ ⌜lv.applyingEntsSize' = ls.apsize⌝ ∗
  "%Hamx" ∷ ⌜lv.maxApplyingEntsSize' = ls.apmax⌝ ∗
  "%Hidx" ∷ ⌜LogIndicesOk ls.prev (ls.sents ++ ls.uents)⌝ ∗
  "%Hnowrap" ∷ ⌜uint.Z ls.prev.index' + (ls.sents.length : Int)
                  + (ls.uents.length : Int) + 1 < 2^64⌝ ∗
  "#HisStorage" ∷ isStorage lv.storage' ∗
  -- (D22 S-d1b, 2026-10-21) unless lent to the application (`lentStor`)
  "HStorage" ∷ lentStor ls.lent lv.storage' σ ∗
  "%Hstore" ∷ ⌜LogStoreOk ls.snap σ ls.prev ls.sents ls.uents⌝ ∗
  "#Husnap" ∷ ownSnap lv.unstable'.snapshot' ls.snap ∗
  -- (2026-10-15, stage S) the snapshots `raftLog.snapshot` may return are ones the node may
  -- send (`ksn`): the storage's, once it is not the empty one, and the pending one
  "%Hsksn" ∷ ⌜σ.ss.index' ≠ W64 0 → SnapTrip.mk σ.ss σ.scs σ.sal σ.sdat ∈ ls.ksn⌝ ∗
  "#Hpksn" ∷ pendKsn lv.unstable'.snapshot' ls.snap ls.ksn ∗
  -- (D22 S-b′3, 2026-10-20) and each is certified in the storage's registry (`storCert`): the
  -- storage's from its own registry (`newRaft`'s premise), a restored one registered from its
  -- message's certificate (`raft.Step`)
  "#Hkcert" ∷ ([∗list] k ∈ ls.ksn, storCert lv.storage' k) ∗
  "%Hoffset" ∷ ⌜uint.Z lv.unstable'.offset'
                 = uint.Z ls.prev.index' + (ls.sents.length : Int) + 1⌝ ∗
  "Huents" ∷ entsRO lv.unstable'.entries' ls.uents ∗
  "Huents_cap" ∷ ownSliceCap Loc lv.unstable'.entries' (DFrac.own 1) ∗
  "%Happlied" ∷ ⌜uint.Z ls.prev.index' ≤ uint.Z ls.committed ∧
                  uint.Z ls.applied ≤ uint.Z ls.committed⌝ ∗
  "%Hpapplied" ∷ ⌜ls.snap = none → uint.Z ls.prev.index' ≤ uint.Z ls.applied⌝ ∗
  "%Hcommitted" ∷ ⌜uint.Z ls.committed
                    ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
                      + (ls.uents.length : Int)⌝ ∗
  "%Hssnap" ∷ ⌜ls.snap = none → StoredSnapOk σ ls.committed ls.prev (ls.sents ++ ls.uents)⌝ ∗
  "#Hl_logger" ∷ isLoggerVal lv.logger' ∗
  "#Hu_logger" ∷ isLoggerVal lv.unstable'.logger' ∗
  -- what `Ready`/`Advance` need (2026-10-05): `offsetInProgress` lies between `offset`
  -- and the end of the log (`nextEntries` slices at it); the persistence invariant
  -- (`LogPersistOk`); `applying` between `applied` and `committed` (`nextCommittedEnts`
  -- slices from `applying+1`); and while applying is not paused there is room under
  -- `maxApplyingEntsSize` (`nextCommittedEnts`' `Panicf` on `maxSize <= 0`).
  "%Hipb" ∷ ⌜uint.Z lv.unstable'.offset' ≤ uint.Z ls.inprogress ∧
             uint.Z ls.inprogress ≤ uint.Z lv.unstable'.offset' + (ls.uents.length : Int)⌝ ∗
  "%Hpersist" ∷ ⌜ls.snap = none →
                  LogPersistOk σ ls.sents ls.uents
                    (uint.Z ls.inprogress - uint.Z lv.unstable'.offset') ls.unpersisted
                    ls.stored⌝ ∗
  "%Happlying" ∷ ⌜uint.Z ls.applied ≤ uint.Z ls.applying ∧
                   uint.Z ls.applying ≤ uint.Z ls.committed⌝ ∗
  "%Hpaused" ∷ ⌜lv.applyingEntsPaused' = false → uint.Z ls.apsize < uint.Z ls.apmax⌝ ∗
  -- the storage, as the state names it, and its pending batch (2026-10-10)
  "%Hstor" ∷ ⌜lv.storage' = ls.storage⌝ ∗
  "%Hpend" ∷ ⌜PendLogOk σ ls⌝ ∗
  "%Hfl" ∷ ⌜FlOk σ ls⌝ ∗
  -- (D22 S-d1b, 2026-10-21) the storage lent only with a snapshot pending; neither of
  -- `ownRaftLogW`'s windows (`sapp`, `aps`); and a snapshot in progress (`SipOk`)
  "%Hlent" ∷ ⌜ls.lent = true → ls.snap ≠ none⌝ ∗
  "%Hq" ∷ ⌜ls.sapp = false ∧ ls.aps = false⌝ ∗
  "%Hprel" ∷ ⌜SipOk ls lv.unstable'.offset'⌝ ∗
  -- (D22 S-d2) the storage at the pending snapshot (`SatOk`)
  "%Hsat" ∷ ⌜ls.sat = true → SatOk σ ls⌝)

/-- Re-seal `ownRaftLog` from the pieces `iNamed Hlog` names. **Use this rather than
`iframe`**: with the existential storage state, Rocq's `iFrame` spends ~35 s searching
(measured in `proof_raftLog__lastIndex.v`, 2026-10-01). `st` is the storage as the
hypotheses mention it -- `lv.storage'`, or `interface.ok isv` after a rewrite with
`Hstok` -- and the premise `lv.storage' = st` is then `rfl` or `Hstok`. The
`reseal_raftLog` tactic below applies it with the standard names and closes the pure
premises by assumption. The snapshot and the unstable entries the spatial premises
mention are `snap` and `uents`, with `ls.snap = snap` and `ls.uents = uents` as the
last premises: were they `ls.snap` and `ls.uents`, `iapply … $$ Husnap Huents` would
fix `ls` to the state the hypotheses were opened at before the goal's (new) state is
seen. (Until 2026-10-09 it took the state as eleven field variables and the storage as
three.) -/
theorem ownRaftLog_intro (l : Loc) (lv : raftLog) (st : Storage) (σ : StorState)
    (snap : Option entryID) (uents : List EntryM) (ls : LogState) {K : List SnapTrip} {lt : Bool} :
    lv.storage' = st →
    lv.committed' = ls.committed →
    lv.applied' = ls.applied →
    LogIndicesOk ls.prev (ls.sents ++ ls.uents) →
    uint.Z ls.prev.index' + (ls.sents.length : Int) + (ls.uents.length : Int) + 1 < 2^64 →
    LogStoreOk ls.snap σ ls.prev ls.sents ls.uents →
    uint.Z lv.unstable'.offset' = uint.Z ls.prev.index' + (ls.sents.length : Int) + 1 →
    uint.Z ls.prev.index' ≤ uint.Z ls.committed ∧ uint.Z ls.applied ≤ uint.Z ls.committed →
    (ls.snap = none → uint.Z ls.prev.index' ≤ uint.Z ls.applied) →
    uint.Z ls.committed ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
      + (ls.uents.length : Int) →
    (ls.snap = none → StoredSnapOk σ ls.committed ls.prev (ls.sents ++ ls.uents)) →
    lv.applying' = ls.applying →
    lv.unstable'.offsetInProgress' = ls.inprogress →
    uint.Z lv.unstable'.offset' ≤ uint.Z ls.inprogress ∧
      uint.Z ls.inprogress ≤ uint.Z lv.unstable'.offset' + (ls.uents.length : Int) →
    (ls.snap = none →
      LogPersistOk σ ls.sents ls.uents
        (uint.Z ls.inprogress - uint.Z lv.unstable'.offset') ls.unpersisted ls.stored) →
    uint.Z ls.applied ≤ uint.Z ls.applying ∧ uint.Z ls.applying ≤ uint.Z ls.committed →
    (lv.applyingEntsPaused' = false → uint.Z ls.apsize < uint.Z ls.apmax) →
    lv.applyingEntsSize' = ls.apsize →
    lv.maxApplyingEntsSize' = ls.apmax →
    lv.storage' = ls.storage →
    PendLogOk σ ls →
    FlOk σ ls →
    (σ.ss.index' ≠ W64 0 → SnapTrip.mk σ.ss σ.scs σ.sal σ.sdat ∈ ls.ksn) →
    lv.unstable'.snapshotInProgress' = ls.sip →
    (ls.snap = none → ls.sip = false) →
    (ls.lent = true → ls.snap ≠ none) →
    ls.sapp = false ∧ ls.aps = false →
    SipOk ls lv.unstable'.offset' →
    (ls.sat = true → SatOk σ ls) →
    ls.snap = snap →
    ls.uents = uents →
    ls.ksn = K →
    ls.lent = lt →
    ⊢ l ↦ lv -∗
      isStorage (GF := GF) st -∗
      lentStor lt st σ -∗
      ownSnap lv.unstable'.snapshot' snap -∗
      pendKsn lv.unstable'.snapshot' snap K -∗
      ([∗list] k ∈ K, storCert st k) -∗
      entsRO lv.unstable'.entries' uents -∗
      ownSliceCap Loc lv.unstable'.entries' (DFrac.own 1) -∗
      isLoggerVal lv.logger' -∗
      isLoggerVal lv.unstable'.logger' -∗
      ownRaftLog l ls := by
  intro Hst Hcm Hap Hidx Hnowrap Hstore Hoffset Happlied Hpapplied
    Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn
    Hsip Hsipn Hlent Hq Hprel Hsat Hsnap Huents HK HLT
  subst Hst Hsnap Huents HK HLT
  iintro Hl #HisStorage HStorage #Husnap #Hpksn #Hkcert #Huents Huents_cap #Hl_logger #Hu_logger
  unfold ownRaftLog
  iexists lv, σ
  simp only [named]
  iframe Hl HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger
  ipureintro
  exact ⟨Hcm, Hap, Hapg, Hip, Hsip, Hsipn, Hasz, Hamx, Hidx, Hnowrap, Hstore, Hsksn, Hoffset, Happlied, Hpapplied, Hcommitted, Hssnap, Hipb, Hpersist, Happlying, Hpaused, Hstor, Hpend, Hfl, Hlent, Hq, Hprel, Hsat⟩

/-! ### The acknowledgement's windows: `ownRaftLogW` (D22 S-d1b, 2026-10-21)

Two log states exist only inside the arm of `raft.Step` that steps a `Ready`'s acknowledgement
of a snapshot (`MsgStorageAppendResp` with `Snapshot` set):

- `sapp` (`LogState.sapp`): the application's receipt of the snapshot in progress is absorbed
  (`ownRaftLog_absorb_snap`), so the storage holds the pending snapshot and the entries after it.
  The arm's `stableTo` then moves entries stable **while `unstable.snapshot` is still set**
  (`raft.go:1194-1201`: `stableTo` before `appliedSnap`), and Go's reads of the log would be
  wrong there -- `unstable.maybeLastIndex` answers the snapshot's index once the unstable entries
  are gone, `maybeTerm` misses inside the stable part -- which is harmless only because nothing
  reads the log before `appliedSnap`'s `stableSnapTo` drops the snapshot;
- `aps` (`LogState.aps`): `appliedSnap` between `stableSnapTo` and `appliedTo`, the snapshot
  dropped and `applied` still below the boundary (`Hpapplied` fails).

`ownRaftLog` has both off (`Hq`), so every reader's proof stays as it was; `ownRaftLogW` (below)
admits them, and only `raftLog.stableTo`, `raftLog.stableSnapTo`, `raftLog.appliedTo` and (at the
raft layer) `raft.appliedTo`, `raft.appliedSnap` are specified on it. In the `sapp` window the
storage relation and the facts kept while no snapshot is pending are stated as if none were
(`snapV`: the storage is at the snapshot, the stable part after it). -/

/-- (D22 S-d1b) The pending snapshot as the storage relation sees it: none once the storage holds
it (`sapp`). -/
abbrev snapV (ls : LogState) : Option entryID := if ls.sapp then none else ls.snap

theorem snapV_of {ls : LogState} (h : ls.sapp = false) : snapV ls = ls.snap := by
  simp [snapV, h]

theorem snapV_sapp {ls : LogState} (h : ls.sapp = true) : snapV ls = none := by
  simp [snapV, h]

/-- (D22 S-d1b) What the `sapp` window says besides the storage relation: a snapshot in progress,
the storage not lent and nothing unpersisted (the receipt absorbed), and the storage's own
snapshot the pending one, which is the log's boundary. -/
abbrev SappOk (σ : StorState) (ls : LogState) : Prop :=
  ls.snap = some ls.prev ∧ ls.sip = true ∧ ls.lent = false ∧ ls.unpersisted = [] ∧ σ.ss = ls.prev

/-- (D22 S-d3a) `SipOk.applying_lt` in the windows (`ownRaftLogW`): a snapshot not in progress
is outside `sapp`, where the storage relation is at it. -/
theorem SipOk.applying_ltW {ls : LogState} {σ : StorState} {off a : w64} (H : SipOk ls off)
    (Hst : LogStoreOk (snapV ls) σ ls.prev ls.sents ls.uents)
    (Hsapp : ls.sapp = true → SappOk σ ls)
    (Hoff : uint.Z off = uint.Z ls.prev.index' + (ls.sents.length : Int) + 1)
    (Ha : uint.Z a ≤ uint.Z ls.applying ∨ uint.Z a < uint.Z ls.inprogress) :
    ls.snap ≠ none → ls.sip = false → ls.inprogress = off ∧ uint.Z a ≤ uint.Z ls.prev.index' := by
  intro h1 h2
  have hs : ls.sapp = false := by
    cases hh : ls.sapp with
    | false => rfl
    | true => have := (Hsapp hh).2.1; rw [h2] at this; cases this
  rw [snapV_of hs] at Hst
  exact SipOk.applying_lt H Hst Hoff Ha h1 h2

/-- `ownRaftLog` with the acknowledgement's windows (`sapp`, `aps`) admitted: the same pieces, the
storage relation, `Hssnap` and `Hpersist` at `snapV`, `Hpapplied` outside `aps`, and `SappOk` in
the `sapp` window. -/
def ownRaftLogW (l : Loc) (ls : LogState) : IProp GF :=
  iprop(∃ (lv : raftLog) (σ : StorState),
  "Hl" ∷ l ↦ lv ∗
  "%Hcm" ∷ ⌜lv.committed' = ls.committed⌝ ∗
  "%Hap" ∷ ⌜lv.applied' = ls.applied⌝ ∗
  "%Hapg" ∷ ⌜lv.applying' = ls.applying⌝ ∗
  "%Hip" ∷ ⌜lv.unstable'.offsetInProgress' = ls.inprogress⌝ ∗
  "%Hsip" ∷ ⌜lv.unstable'.snapshotInProgress' = ls.sip⌝ ∗
  "%Hsipn" ∷ ⌜ls.snap = none → ls.sip = false⌝ ∗
  "%Hasz" ∷ ⌜lv.applyingEntsSize' = ls.apsize⌝ ∗
  "%Hamx" ∷ ⌜lv.maxApplyingEntsSize' = ls.apmax⌝ ∗
  "%Hidx" ∷ ⌜LogIndicesOk ls.prev (ls.sents ++ ls.uents)⌝ ∗
  "%Hnowrap" ∷ ⌜uint.Z ls.prev.index' + (ls.sents.length : Int)
                  + (ls.uents.length : Int) + 1 < 2^64⌝ ∗
  "#HisStorage" ∷ isStorage lv.storage' ∗
  "HStorage" ∷ lentStor ls.lent lv.storage' σ ∗
  "%Hstore" ∷ ⌜LogStoreOk (snapV ls) σ ls.prev ls.sents ls.uents⌝ ∗
  "#Husnap" ∷ ownSnap lv.unstable'.snapshot' ls.snap ∗
  "%Hsksn" ∷ ⌜σ.ss.index' ≠ W64 0 → SnapTrip.mk σ.ss σ.scs σ.sal σ.sdat ∈ ls.ksn⌝ ∗
  "#Hpksn" ∷ pendKsn lv.unstable'.snapshot' ls.snap ls.ksn ∗
  "#Hkcert" ∷ ([∗list] k ∈ ls.ksn, storCert lv.storage' k) ∗
  "%Hoffset" ∷ ⌜uint.Z lv.unstable'.offset'
                 = uint.Z ls.prev.index' + (ls.sents.length : Int) + 1⌝ ∗
  "Huents" ∷ entsRO lv.unstable'.entries' ls.uents ∗
  "Huents_cap" ∷ ownSliceCap Loc lv.unstable'.entries' (DFrac.own 1) ∗
  "%Happlied" ∷ ⌜uint.Z ls.prev.index' ≤ uint.Z ls.committed ∧
                  uint.Z ls.applied ≤ uint.Z ls.committed⌝ ∗
  "%Hpapplied" ∷ ⌜ls.snap = none → ls.aps = false → uint.Z ls.prev.index' ≤ uint.Z ls.applied⌝ ∗
  "%Hcommitted" ∷ ⌜uint.Z ls.committed
                    ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
                      + (ls.uents.length : Int)⌝ ∗
  "%Hssnap" ∷ ⌜snapV ls = none → StoredSnapOk σ ls.committed ls.prev (ls.sents ++ ls.uents)⌝ ∗
  "#Hl_logger" ∷ isLoggerVal lv.logger' ∗
  "#Hu_logger" ∷ isLoggerVal lv.unstable'.logger' ∗
  "%Hipb" ∷ ⌜uint.Z lv.unstable'.offset' ≤ uint.Z ls.inprogress ∧
             uint.Z ls.inprogress ≤ uint.Z lv.unstable'.offset' + (ls.uents.length : Int)⌝ ∗
  "%Hpersist" ∷ ⌜snapV ls = none →
                  LogPersistOk σ ls.sents ls.uents
                    (uint.Z ls.inprogress - uint.Z lv.unstable'.offset') ls.unpersisted
                    ls.stored⌝ ∗
  "%Happlying" ∷ ⌜uint.Z ls.applied ≤ uint.Z ls.applying ∧
                   uint.Z ls.applying ≤ uint.Z ls.committed⌝ ∗
  "%Hpaused" ∷ ⌜lv.applyingEntsPaused' = false → uint.Z ls.apsize < uint.Z ls.apmax⌝ ∗
  "%Hstor" ∷ ⌜lv.storage' = ls.storage⌝ ∗
  "%Hpend" ∷ ⌜PendLogOk σ ls⌝ ∗
  "%Hfl" ∷ ⌜FlOk σ ls⌝ ∗
  "%Hlent" ∷ ⌜ls.lent = true → ls.snap ≠ none⌝ ∗
  "%Hsappi" ∷ ⌜ls.sapp = true → SappOk σ ls⌝ ∗
  "%Hprel" ∷ ⌜SipOk ls lv.unstable'.offset'⌝ ∗
  "%Hsat" ∷ ⌜ls.sat = true → SatOk σ ls⌝)

/-- Re-seal `ownRaftLogW`, as `ownRaftLog_intro` (the premises in the same order, the windows'
forms of `Hstore`, `Hpapplied`, `Hssnap`, `Hpersist`, and `SappOk` in place of `Hq`). -/
theorem ownRaftLogW_intro (l : Loc) (lv : raftLog) (st : Storage) (σ : StorState)
    (snap : Option entryID) (uents : List EntryM) (ls : LogState) {K : List SnapTrip} {lt : Bool} :
    lv.storage' = st →
    lv.committed' = ls.committed →
    lv.applied' = ls.applied →
    LogIndicesOk ls.prev (ls.sents ++ ls.uents) →
    uint.Z ls.prev.index' + (ls.sents.length : Int) + (ls.uents.length : Int) + 1 < 2^64 →
    LogStoreOk (snapV ls) σ ls.prev ls.sents ls.uents →
    uint.Z lv.unstable'.offset' = uint.Z ls.prev.index' + (ls.sents.length : Int) + 1 →
    uint.Z ls.prev.index' ≤ uint.Z ls.committed ∧ uint.Z ls.applied ≤ uint.Z ls.committed →
    (ls.snap = none → ls.aps = false → uint.Z ls.prev.index' ≤ uint.Z ls.applied) →
    uint.Z ls.committed ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
      + (ls.uents.length : Int) →
    (snapV ls = none → StoredSnapOk σ ls.committed ls.prev (ls.sents ++ ls.uents)) →
    lv.applying' = ls.applying →
    lv.unstable'.offsetInProgress' = ls.inprogress →
    uint.Z lv.unstable'.offset' ≤ uint.Z ls.inprogress ∧
      uint.Z ls.inprogress ≤ uint.Z lv.unstable'.offset' + (ls.uents.length : Int) →
    (snapV ls = none →
      LogPersistOk σ ls.sents ls.uents
        (uint.Z ls.inprogress - uint.Z lv.unstable'.offset') ls.unpersisted ls.stored) →
    uint.Z ls.applied ≤ uint.Z ls.applying ∧ uint.Z ls.applying ≤ uint.Z ls.committed →
    (lv.applyingEntsPaused' = false → uint.Z ls.apsize < uint.Z ls.apmax) →
    lv.applyingEntsSize' = ls.apsize →
    lv.maxApplyingEntsSize' = ls.apmax →
    lv.storage' = ls.storage →
    PendLogOk σ ls →
    FlOk σ ls →
    (σ.ss.index' ≠ W64 0 → SnapTrip.mk σ.ss σ.scs σ.sal σ.sdat ∈ ls.ksn) →
    lv.unstable'.snapshotInProgress' = ls.sip →
    (ls.snap = none → ls.sip = false) →
    (ls.lent = true → ls.snap ≠ none) →
    (ls.sapp = true → SappOk σ ls) →
    SipOk ls lv.unstable'.offset' →
    (ls.sat = true → SatOk σ ls) →
    ls.snap = snap →
    ls.uents = uents →
    ls.ksn = K →
    ls.lent = lt →
    ⊢ l ↦ lv -∗
      isStorage (GF := GF) st -∗
      lentStor lt st σ -∗
      ownSnap lv.unstable'.snapshot' snap -∗
      pendKsn lv.unstable'.snapshot' snap K -∗
      ([∗list] k ∈ K, storCert st k) -∗
      entsRO lv.unstable'.entries' uents -∗
      ownSliceCap Loc lv.unstable'.entries' (DFrac.own 1) -∗
      isLoggerVal lv.logger' -∗
      isLoggerVal lv.unstable'.logger' -∗
      ownRaftLogW l ls := by
  intro Hst Hcm Hap Hidx Hnowrap Hstore Hoffset Happlied Hpapplied
    Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn
    Hsip Hsipn Hlent Hsappi Hprel Hsat Hsnap Huents HK HLT
  subst Hst Hsnap Huents HK HLT
  iintro Hl #HisStorage HStorage #Husnap #Hpksn #Hkcert #Huents Huents_cap #Hl_logger #Hu_logger
  unfold ownRaftLogW
  iexists lv, σ
  simp only [named]
  iframe Hl HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger
  ipureintro
  exact ⟨Hcm, Hap, Hapg, Hip, Hsip, Hsipn, Hasz, Hamx, Hidx, Hnowrap, Hstore, Hsksn, Hoffset, Happlied, Hpapplied, Hcommitted, Hssnap, Hipb, Hpersist, Happlying, Hpaused, Hstor, Hpend, Hfl, Hlent, Hsappi, Hprel, Hsat⟩

/-- Every quiet log is one with the windows admitted. -/
theorem ownRaftLog_toW (l : Loc) (ls : LogState) :
    ownRaftLog (GF := GF) l ls ⊢ ownRaftLogW l ls := by
  iintro H
  iNamed H
  have Hv : snapV ls = ls.snap := snapV_of Hq.1
  iapply ownRaftLogW_intro l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap (Hv ▸ Hstore) Hoffset
    Happlied (fun h _ => Hpapplied h) Hcommitted (Hv ▸ Hssnap) Hapg Hip Hipb (Hv ▸ Hpersist)
    Happlying Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn Hsip Hsipn Hlent
    (fun h => absurd h (by rw [Hq.1]; decide)) Hprel Hsat rfl rfl rfl rfl
    $$ Hl HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger

/-- Outside the windows, a log with them admitted is quiet. -/
theorem ownRaftLogW_quiet (l : Loc) (ls : LogState) (Hq : ls.sapp = false ∧ ls.aps = false) :
    ownRaftLogW (GF := GF) l ls ⊢ ownRaftLog l ls := by
  iintro H
  iNamed H
  have Hv : snapV ls = ls.snap := snapV_of Hq.1
  iapply ownRaftLog_intro l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap (Hv ▸ Hstore) Hoffset
    Happlied (fun h => Hpapplied h Hq.2) Hcommitted (Hv ▸ Hssnap) Hapg Hip Hipb (Hv ▸ Hpersist)
    Happlying Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn Hsip Hsipn Hlent Hq Hprel Hsat rfl rfl rfl rfl
    $$ Hl HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger

/-- `ownRaftLogW_quiet` with the facts as a pure premise, for a state the caller has not named. -/
theorem ownRaftLogW_quietW (l : Loc) (ls : LogState) :
    ⊢ ownRaftLogW (GF := GF) l ls -∗ ⌜ls.sapp = false ∧ ls.aps = false⌝ -∗ ownRaftLog l ls := by
  iintro H %Hq
  iapply ownRaftLogW_quiet l ls Hq $$ H

/-- (D22 S-d2, 2026-10-21) **The `sapp` window opened**, in the acknowledgement's arm of
`raft.Step`: with the storage at the pending snapshot (`sat`, `SatOk`), the storage relation is
the one with no snapshot pending (`snapV`), the persistence relation of the snapshot in progress
(`SipOk`) giving `LogPersistOk` against the storage. -/
theorem ownRaftLog_sapp (l : Loc) (ls : LogState) (Hs : ls.sat = true) :
    ownRaftLog (GF := GF) l ls ⊢ ownRaftLogW l { ls with sapp := true } := by
  iintro H
  iNamed H
  obtain ⟨Hsp, Hsipt, Hlnt, Hunp, Hσp, Hσs, Hσe, Hσpd⟩ := Hsat Hs
  obtain ⟨-, Hse, -⟩ : LogStoreOk (some ls.prev) σ ls.prev ls.sents ls.uents := Hsp ▸ Hstore
  have Hrel := Hprel.1 Hsipt
  have Hstore' : LogStoreOk (snapV { ls with sapp := true }) σ ls.prev ls.sents ls.uents := by
    show σ.prev = ls.prev ∧ ls.sents <+: σ.ents ∧ (ls.uents = [] → ls.sents = σ.ents)
    refine ⟨Hσp, by rw [Hse]; exact List.nil_prefix, fun Hu => ?_⟩
    have Hz : (uint.Z ls.inprogress - uint.Z lv.unstable'.offset').toNat = ls.uents.length := by
      rw [Hu] at Hipb ⊢
      simp only [List.length_nil, Int.natCast_zero, Int.add_zero] at Hipb ⊢
      omega
    have := Hrel.2 Hz
    rw [Hu, List.append_nil] at this
    rw [Hσe]; exact this
  have Hpersist' : snapV { ls with sapp := true } = none →
      LogPersistOk σ ls.sents ls.uents (uint.Z ls.inprogress - uint.Z lv.unstable'.offset')
        ls.unpersisted ls.stored := by
    intro _
    rw [Hunp]
    refine ⟨?_, ?_, fun _ => rfl, Hσe⟩
    · show _ <+: σ.ents; rw [Hσe]; exact Hrel.1
    · intro h; show _ = σ.ents; rw [Hσe]; exact Hrel.2 h
  have Hssnap' : snapV { ls with sapp := true } = none →
      StoredSnapOk σ ls.committed ls.prev (ls.sents ++ ls.uents) := by
    intro _
    right
    rw [Hσs]
    exact ⟨Happlied.1, plogTermAt_base _ _⟩
  iapply ownRaftLogW_intro l lv lv.storage' σ _ _ { ls with sapp := true } rfl Hcm Hap Hidx
    Hnowrap Hstore' Hoffset Happlied (fun h _ => Hpapplied h) Hcommitted Hssnap' Hapg Hip Hipb
    Hpersist' Happlying Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn Hsip Hsipn Hlent
    (fun _ => ⟨Hsp, Hsipt, Hlnt, Hunp, Hσs⟩) Hprel Hsat rfl rfl rfl rfl
    $$ Hl HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger

/-- (D22 S-d2, 2026-10-21) `ownRaftLog_struct` in the windows, with what `raft.appliedTo` and
`raft.appliedSnap` read off the log: `applied` at most `applying` and `committed`, the boundary at
most `committed` and below `offsetInProgress`. -/
theorem ownRaftLogW_struct (l : Loc) (ls : LogState) :
    ⊢ ownRaftLogW (GF := GF) l ls -∗
      ∃ lv : raftLog, l ↦ lv ∗
        ⌜lv.applied' = ls.applied ∧ uint.Z ls.applied ≤ uint.Z ls.applying ∧
          uint.Z ls.applied ≤ uint.Z ls.committed ∧
          uint.Z ls.prev.index' ≤ uint.Z ls.committed ∧
          uint.Z ls.prev.index' < uint.Z ls.inprogress⌝ ∗
        (l ↦ lv -∗ ownRaftLogW l ls) := by
  iintro H
  iNamed H
  iexists lv
  iframe Hl
  isplitr
  · ipureintro; exact ⟨Hap, Happlying.1, Happlied.2, Happlied.1, by omega⟩
  · iintro Hl
    iapply ownRaftLogW_intro l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
      Happlied Hpapplied Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying
      Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn Hsip Hsipn Hlent Hsappi Hprel Hsat rfl rfl rfl rfl
      $$ Hl HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger

/-- (D22 S-d2) In the windows too, a pending snapshot is the log's boundary. -/
theorem ownRaftLogW_snap_prev (l : Loc) (ls : LogState) :
    ⊢ ownRaftLogW (GF := GF) l ls -∗
      ⌜∀ sid, ls.snap = some sid → sid = ls.prev⌝ ∗ ownRaftLogW l ls := by
  iintro H
  iNamed H
  isplitr
  · ipureintro
    intro sid Hs
    cases Hsa : ls.sapp
    · have Hv := snapV_of Hsa
      rw [Hv, Hs] at Hstore
      exact Hstore.1.symm
    · have := (Hsappi Hsa).1
      rw [Hs] at this
      exact Option.some.inj this
  · iapply ownRaftLogW_intro l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
      Happlied Hpapplied Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying
      Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn Hsip Hsipn Hlent Hsappi Hprel Hsat rfl rfl rfl rfl
      $$ Hl HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger

/-- The struct, for a field read. `committed` and `applied` are what the state says
they are. -/
theorem ownRaftLog_struct (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ∃ lv : raftLog, l ↦ lv ∗
            ⌜lv.committed' = ls.committed ∧ lv.applied' = ls.applied⌝ ∗
            (l ↦ lv -∗ ownRaftLog l ls) := by
  iintro H
  iNamed H
  iexists lv
  iframe Hl
  isplitr
  · ipureintro; exact ⟨Hcm, Hap⟩
  · iintro Hl
    iapply ownRaftLog_intro l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
      Happlied Hpapplied Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying
      Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn Hsip Hsipn Hlent Hq Hprel Hsat rfl rfl rfl rfl $$ Hl HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger
      Hu_logger

/-- Read a pure fact of `ownRaftLog` out of it, without consuming it, from the facts
about the whole of the log. The common proof of the `ownRaftLog_*` read-out lemmas below
(Rocq proves each by `iNamed`; `iFrame "∗#%"`). -/
theorem ownRaftLog_pure (l : Loc) (ls : LogState) (φ : Prop)
    (H : ∀ (lv : raftLog) (σ : StorState),
      LogIndicesOk ls.prev (ls.sents ++ ls.uents) →
      uint.Z ls.prev.index' + (ls.sents.length : Int) + (ls.uents.length : Int) + 1 < 2^64 →
      LogStoreOk ls.snap σ ls.prev ls.sents ls.uents →
      uint.Z lv.unstable'.offset' = uint.Z ls.prev.index' + (ls.sents.length : Int) + 1 →
      uint.Z ls.prev.index' ≤ uint.Z ls.committed ∧ uint.Z ls.applied ≤ uint.Z ls.committed →
      (ls.snap = none → uint.Z ls.prev.index' ≤ uint.Z ls.applied) →
      uint.Z ls.committed ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
        + (ls.uents.length : Int) →
      uint.Z lv.unstable'.offset' ≤ uint.Z ls.inprogress ∧
        uint.Z ls.inprogress ≤ uint.Z lv.unstable'.offset' + (ls.uents.length : Int) →
      uint.Z ls.applied ≤ uint.Z ls.applying ∧ uint.Z ls.applying ≤ uint.Z ls.committed →
      φ) :
    ⊢ ownRaftLog (GF := GF) l ls -∗ ⌜φ⌝ ∗ ownRaftLog l ls := by
  iintro H0
  iNamed H0
  isplitr
  · ipureintro
    exact H lv σ Hidx Hnowrap Hstore Hoffset Happlied Hpapplied Hcommitted
      Hipb Happlying
  · iapply ownRaftLog_intro l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
      Happlied Hpapplied Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying
      Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn Hsip Hsipn Hlent Hq Hprel Hsat rfl rfl rfl rfl $$ Hl HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger
      Hu_logger

/-- The `Ready`-side facts, read out without consuming the log: `inprogress` between
`offset` and the end of the log, and `applying` between `applied` and `committed`. -/
theorem ownRaftLog_ready_wf (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜(uint.Z ls.prev.index' + (ls.sents.length : Int) + 1 ≤ uint.Z ls.inprogress ∧
        uint.Z ls.inprogress ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
          + (ls.uents.length : Int) + 1) ∧
       (uint.Z ls.applied ≤ uint.Z ls.applying ∧ uint.Z ls.applying ≤ uint.Z ls.committed)⌝ ∗
      ownRaftLog l ls :=
  ownRaftLog_pure l ls _ fun _ _ _ _ _ Hoffset _ _ _ Hipb Happlying =>
    ⟨⟨by omega, by omega⟩, Happlying⟩

/-- The storage handshake's last step (2026-10-10; until then `ownRaftLog_persist`, an
accessor lending the storage itself): the receipt of the application's append of the
unpersisted entries -- for the log's own storage, at the state they were handed out at
-- is absorbed into the storage (`isStorage`'s `Habsorb`), which then holds them
(`storAbsorb`, `storApp` of the entries `Ready` handed out, which is what
`MemoryStorage.Append(rd.Entries)` does). The log then records nothing unpersisted.

Until 2026-10-10 the application borrowed the storage itself, which excluded raft's
reads meanwhile; a loan across calls was rejected earlier for the same reason (`Step`
between `Ready` and `Advance` is legal in Go, and reads the storage on most of its
paths). The pending batch in the storage's state (`StorState.pend`) lets raft keep
reading while the application appends. -/
theorem ownRaftLog_absorb (l : Loc) (ls : LogState) (σa : StorState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗ appendedTok ls.storage σa ls.unpersisted ==∗
      ownRaftLog l { ls with unpersisted := [] } := by
  iintro H Htok
  iNamed H
  rcases Bool.eq_false_or_eq_true ls.lent with Hlt | Hlt
  · -- (D22 S-d1b) lent: the storage is the application's, which appended the batch itself (the
    -- snapshot path never hands out a batch this way); the token is dropped, and the state the
    -- storage was lent at has nothing pending
    iclear Htok
    imodintro
    have Hsn : ls.snap ≠ none := Hlent Hlt
    have Hstore' : LogStoreOk ls.snap { σ with pend := [] } ls.prev ls.sents ls.uents := by
      cases Hs : ls.snap with
      | none => exact absurd Hs Hsn
      | some sid => rw [Hs] at Hstore; exact Hstore
    have Hpersist' : ls.snap = none →
        LogPersistOk { σ with pend := [] } ls.sents ls.uents
          (uint.Z ls.inprogress - uint.Z lv.unstable'.offset') [] ls.stored :=
      fun h => absurd h Hsn
    have Hssnap' : ls.snap = none →
        StoredSnapOk { σ with pend := [] } ls.committed ls.prev (ls.sents ++ ls.uents) :=
      fun h => absurd h Hsn
    have Hpend' : PendLogOk { σ with pend := [] } { ls with unpersisted := [] } :=
      ⟨rfl, fun _ e0 He0 => by simp at He0⟩
    have Hfl' : FlOk { σ with pend := [] } { ls with unpersisted := [] } :=
      ⟨Hfl.1, Hfl.2.1, Hfl.2.2.1, fun e0 He0 => by simp at He0,
        fun _ h => absurd (show ls.lent = false from h) (by rw [Hlt]; decide)⟩
    iapply ownRaftLog_intro l lv lv.storage' { σ with pend := [] } _ _ { ls with unpersisted := [] }
      rfl Hcm Hap Hidx Hnowrap Hstore' Hoffset Happlied Hpapplied Hcommitted Hssnap' Hapg Hip Hipb
      Hpersist' Happlying Hpaused Hasz Hamx Hstor Hpend' Hfl' Hsksn Hsip Hsipn Hlent Hq Hprel
      (fun h => absurd (Hsat h).2.2.1 (by rw [Hlt]; decide)) rfl rfl
      rfl rfl $$ Hl HisStorage [] Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger
    iapply lentStor_lent Hlt
  ihave HStorage := lentStor_open Hlt _ _ $$ HStorage
  ihave Htok : appendedTok lv.storage' σa ls.unpersisted $$ [Htok]
  · rw [Hstor]; iexact Htok
  ihave #Hsto : isStorageWith (ownStorage lv.storage') (appendTok lv.storage')
      (appendedTok lv.storage') (storCut lv.storage') (storFloor lv.storage') (storCert lv.storage') lv.storage' $$ [HisStorage]
  · unfold isStorage; iexact HisStorage
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  imod Habsorb $$ HStorage Htok with ⟨%Heq, HStorage⟩
  imodintro
  obtain ⟨Hpσ, -⟩ := Hpend
  have Hab : storAbsorb σ = { σ with ents := storApp σ ls.unpersisted, pend := [] } := by
    rw [← Hpσ]; rfl
  have Hstore' : LogStoreOk ls.snap (storAbsorb σ) ls.prev ls.sents ls.uents := by
    rw [Hab]
    cases Hs : ls.snap with
    | some sid => rw [Hs] at Hstore; exact Hstore
    | none =>
      rw [Hs] at Hstore
      obtain ⟨Hpre, _, Hpe, -⟩ := Hpersist Hs
      obtain ⟨Hsp, _, Hsu⟩ := Hstore
      refine ⟨Hsp, (List.prefix_append ls.sents _).trans Hpre, ?_⟩
      intro Hu
      rw [Hpe Hu]
      exact Hsu Hu
  have Hpersist' : ls.snap = none →
      LogPersistOk (storAbsorb σ) ls.sents ls.uents
        (uint.Z ls.inprogress - uint.Z lv.unstable'.offset') [] ls.stored := by
    intro Hs
    rw [Hab]
    obtain ⟨Hpre, Heq, _, Hst⟩ := Hpersist Hs
    exact ⟨Hpre, Heq, fun _ => rfl, Hst⟩
  have Hssnap' : ls.snap = none →
      StoredSnapOk (storAbsorb σ) ls.committed ls.prev (ls.sents ++ ls.uents) := Hssnap
  have Hpend' : PendLogOk (storAbsorb σ) { ls with unpersisted := [] } :=
    ⟨rfl, fun _ e0 He0 => by simp at He0⟩
  have Hfl' : FlOk (storAbsorb σ) { ls with unpersisted := [] } :=
    ⟨Hfl.1, Hfl.2.1, Hfl.2.2.1, fun e0 He0 => by simp [storAbsorb] at He0,
      fun h1 h2 => Hfl.2.2.2.2 h1 h2⟩
  -- (D22 S-d2) at the pending snapshot nothing was unpersisted: the storage is unchanged
  have Hsat' : ls.sat = true → SatOk (storAbsorb σ) { ls with unpersisted := [] } := by
    intro h
    obtain ⟨H1, H2, H3, H4, H5, H6, H7, H8⟩ := Hsat h
    rw [Hab]
    refine ⟨H1, H2, H3, rfl, H5, H6, ?_, rfl⟩
    show storApp σ ls.unpersisted = ls.stored
    rw [H4]; exact H7
  iapply ownRaftLog_intro l lv lv.storage' _ _ _ { ls with unpersisted := [] } rfl Hcm Hap Hidx
    Hnowrap Hstore' Hoffset Happlied Hpapplied Hcommitted Hssnap' Hapg Hip Hipb
    Hpersist' Happlying Hpaused Hasz Hamx Hstor Hpend' Hfl' Hsksn Hsip Hsipn Hlent Hq Hprel Hsat' rfl rfl rfl rfl $$ Hl HisStorage [HStorage]
    Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger
  iapply lentStor_close Hlt; iexact HStorage

/-- (D19i part 1) **Raising the floor** to `x`, between the floor and `applying`, with nothing
unpersisted and the storage not lent: the storage's floor law
(`isStorageWith`'s `Hfloor`) gives the application the witness `storFloor` (its right to compact
and snapshot up to `x`). With no snapshot pending the storage holds the log up to
`offsetInProgress` (`LogPersistOk`), past `applying` (`FlOk`), so up to `x`; with one (restored
since the last `Ready`, D22 S-d4 item 3) it holds the log up to `applying` (`StorExtOk`). -/
theorem ownRaftLog_raise_floor (l : Loc) (ls : LogState) (x : w64)
    (Hx : uint.Z ls.fl ≤ uint.Z x ∧ uint.Z x ≤ uint.Z ls.applying)
    (Hunp : ls.unpersisted = []) (Hlnt : ls.lent = false) :
    ⊢ ownRaftLog (GF := GF) l ls ==∗
      ownRaftLog l { ls with fl := x } ∗ storFloor ls.storage x := by
  iintro H
  iNamed H
  ihave #Hsto : isStorageWith (ownStorage lv.storage') (appendTok lv.storage')
      (appendedTok lv.storage') (storCut lv.storage') (storFloor lv.storage') (storCert lv.storage') lv.storage' $$ [HisStorage]
  · unfold isStorage; iexact HisStorage
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  have Hpσ : σ.pend = [] := Hpend.1.trans Hunp
  ihave HStorage := lentStor_open Hlnt _ _ $$ HStorage
  have Hlt := Hfl.2.2.1
  have Hxle : uint.Z x ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) := by
    rcases Option.eq_none_or_eq_some ls.snap with Hsn | ⟨sid, Hsn⟩
    · obtain ⟨Hsp, -, -⟩ : LogStoreOk none σ ls.prev ls.sents ls.uents := Hsn ▸ Hstore
      have Hp0 := Hpersist Hsn
      rw [Hunp] at Hp0
      have Hplen := Hp0.1.length_le
      simp only [storApp, List.length_append, List.length_take] at Hplen
      rw [Hsp]
      have : (min (uint.Z ls.inprogress - uint.Z lv.unstable'.offset').toNat ls.uents.length : Int)
          = uint.Z ls.inprogress - uint.Z lv.unstable'.offset' := by omega
      omega
    · have He := Hfl.2.2.2.2 (by rw [Hsn]; simp) Hlnt
      have He2 := He.2
      have He1 := He.1
      rw [Hpσ] at He1
      simp only [storApp] at He1
      omega
  have Hpre : σ.pend = [] ∧ uint.Z σ.fl ≤ uint.Z x ∧
      uint.Z x ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) :=
    ⟨Hpσ, by rw [Hfl.1]; exact Hx.1, Hxle⟩
  imod Hfloor $$ %σ %x HStorage %Hpre with ⟨HStorage, Hfw⟩
  imodintro
  isplitr [Hfw]
  · have Hfl' : FlOk { σ with fl := x } { ls with fl := x } :=
      ⟨rfl, Hx.2, Hfl.2.2.1, fun e0 He0 => by simp [Hpσ] at He0, Hfl.2.2.2.2⟩
    have Hpend' : PendLogOk { σ with fl := x } { ls with fl := x } := Hpend
    have Hpersist' : ls.snap = none →
        LogPersistOk { σ with fl := x } ls.sents ls.uents
          (uint.Z ls.inprogress - uint.Z lv.unstable'.offset') ls.unpersisted ls.stored := Hpersist
    have Hssnap' : ls.snap = none →
        StoredSnapOk { σ with fl := x } ls.committed ls.prev (ls.sents ++ ls.uents) := Hssnap
    have Hstore' : LogStoreOk ls.snap { σ with fl := x } ls.prev ls.sents ls.uents := Hstore
    iapply ownRaftLog_intro l lv lv.storage' _ _ _ { ls with fl := x } rfl Hcm Hap Hidx
      Hnowrap Hstore' Hoffset Happlied Hpapplied Hcommitted Hssnap' Hapg Hip Hipb
      Hpersist' Happlying Hpaused Hasz Hamx Hstor Hpend' Hfl' Hsksn Hsip Hsipn Hlent Hq Hprel Hsat rfl rfl rfl rfl $$ Hl HisStorage [HStorage]
      Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger
    iapply lentStor_close Hlnt; iexact HStorage
  rw [← Hstor]
  iexact Hfw

/-- (D19i part 1) The floor, read out without consuming the log: at most `applying`, so at most
`committed` and the last index; below `offsetInProgress` with no snapshot pending. -/
theorem ownRaftLog_fl (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜uint.Z ls.fl ≤ uint.Z ls.applying ∧ uint.Z ls.applying ≤ uint.Z ls.committed ∧
        uint.Z ls.committed ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
          + (ls.uents.length : Int) ∧
        (ls.snap = none → uint.Z ls.fl < uint.Z ls.inprogress)⌝ ∗
      ownRaftLog l ls := by
  iintro H0
  iNamed H0
  isplitr
  · ipureintro
    exact ⟨Hfl.2.1, Happlying.2, Hcommitted, fun _ => Int.lt_of_le_of_lt Hfl.2.1 Hfl.2.2.1⟩
  · iapply ownRaftLog_intro l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
      Happlied Hpapplied Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying
      Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn Hsip Hsipn Hlent Hq Hprel Hsat rfl rfl rfl rfl $$ Hl HisStorage HStorage Husnap Hpksn Hkcert Huents
      Huents_cap Hl_logger Hu_logger

/-- (D22 S-d1b) The stable part ends below `2^61`: from `isStorage`'s bound with no snapshot
pending (the storage is then not lent), from the pending snapshot's index otherwise (the stable
part is empty). -/
theorem ownRaftLog_stable_bound (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜uint.Z ls.prev.index' + (ls.sents.length : Int) < 2^61⌝ ∗ ownRaftLog l ls := by
  iintro H0
  iNamed H0
  rcases Option.eq_none_or_eq_some ls.snap with Hs | ⟨sid, Hs⟩
  · have Hlnt := lent_false_of Hlent Hs
    ihave HStorage := lentStor_open Hlnt _ _ $$ HStorage
    ihave #Hsto : isStorage (GF := GF) lv.storage' $$ []
    · iexact HisStorage
    iunfold isStorage at Hsto
    iunfold isStorageWith at Hsto
    icases Hsto with ⟨%isv, #Hst⟩
    iNamed Hst
    icases Hbounded $$ %σ HStorage with ⟨%Hstb, HStorage⟩
    obtain ⟨Hsp, Hstored, -⟩ : LogStoreOk none σ ls.prev ls.sents ls.uents := Hs ▸ Hstore
    have := Hstored.length_le
    rw [Hsp] at Hstb
    isplitr [Hl HStorage Huents Huents_cap]
    · ipureintro; omega
    ihave HStorage := lentStor_close Hlnt _ _ $$ HStorage
    iapply ownRaftLog_intro l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
      Happlied Hpapplied Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying
      Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn Hsip Hsipn Hlent Hq Hprel Hsat rfl rfl rfl rfl $$ Hl
      HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger
  · obtain ⟨Hp, Hs0, Hsid⟩ : LogStoreOk (some sid) σ ls.prev ls.sents ls.uents := Hs ▸ Hstore
    isplitr [Hl HStorage Huents Huents_cap]
    · ipureintro; rw [Hs0, List.length_nil, Hp]; omega
    iapply ownRaftLog_intro l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
      Happlied Hpapplied Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying
      Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn Hsip Hsipn Hlent Hq Hprel Hsat rfl rfl rfl rfl $$ Hl
      HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger

/-- (D22 S-d1b) A quiet log is outside both windows. -/
theorem ownRaftLog_quiet (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗ ⌜ls.sapp = false ∧ ls.aps = false⌝ ∗ ownRaftLog l ls := by
  iintro H0
  iNamed H0
  isplitr
  · ipureintro; exact Hq
  iapply ownRaftLog_intro l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
    Happlied Hpapplied Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying
    Hpaused Hasz Hamx Hstor Hpend Hfl Hsksn Hsip Hsipn Hlent Hq Hprel Hsat rfl rfl rfl rfl $$ Hl
    HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger

/-- `Hnowrap`, read out without consuming the log. Needed to know `lastIndex() + 1`
does not wrap, which is what makes the range premises of `raftLog.slice` and
`raftLog.mustCheckOutOfBounds` hold. -/
theorem ownRaftLog_nowrap (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜uint.Z ls.prev.index' + (ls.sents.length : Int)
         + (ls.uents.length : Int) + 1 < 2^64⌝ ∗
      ownRaftLog l ls :=
  ownRaftLog_pure l ls _ fun _ _ _ Hnowrap _ _ _ _ _ _ _ => Hnowrap

/-- `Hidx` and the commit bounds, read out without consuming the log. -/
theorem ownRaftLog_wf (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜LogIndicesOk ls.prev (ls.sents ++ ls.uents)⌝ ∗
      ownRaftLog l ls :=
  ownRaftLog_pure l ls _ fun _ _ Hidx _ _ _ _ _ _ _ _ => Hidx

theorem ownRaftLog_committed (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜(uint.Z ls.prev.index' ≤ uint.Z ls.committed ∧
        uint.Z ls.applied ≤ uint.Z ls.committed ∧
        uint.Z ls.committed ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
          + (ls.uents.length : Int)) ∧
       (ls.snap = none → uint.Z ls.prev.index' ≤ uint.Z ls.applied)⌝ ∗
      ownRaftLog l ls :=
  ownRaftLog_pure l ls _ fun _ _ _ _ _ _ Happlied Hpapplied Hcommitted _ _ =>
    ⟨⟨Happlied.1, Happlied.2, Hcommitted⟩, Hpapplied⟩

omit [GoGlobalContext] in
/-- An entry `Storage.Entries` hands back for a range ending at or below
`unstable.offset` is an entry of the *visible* stable part `sents` (`isStorage`'s
`HEntries` bounds it by `hi`; `Hstored` makes the prefix below `hi` a prefix of
`sents`). -/
theorem stored_take_visible (prev : entryID) (sents stored : List EntryM) (hi : w64)
    (e : EntryM) (Hpre : sents <+: stored)
    (Hhi : uint.Z hi ≤ uint.Z prev.index' + (sents.length : Int) + 1)
    (He : e ∈ stored.take (uint.Z hi - uint.Z prev.index' - 1).toNat) : e ∈ sents := by
  obtain ⟨k, rfl⟩ := Hpre
  rw [List.take_append_of_le_length (by omega)] at He
  exact List.mem_of_mem_take He

/-- `offsetInProgress` after `unstable.truncateAndAppend` of a batch starting at `f`:
unchanged when the batch continues the log (the `append` arm), otherwise
`min(offsetInProgress, f)` -- the replace arm sets it to `f` (the new offset, at or
below the old one), the truncate arm to `min(offsetInProgress, f)`. (2026-10-05) -/
def logTruncInprogress (ls : LogState) (f : w64) : w64 :=
  if uint.Z f < uint.Z ls.prev.index' + (ls.sents.length : Int)
                  + (ls.uents.length : Int) + 1
  then (if uint.Z f < uint.Z ls.inprogress then f else ls.inprogress)
  else ls.inprogress

omit [GoGlobalContext] in
/-- The persistence invariant survives `truncateAndAppend`: what is handed out
afterwards (`k'` unstable entries past a stable part cut at the batch's position `m`) is
a prefix of what was handed out before (`kip` past the old stable part). `k'` is what
`logTruncInprogress` leaves: `kip` when the batch continues the log, at most `kip` and
at most the kept part of the suffix otherwise. -/
theorem persist_prefix_truncate {A : Type _} (sents uents ents : List A) (m kip k' : Nat)
    (Hkip : kip ≤ uents.length)
    (Hm : m ≤ sents.length + uents.length)
    (Hlt : m < sents.length + uents.length → k' ≤ kip ∧ k' ≤ m - sents.length)
    (Heq : m = sents.length + uents.length → k' = kip) :
    (sents.take m ++ (uents.take (m - sents.length) ++ ents).take k')
      <+: (sents ++ uents.take kip) := by
  by_cases He : m = sents.length + uents.length
  · rw [Heq He, He, List.take_of_length_le (by omega),
      show sents.length + uents.length - sents.length = uents.length by omega,
      List.take_of_length_le (Nat.le_refl _), List.take_append_of_le_length Hkip]
    exact List.prefix_refl _
  · obtain ⟨Hk1, Hk2⟩ := Hlt (by omega)
    by_cases Hge : sents.length ≤ m
    · rw [List.take_of_length_le Hge]
      apply List.prefix_append_right_inj sents |>.2
      rw [List.take_append_of_le_length (by rw [List.length_take]; omega), List.take_take,
        show min k' (m - sents.length) = min k' kip by omega, ← List.take_take]
      exact List.take_prefix _ _
    · rw [show k' = 0 by omega, List.take_zero, List.append_nil]
      exact (List.take_prefix _ _).trans (List.prefix_append _ _)

/-! ## Appending with truncation (`raftLog.append`)

`logTruncateAppend ls ents` is the log state `raftLog.append(ents)` leaves: everything
below `ents[0].Index` is kept, then `ents`. When the batch starts inside the stable part
(`unstable.truncateAndAppend`'s `fromIndex <= u.offset` arm) the *visible* stable part
`sents` shrinks to the entries below it and `ents` becomes the whole unstable suffix;
the storage keeps the shadowed tail (`ownRaftLog`'s `σ.ents`). Otherwise `sents`
is unchanged and the unstable suffix is cut at `ents[0].Index` and extended.
`Spec/raftLog__append.lean` relates it to `plogTruncateAppend`. -/
def logTruncateAppend (ls : LogState) (ents : List EntryM) : LogState :=
  match ents with
  | [] => ls
  | e0 :: _ =>
      { ls with
          sents := ls.sents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1).toNat,
          uents := ls.uents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1
                                   - (ls.sents.length : Int)).toNat ++ ents,
          inprogress := logTruncInprogress ls e0.Index' }

/-- Whether `unstable.truncateAndAppend` takes its replace arm and adopts the caller's
slice as `u.entries`: the batch starts at or below `u.offset` and does not simply
continue the suffix (with an empty suffix and `ents[0].Index = u.offset` the first arm,
`append`, wins). -/
def logAdopts (ls : LogState) (ents : List EntryM) : Bool :=
  match ents with
  | [] => false
  | e0 :: _ =>
      decide (uint.Z e0.Index' ≤ uint.Z ls.prev.index' + (ls.sents.length : Int) + 1 ∧
              uint.Z e0.Index' ≠ uint.Z ls.prev.index' + (ls.sents.length : Int)
                + (ls.uents.length : Int) + 1)

omit [GoGlobalContext] in
/-- A batch that continues the log is a plain `logAppend`. -/
theorem logTruncateAppend_cont (ls : LogState) (ents : List EntryM)
    (H : ∀ e0, ents[0]? = some e0 →
      uint.Z e0.Index' = uint.Z ls.prev.index' + (ls.sents.length : Int)
        + (ls.uents.length : Int) + 1) :
    logTruncateAppend ls ents = logAppend ls ents ∧ logAdopts ls ents = false := by
  cases ents with
  | nil => simp [logTruncateAppend, logAdopts, logAppend]
  | cons e0 ents' =>
    have H0 := H e0 rfl
    simp only [logTruncateAppend, logAdopts, logAppend]
    refine ⟨?_, ?_⟩
    · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      simp only [logTruncInprogress, show ¬ (uint.Z e0.Index' < uint.Z ls.prev.index'
        + (ls.sents.length : Int) + (ls.uents.length : Int) + 1) by omega, ite_false]
    · simp only [decide_eq_false_iff_not]; omega

/-! ## Reading the log through `scan`

`raftLog.scan lo hi pageSize v` pages through `[lo, hi)` and hands each page to the
callback `v` as a slice of the log's entries, read-only (a sub-slice of
`unstable.entries`, or one the `Storage` handed out, or a fresh concatenation).
`scanClosure f L I B` is what `raftLog.wp_scan` asks of the callback, for the scanned
range `L` (`scanRange`: the log's entries at `[lo, hi)`, in order): given a non-empty page
`es` that continues the pages `acc` already seen inside `L` (`acc ++ es <+: L`), with the
caller's state `I acc`, it returns `nil` and `I (acc ++ es)`, or (since 2026-10-13) stops
the scan with a non-`nil` error `err` and `B err` -- `errBreak` in
`hasUnappliedConfChanges`. (Until 2026-10-13 the closure had to return `nil`, with an
invariant `I` and a fact `P` of every entry instead of the pages' positions.) -/
def scanClosure (f : GoFunc) (L : List EntryM) (I : List EntryM → IProp GF)
    (B : GoInterface → IProp GF) : IProp GF :=
  iprop(∀ (s : GoSlice) (acc es : List EntryM) (dq : DFrac),
    {{ entsPts s dq es ∗ ⌜es ≠ [] ∧ acc ++ es <+: L⌝ ∗ I acc }}
      (App (Val #f) (Val #s))
    {{ (err : GoInterface), RET #err; entsPts s dq es ∗
        ((⌜err = interface.nil⌝ ∗ I (acc ++ es)) ∨ (⌜err ≠ interface.nil⌝ ∗ B err)) }})

/-! `scanRange` and `unappliedEnts` are in `SpecResults.lean` (moved there in stage R1). -/

/-- Two slice values with the same pointer and length own the same elements.
`unstable.slice` and `raftLog.slice` return three-index slices (`s[lo:hi:hi]`) whose
capacity differs from the `slice.slice` form the ownership lemmas (`ownSlice_slice`)
speak about; this moves the points-to across. Needs a non-empty list, because for an
empty one `ownSlice` may hold through its `slice.nil` disjunct, which fixes the
capacity too. -/
theorem ownSlice_same_ptr_len {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s1 s2 : GoSlice) (dq : DFrac) (vs : List V) :
    vs ≠ [] →
    s1.ptr = s2.ptr →
    s1.len = s2.len →
    sint.Z s2.len ≤ sint.Z s2.cap →
    ⊢ (s1 ↦*{dq} vs : IProp GF) -∗ s2 ↦*{dq} vs := by
  intro Hne Hptr Hlen Hcap
  obtain ⟨p1, l1, c1⟩ := s1
  obtain ⟨p2, l2, c2⟩ := s2
  simp only at Hptr Hlen Hcap
  subst Hptr Hlen
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %_⟩)
  · exact absurd H.2 Hne
  · iright
    iframe H
    ipureintro; exact Hcap

/-- Split the `unstable` field out of `l ↦ lv`, keeping a wand that accepts *any* new
value for it. Since 2026-10-08 every `raftLog` method that calls an `unstable` method
splits the field this way: `ownUnstable` keeps the Goose value existential, so every
such call hands back a value the caller has not seen, which the `AccessStrict` store
instance (the former macro `split_unstable`) cannot take, its evar being created before
the call (notes/gotchas.md, "The `AccessStrict` store instance cannot take a value the
call has not produced yet"). Moved here from `proof_raftLog__append.v` on 2026-10-02
for `raftLog.restore`. -/
theorem raftLog_split_unstable (l : Loc) (lv : raftLog) :
    ⊢ (l ↦ lv : IProp GF) -∗
      l.[raftLog, go!"unstable"] ↦ lv.unstable' ∗
      (∀ uv, l.[raftLog, go!"unstable"] ↦ uv -∗ l ↦ { lv with unstable' := uv }) := by
  rw [typedPointsto_unseal_eq l lv]
  simp only [TypedPointsto.typedPointstoDef]
  iintro ⟨Hf, %Hnn⟩
  icases Hf with ⟨Hs, Hu, Hrest⟩
  iframe Hu
  iintro %uv Huv
  iapply typedPointsto_combine l _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe Hs Huv Hrest


/-- Open the `ownUnstable` a `raftLog` method handed to an `unstable` method (the field
split off with `raftLog_split_unstable`) and put the struct back together at the new
value, with the pieces `ownRaftLog` keeps on it. For a method that leaves the state
as it was, `ownUnstable_return` below states it at `unstableOf`. -/
theorem ownUnstable_reopen (l : Loc) (lv : raftLog) (us : UnstableSt) :
    ⊢ (∀ uv, l.[raftLog, go!"unstable"] ↦ uv -∗ (l ↦ { lv with unstable' := uv } : IProp GF)) -∗
      ownUnstable l.[raftLog, go!"unstable"] us -∗
      ∃ uv, l ↦ { lv with unstable' := uv } ∗
        ownSliceCap Loc uv.entries' (DFrac.own 1) ∗
        entsRO uv.entries' us.ents ∗ ownSnap uv.snapshot' us.snap ∗
        pendKsn uv.snapshot' us.snap us.ksn ∗ isLoggerVal uv.logger' ∗
        ⌜uv.offset' = us.offset⌝ ∗ ⌜uv.offsetInProgress' = us.inprogress⌝ ∗
        ⌜uv.snapshotInProgress' = us.sip⌝ := by
  iintro Hlback Hun
  iunfold ownUnstable at Hun
  iNamed Hun
  ihave Hl := Hlback $$ Hu
  iexists uv
  iframe Hl Hents_cap Hents Hsnap Hpksn Hlogger
  ipureintro
  exact ⟨Hoff, Hoip, Hsip⟩

/-- Lend the `unstable` field of the log at `l ↦ lv` to an `unstable` method, at
`unstableOf lv ls`, from the pieces `ownRaftLog` keeps on it (`iNamed Hlog` names them;
`Hip` is the premise). The wand takes the field back at any value. (Since 2026-10-09;
until then `raftLog_split_unstable` and the macro `close_unstable_log`, at a literal
record.) -/
theorem raftLog_lend_unstable (l : Loc) (lv : raftLog) (ls : LogState) :
    lv.unstable'.offsetInProgress' = ls.inprogress →
    lv.unstable'.snapshotInProgress' = ls.sip →
    ⊢ (l ↦ lv : IProp GF) -∗
      ownSliceCap Loc lv.unstable'.entries' (DFrac.own 1) -∗
      entsRO lv.unstable'.entries' ls.uents -∗
      ownSnap lv.unstable'.snapshot' ls.snap -∗
      pendKsn lv.unstable'.snapshot' ls.snap ls.ksn -∗
      isLoggerVal lv.unstable'.logger' -∗
      ownUnstable l.[raftLog, go!"unstable"] (unstableOf lv ls) ∗
      (∀ uv, l.[raftLog, go!"unstable"] ↦ uv -∗ l ↦ { lv with unstable' := uv }) := by
  intro Hip Hsip
  iintro Hl Hcap #Hents #Hsnap #Hpksn #Hlogger
  icases raftLog_split_unstable l lv $$ Hl with ⟨Huf, Hlback⟩
  iframe Hlback
  unfold unstableOf
  iapply ownUnstable_intro $$ Huf Hcap Hents Hsnap Hpksn Hlogger
  ipureintro
  exact ⟨rfl, Hip, Hsip⟩

/-- `ownUnstable_reopen` for an `unstable` method that leaves the state `unstableOf lv ls`
as it was: the struct at the new value `uv`, with the pieces `ownRaftLog` keeps, and
`uv`'s `offset` and `offsetInProgress` those `ownRaftLog` knows. -/
theorem ownUnstable_return (l : Loc) (lv : raftLog) (ls : LogState) :
    ⊢ (∀ uv, l.[raftLog, go!"unstable"] ↦ uv -∗ (l ↦ { lv with unstable' := uv } : IProp GF)) -∗
      ownUnstable l.[raftLog, go!"unstable"] (unstableOf lv ls) -∗
      ∃ uv, l ↦ { lv with unstable' := uv } ∗
        ownSliceCap Loc uv.entries' (DFrac.own 1) ∗
        entsRO uv.entries' ls.uents ∗ ownSnap uv.snapshot' ls.snap ∗
        pendKsn uv.snapshot' ls.snap ls.ksn ∗ isLoggerVal uv.logger' ∗
        ⌜uv.offset' = lv.unstable'.offset'⌝ ∗ ⌜uv.offsetInProgress' = ls.inprogress⌝ ∗
        ⌜uv.snapshotInProgress' = ls.sip⌝ :=
  ownUnstable_reopen l lv (unstableOf lv ls)

end proof

set_option hygiene false in
/-- Re-seal `ownRaftLog l ls` from the hypotheses `iNamed Hlog` introduced
(`ownRaftLog_intro`). The pure premises are closed by reducible `rfl` or `assumption`
(Rocq `try done`; a plain `assumption` runs out of recursion depth on the `2^64`
bounds), or, after `reopen_unstable`, by the same once rewritten with `Huoff`. -/
macro "reseal_raftLog" : tactic =>
  `(tactic| (try (ihave HStorage := Perennial.EtcdGrove.lentStor_close Hlnt _ _ $$ HStorage)) <;>
    (iapply Perennial.EtcdGrove.ownRaftLog_intro _ _ _ _ _ _ _ $$ Hl HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger) <;>
    try (first | with_reducible rfl | with_reducible assumption
               | ((rewrite [Huoff]); with_reducible assumption)
               -- the storage and its pending batch (2026-10-10), for a state that
               -- keeps the fields they are stated on
               | exact Hstor | exact Hpend | exact Hfl))

set_option hygiene false in
/-- `reseal_raftLog` for `ownRaftLogW` (`ownRaftLogW_intro`). -/
macro "reseal_raftLogW" : tactic =>
  `(tactic| (try (ihave HStorage := Perennial.EtcdGrove.lentStor_close Hlnt _ _ $$ HStorage)) <;>
    (iapply Perennial.EtcdGrove.ownRaftLogW_intro _ _ _ _ _ _ _ $$ Hl HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger) <;>
    try (first | with_reducible rfl | with_reducible assumption
               | ((rewrite [Huoff]); with_reducible assumption)
               | exact Hstor | exact Hpend | exact Hfl))

set_option hygiene false in
/-- (D22 S-d1b) In a `raftLog` method, after `iNamed Hlog`, in a branch where `h : ls.snap = none`:
the storage is not lent (`Hlnt`), and `HStorage` is `ownStorage`; `reseal_raftLog` turns it back. -/
macro "take_storage" h:ident : tactic =>
  `(tactic| (
    have Hlnt := Perennial.EtcdGrove.lent_false_of Hlent $h
    ihave HStorage := Perennial.EtcdGrove.lentStor_open Hlnt _ _ $$ HStorage))

section setCommitted
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The raw store `l.committed = n` (2026-10-16, stage R8b: `RawNode.Bootstrap`'s
`rn.raft.raftLog.committed = uint64(len(ents))`, with no `commitTo` guard), for `n` within the log
and at or above `applying` (so above `applied`) and the old commit index (`StoredSnapOk` is
monotone in it): the rest of `ownRaftLog` does not mention the commit index. Stated on the field
store as `wp_auto` leaves it after loading the `raftLog` pointer. -/
theorem ownRaftLog_setCommitted (l : Loc) (ls : LogState) (n : w64)
    (Hlo : uint.Z ls.prev.index' ≤ uint.Z n)
    (Hhi : uint.Z n ≤ uint.Z ls.prev.index' + (ls.sents.length : Int) + (ls.uents.length : Int))
    (Happ : uint.Z ls.applying ≤ uint.Z n)
    (Hcm : uint.Z ls.committed ≤ uint.Z n) (Φ : val → IProp GF) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      (ownRaftLog l { ls with committed := n } -∗ Φ #()) -∗
      WP (App (Val (GoInstruction (GoStore go.uint64)))
            (Val (PairV #(l.[raftLog, go!"committed"]) #n))) {{ Φ }} := by
  iintro Hlog HΦ
  iNamed Hlog
  wp_auto
  iapply HΦ
  reseal_raftLog
  all_goals first
    | word
    | (intro Hs; exact StoredSnapOk_commit _ _ _ _ _ (by word) (Hssnap Hs))

end setCommitted

set_option hygiene false in
/-- Open `Hun : ownUnstable u us` in the proof of an `unstable` method
(`ownUnstable_open`): the Goose value `uv`, with the struct at
`{ uv with offset' := us.offset, offsetInProgress' := us.inprogress }`, and the pieces
`Hu`, `Hents_cap`, `Hents`, `Hsnap`, `Hlogger`. `us` stays a variable: the proof works
on `us.offset` and `us.inprogress` throughout. (Until 2026-10-09 it destructured `us`
and substituted the value's fields for the record's.) -/
macro "open_unstable" : tactic =>
  `(tactic| (
    icases Perennial.EtcdGrove.ownUnstable_open _ _ $$ Hun
      with ⟨%uv, Hu, Hents_cap, Hents, #Hsnap, #Hpksn, #Hlogger⟩))

set_option hygiene false in
/-- Reopen `Hun` after the proof of an `unstable` method handed it, closed by
`close_unstable`, to another `unstable` method: as `open_unstable`, at the new value
`uv` (the old one becomes inaccessible). -/
macro "open_unstable_again" : tactic =>
  `(tactic| (
    iclear Hsnap Hlogger
    open_unstable))

set_option hygiene false in
/-- Close `ownUnstable u us'` from the pieces `open_unstable` named
(`ownUnstable_intro`): the value's `offset` and `offsetInProgress` are `us'`'s by
construction. -/
macro "close_unstable" : tactic =>
  `(tactic| (
    iapply Perennial.EtcdGrove.ownUnstable_intro $$ Hu Hents_cap Hents Hsnap Hpksn Hlogger
    ipureintro
    exact ⟨rfl, rfl, rfl⟩))

set_option hygiene false in
/-- In a `raftLog` method, after `iNamed Hlog`: lend the `unstable` field to an
`unstable` method (`raftLog_lend_unstable`) as `Hun : ownUnstable _ (unstableOf lv ls)`,
with `Hlback` the wand that takes it back. (Since 2026-10-09; until then
`raftLog_split_unstable` and `close_unstable_log` at the call.) -/
macro "lend_unstable" : tactic =>
  `(tactic| (
    icases Perennial.EtcdGrove.raftLog_lend_unstable _ _ _ Hip Hsip $$ Hl Huents_cap Huents Husnap
      Hpksn Hu_logger with ⟨Hun, Hlback⟩))

set_option hygiene false in
/-- After a `raftLog` method has lent the `unstable` field (`lend_unstable`) to an
`unstable` method that leaves its state as it was (`ownUnstable _ (unstableOf lv ls)` in
and out), take it back with `Hlback` (`ownUnstable_return`): `Hl` is then the log at the
new value `uv'`, `Huents_cap`, `Huents`, `Husnap` and `Hu_logger` are its pieces,
`Huoff` says its `offset` is the old value's (which `reseal_raftLog` rewrites with), and
`Hip` its `offsetInProgress` is `ls.inprogress`, so that `reseal_raftLog` closes the log
as before. -/
macro "reopen_unstable" : tactic =>
  `(tactic| (
    iclear Husnap Hpksn Hu_logger
    clear Hip Hsip
    icases Perennial.EtcdGrove.ownUnstable_return _ _ _ $$ Hlback Hun
      with ⟨%uv', Hl, Huents_cap, Huents, #Husnap, #Hpksn, #Hu_logger, %Huoff, %Hip, %Hsip⟩))

section snpok
variable [FfiSyntax]

/-- (D22 S-d4 item 3, 2026-10-21) What the log keeps of the snapshot the last `Ready` handed out
(`NGhost.snp`) once the storage is back (`lent = false`, inside `RawNode.Advance`): with a snapshot
pending the storage holds the log up to it (`LogState.sxt`, set by the absorption of the receipt:
also when a later snapshot was restored meanwhile, where `appliedSnap` moves `applying` to the
handed-out one, `StorExtOk`), and once the pending one is dropped and `appliedSnap`'s window has
ended, `applying` is past it. -/
def SnpExt (g : NGhost) (ls : LogState) : Prop :=
  ∀ k, g.snp = some k → ls.lent = false →
    (ls.snap ≠ none → uint.Z k.sid.index' ≤ uint.Z ls.sxt) ∧
    (ls.snap = none → ls.aps = false → uint.Z k.sid.index' ≤ uint.Z ls.applying)

/-- (D22 S-d3a, 2026-10-21) What the log keeps of the snapshot the last `Ready` handed out
(`NGhost.slent`, `NGhost.snp`): the storage lent exactly when `slent`; while the snapshot handed
out (`snp`) is the pending one, it is in progress and the storage lent or at it (`sat`), and it is
a snapshot the node may send (`ksn`) at most the commit index (so a later restore, past the commit
index, is of another snapshot); and a snapshot in progress or absorbed has one recorded; (D22 S-d3b,
2026-10-21) and the storage is at the pending snapshot (`sat`) only when that is the one handed out
(an absorption after a second restore leaves it shadowed, `logAbsorbSnap`), and in progress only
then. A mirror
of the log's ghost fields in `NGhost`, which every step keeps (`NetFrame`, `LocalFrame`,
`SnapStep`: `s'.gh = s.gh`), so that the `RawNode` knows them across the steps between a snapshot's
`Ready` and its `Advance`. -/
def SnpOk (g : NGhost) (ls : LogState) : Prop :=
  ls.lent = g.slent ∧
  (∀ k, g.snp = some k →
    (ls.snap = some k.sid → ls.sip = true ∧ (ls.lent = true ∨ ls.sat = true)) ∧
    k ∈ ls.ksn ∧ uint.Z k.sid.index' ≤ uint.Z ls.committed) ∧
  (ls.sip = true ∨ ls.sat = true → g.snp ≠ none) ∧
  (ls.sip = true ∨ ls.sat = true → ∃ k, g.snp = some k ∧ ls.snap = some k.sid) ∧
  SnpExt g ls

/-- `SnpOk` of a log that keeps the fields it reads (`hx`: by default the fields `SnpExt` reads
are the same). -/
theorem SnpOk.of_fields {g : NGhost} {ls ls' : LogState} (H : SnpOk g ls)
    (hlt : ls'.lent = ls.lent) (hsn : ls'.snap = ls.snap) (hsip : ls'.sip = ls.sip)
    (hsat : ls'.sat = ls.sat) (hk : ls'.ksn = ls.ksn)
    (hcm : uint.Z ls.committed ≤ uint.Z ls'.committed)
    (hx : SnpExt g ls → SnpExt g ls' := by exact fun h => h) : SnpOk g ls' := by
  obtain ⟨H1, H2, H3, H4, H5⟩ := H
  refine ⟨hlt.trans H1, fun k hk' => ?_, fun h => H3 (by rw [← hsip, ← hsat]; exact h),
    fun h => by rw [hsn]; exact H4 (by rw [← hsip, ← hsat]; exact h), hx H5⟩
  obtain ⟨Ha, Hb, Hc⟩ := H2 k hk'
  refine ⟨fun h => ?_, hk ▸ Hb, Int.le_trans Hc hcm⟩
  rw [hsip, hsat, hlt]; exact Ha (hsn ▸ h)

/-- `SnpOk` with nothing pending, in progress, absorbed or lent. -/
theorem SnpOk.of_quiet {g : NGhost} {ls : LogState} (hlt : ls.lent = g.slent)
    (hsn : ls.snap = none) (hsip : ls.sip = false) (hsat : ls.sat = false)
    (hk : ∀ k, g.snp = some k → k ∈ ls.ksn ∧ uint.Z k.sid.index' ≤ uint.Z ls.committed)
    (hx : SnpExt g ls) :
    SnpOk g ls :=
  ⟨hlt, fun k h => ⟨(fun h' => by rw [hsn] at h'; cases h'), hk k h⟩,
    (fun h => by rcases h with h | h <;> simp_all), (fun h => by rcases h with h | h <;> simp_all),
    hx⟩

/-- (D22 S-d3b) `SnpOk` with nothing handed out, in progress, absorbed or lent (a snapshot may be
pending: one restored after the last `Ready`). -/
theorem SnpOk.of_none {g : NGhost} {ls : LogState} (hlt : ls.lent = g.slent)
    (hsnp : g.snp = none) (hsip : ls.sip = false) (hsat : ls.sat = false) : SnpOk g ls :=
  ⟨hlt, fun k h => (by rw [hsnp] at h; cases h),
    (fun h => by rcases h with h | h <;> simp_all), (fun h => by rcases h with h | h <;> simp_all),
    fun k h => by rw [hsnp] at h; cases h⟩

/-- (D22 S-d3a) `SnpOk` after a restore past the commit index: the snapshot restored is not the
one handed out (at most the commit index), and is not in progress. -/
theorem SnpOk.restore {g : NGhost} {ls : LogState} (k : SnapTrip) (H : SnpOk g ls)
    (Hgt : uint.Z ls.committed < uint.Z k.sid.index')
    -- (D22 S-d4 item 3) outside `appliedSnap`'s window (a quiet log)
    (Haps : ls.aps = false) : SnpOk g (logRestore ls k) := by
  obtain ⟨H1, H2, -, -, H5⟩ := H
  refine ⟨H1, fun k0 hk0 => ?_, fun h => by simp [logRestore] at h,
    fun h => by simp [logRestore] at h, fun k0 hk0 hl => ⟨fun _ => ?_, fun h => by
      simp [logRestore] at h⟩⟩
  rotate_left
  · have hl' : ls.lent = false := hl
    show uint.Z k0.sid.index' ≤
      uint.Z (if ls.snap.isSome ∧ uint.Z ls.applying ≤ uint.Z ls.sxt then ls.sxt else ls.applying)
    rcases Option.eq_none_or_eq_some ls.snap with Hs | ⟨sid, Hs⟩
    · have := (H5 k0 hk0 hl').2 Hs Haps
      rw [if_neg (by simp [Hs])]; exact this
    · have := (H5 k0 hk0 hl').1 (by rw [Hs]; simp)
      split
      · exact this
      · rename_i hc
        simp only [Hs, Option.isSome_some, true_and] at hc
        omega
  obtain ⟨-, Hb, Hc⟩ := H2 k0 hk0
  refine ⟨fun h => ?_, List.mem_append_left _ Hb, ?_⟩
  · exfalso
    have h' : k.sid = k0.sid := Option.some.inj h
    rw [h'] at Hgt
    omega
  · show uint.Z k0.sid.index' ≤ uint.Z k.sid.index'
    omega

/-- (D22 S-d3a) The log fields `SnpOk` reads but the pending snapshot and the commit index. -/
def SnpKeep (ls ls' : LogState) : Prop :=
  ls'.lent = ls.lent ∧ ls'.sip = ls.sip ∧ ls'.sat = ls.sat ∧ ls'.ksn = ls.ksn ∧
  -- (D22 S-d4 item 3) and what `SnpExt` reads
  ls'.sxt = ls.sxt ∧ ls'.aps = ls.aps ∧ ls'.applying = ls.applying

theorem SnpKeep.refl (ls : LogState) : SnpKeep ls ls := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SnpOk.keep {g : NGhost} {ls ls' : LogState} (H : SnpOk g ls) (hk : SnpKeep ls ls')
    (hsn : ls'.snap = ls.snap) (hcm : uint.Z ls.committed ≤ uint.Z ls'.committed) : SnpOk g ls' :=
  H.of_fields hk.1 hsn hk.2.1 hk.2.2.1 hk.2.2.2.1 hcm (fun h k hk' hl => by
    obtain ⟨h1, -, -, -, h5, h6, h7⟩ := hk
    rw [h5, h6, h7, hsn]; rw [h1] at hl; exact h k hk' hl)

theorem logTruncateAppend_snpKeep (ls : LogState) (ents : List EntryM) :
    SnpKeep ls (logTruncateAppend ls ents) := by
  cases ents <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- (D22 S-d3b, 2026-10-21) **A truncation's mark**: `offsetInProgress` moved back to `i` by an append
of `ents` (`raftLog.maybeAppend`'s conflict arm, `unstable.truncateAndAppend`): above the commit
index, at an entry of the batch that the log did not have (`findConflict`'s index). What the
`RawNode` needs to know of an in-progress batch a `MsgApp` cut (`ackLostW`, `InvRawnode.lean`). -/
def TruncAt (ls : LogState) (ents : List EntryM) (i : w64) : Prop :=
  uint.Z ls.committed < uint.Z i ∧
  ∃ e ∈ ents, e.Index' = i ∧ ¬ PlogMatches ls.prev (ls.sents ++ ls.uents) (entId e)

/-- `logTruncInprogress` moves `offsetInProgress` back only to the batch's first index. -/
theorem logTruncInprogress_lt {ls : LogState} {f : w64}
    (h : uint.Z (logTruncInprogress ls f) < uint.Z ls.inprogress) :
    logTruncInprogress ls f = f := by
  unfold logTruncInprogress at *
  split at h
  · split at h
    · rw [if_pos ‹_›, if_pos ‹_›]
    · omega
  · omega

end snpok

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean).
proj_simps Perennial.EtcdGrove.unstableOf
