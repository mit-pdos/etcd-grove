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
- **no entry anywhere in the log is a configuration change**: `HnoConfChange` is
  `∀ e ∈ sents ++ uents, e.Type' = EntryNormal`. That is the conjunct
  `hasUnappliedConfChanges` needs (with `Happlied` / `Hcommitted` below placing
  `(applied, committed]` inside the log). It holds because **no configuration change is
  ever requested** -- a scope assumption, see below.
- `prev.index <= committed`, `applied <= committed <= prev.index + |sents| + |uents|`,
  and `prev.index <= applied` when no snapshot is pending: raft compacts only up to
  `applied` and commits only what it has. A received snapshot moves `prev` and
  `committed` to its index and leaves `applied` below it until the application applies
  it.
- **a pending snapshot** (`LogState.snap`, since 2026-10-02): when `unstable.snapshot`
  is set, the log starts at the snapshot's id with no stable part, and the `Storage` is
  shadowed (`LogStoreOk`).

### Scope assumptions written into the predicate

One, in the same class as `ownRaftPhys`'s `checkQuorum = false`: it is preserved by
everything on the election path, so a predicate may assert it, but it does restrict the
runs covered.

1. **No configuration change is ever requested.** Sanctioned scope. With it, no
   `EntryConfChange`/`EntryConfChangeV2` is ever appended, so `HnoConfChange` is
   preserved by `append` (the only log write on this path is the single empty
   `EntryNormal` a new leader appends).
(Until 2026-10-02 there was a second: no snapshot is ever received,
`unstable.snapshot = nil`. `LogState.snap` replaced it when `MsgSnap` came into
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

Lean notes: the Rocq `Ltac split_unstable l lv` is the tactic macro `split_unstable`
(same arguments; it acts on the hypothesis `Hl`, as the Ltac does). Rocq `Forall P l`
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
import EtcdGrove.Raft.InvStorage
import EtcdGrove.Raft.InvLogger

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

set_option hygiene false in
/-- Split `l.unstable` out of `l ↦ lv` and get a wand to put it back. The three
`unstable.maybe*` specs are stated on a bare `*unstable`, so every `raftLog` method
that consults the suffix needs this first. Exported rather than local because those
proofs now live in their own files. Acts on the hypothesis `Hl`, producing `Huf` (the
field) and `Hlback` (the wand back). -/
macro "split_unstable " l:term:max lv:term:max : tactic =>
  `(tactic| icases (Perennial.go_etcd_io.raft.v3.raftLog.raftLog_access_load_unstable $l $lv (DFrac.own 1)).access_strict $$ Hl
      with ⟨Huf, Hlback⟩)

/-! `LogState`, the log's abstract state, is defined in `Defs.lean`: the physical raft
state `NState` contains one. -/

/-- The log's entries are numbered consecutively from `prev.index + 1`. -/
def LogIndicesOk [FfiSyntax] (prev : entryID) (ents : List raftpb.Entry) : Prop :=
  ∀ (k : Nat) (e : raftpb.Entry), ents[k]? = some e →
    uint.Z e.Index' = uint.Z prev.index' + ((k + 1 : Nat) : Int)

def EntryNormal : w32 := W32 0

/-- Rocq `Forall_sublist_of`. -/
theorem forall_sublist_of {A : Type _} (P : A → Prop) (l es : List A) :
    (∀ e ∈ l, P e) → (∀ e, e ∈ es → e ∈ l) → ∀ e ∈ es, P e := by
  intro Hl Hin e He
  exact Hl e (Hin e He)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## The `unstable` struct

`ownUnstable u uv uents` owns the `unstable` at `u` -- in the development always the
`unstable` field of a `raftLog` -- at value `uv`, together with its entry slice,
holding `uents`.

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
def ownUnstable (u : Loc) (uv : unstable) (uents : List raftpb.Entry) : IProp GF :=
  iprop("Hu" ∷ u ↦ uv ∗
  "Hents_cap" ∷ ownSliceCap raftpb.Entry uv.entries' (DFrac.own 1) ∗
  "Hents" ∷ uv.entries' ↦*□ uents)

/-! ## The log -/

/-- A `Logger` interface value that is non-nil and satisfies `isLogger`. One persistent
assertion (rather than `∃ lg, ⌜x = ok lg⌝ ∗ isLogger lg` spread over the predicate) so
that `iframe` re-seals it as a unit: with two loggers' `isLogger`s in context it
otherwise picks the wrong one. -/
def isLoggerVal (x : GoInterface) : IProp GF :=
  iprop(∃ lg, ⌜x = interface.ok lg⌝ ∗ isLogger lg)

instance isLoggerVal_pers (x : GoInterface) : Persistent (isLoggerVal (GF := GF) x) := by
  unfold isLoggerVal; infer_instance

/-! Everything `ownRaftLog` owns besides the struct itself, at struct value `lv` and
entry list `prev`/`sents`/`uents`, is `ownRaftLogCore` below. Not a second predicate
for the log: nothing is specified on it. `ownRaftLog_unfold` is how a proof gets at
it. The unstable entries are held read-only, as in `ownUnstable` and for the same
reason.

**`sents` is the *visible* stable part** (since 2026-10-01). The `Storage` holds
`stored`, of which `sents` is a prefix: when `unstable.truncateAndAppend` takes its
`fromIndex <= u.offset` arm (a `MsgApp` that conflicts with an entry already handed to
storage), the new unstable suffix starts at `fromIndex` and *shadows* the tail of
`stored` from there on -- Go never deletes it from storage, it is just no longer read:
every read of the stable part (`term`, `slice`) is below `unstable.offset`.
`Hstored_eq` says the shadowing needs a non-empty suffix: with `uents = []`,
`lastIndex()` falls back to `storage.LastIndex()`, which is `prev.index + |stored|`,
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
      iprop(∃ (sv : raftpb.Snapshot), p ↦□ sv ∗
        ⌜sv.Metadata'.Index' = sid.index' ∧ sv.Metadata'.Term' = sid.term'⌝ ∗
        ∃ (voters : List w64), sv.Metadata'.ConfState'.Voters' ↦*□ voters)

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
    ∃ (sv : raftpb.Snapshot), p ↦□ sv ∗
      ⌜sv.Metadata'.Index' = sid.index' ∧ sv.Metadata'.Term' = sid.term'⌝ ∗
      ∃ (voters : List w64), sv.Metadata'.ConfState'.Voters' ↦*□ voters := by
  rw [ownSnap_unseal]; exact .rfl

instance ownSnap_pers (p : Loc) (snap : Option entryID) :
    Persistent (ownSnap (GF := GF) p snap) := by
  rw [ownSnap_unseal]; cases snap <;> unfold ownSnapDef <;> infer_instance

/-- How the visible log relates to what `Storage` holds, by whether a snapshot is
pending. The storage holds `stored` after `sprev` (`ownStorage`).

- No snapshot: `sprev` is the log's `prev`, and `sents` is a prefix of `stored` -- all
  of it when the unstable suffix is empty (see `ownRaftLogCore`).
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
def LogStoreOk (snap : Option entryID) (sprev : entryID) (stored : List raftpb.Entry)
    (prev : entryID) (sents uents : List raftpb.Entry) : Prop :=
  match snap with
  | none => sprev = prev ∧ sents <+: stored ∧ (uents = [] → sents = stored)
  | some sid => prev = sid ∧ sents = [] ∧
      (0 < uint.Z sid.index' ∧ uint.Z sid.index' < 2^61)

/-- The storage's own snapshot `ss` (`ownStorage`'s last index; `Storage.Snapshot`
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
def StoredSnapOk (ss : entryID) (cm : w64) (prev : entryID) (es : List raftpb.Entry) :
    Prop :=
  uint.Z ss.index' = 0 ∨
  (uint.Z ss.index' ≤ uint.Z cm ∧ plogTermAt prev es ss.index' = some ss.term')

omit [GoGlobalContext] in
theorem StoredSnapOk_commit (ss : entryID) (cm cm' : w64) (prev : entryID)
    (es : List raftpb.Entry) (Hle : uint.Z cm ≤ uint.Z cm') (H : StoredSnapOk ss cm prev es) :
    StoredSnapOk ss cm' prev es := by
  rcases H with H | ⟨H1, H2⟩
  · exact .inl H
  · exact .inr ⟨by omega, H2⟩

omit [GoGlobalContext] in
/-- An `append` keeps the log's terms below the batch. -/
theorem plogTermAt_truncateAppend_below (b : entryID) (es ents : List raftpb.Entry)
    (e0 : raftpb.Entry) (i t : w64) (H0 : ents[0]? = some e0)
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
    simp only [h1, h2, if_false] at Ht ⊢
    cases He : es[(uint.Z i - uint.Z b.index' - 1).toNat]? with
    | none => rw [He] at Ht; simp at Ht
    | some e =>
      have Hlen := (List.getElem?_eq_some_iff.1 He).1
      rw [He] at Ht
      rw [List.getElem?_append_left (by rw [List.length_take]; omega),
        List.getElem?_take_of_lt (by omega), He]
      exact Ht

/-! ## The storage handshake (2026-10-05)

`storApp sprev stored pend` is what a `Storage` holding `stored` after `sprev` holds
once the entries `pend` are appended to it the way `MemoryStorage.Append` does
(`storage.go`): everything at or above the batch's first index is replaced by the
batch. `Append` is not part of the `Storage` interface raft uses; it is how the
*application* persists `Ready.Entries`, and this is the state the application has to
leave the storage in (`ownRaftLog_persist`). -/
def storApp (sprev : entryID) (stored pend : List raftpb.Entry) : List raftpb.Entry :=
  match pend with
  | [] => stored
  | e0 :: _ =>
      stored.take (uint.Z e0.Index' - uint.Z sprev.index' - 1).toNat ++ pend

/-- The persistence invariant (`Hpersist` below), with no snapshot pending: the stable
part followed by the unstable entries already handed to the application
(`offsetInProgress - offset` of them) is a prefix of what the storage holds once the
unpersisted entries `pend` are appended -- everything raft has handed out is persisted,
or is exactly `pend` -- *exactly* when all of the unstable suffix has been handed out
(the application's truncating append leaves nothing behind it), and with no unstable
entries nothing is waiting to be persisted. `unstable.stableTo` (an `Advance`) moves
stable exactly entries this says are persisted, and the equality is what gives
`LogStoreOk`'s `sents = stored` when it empties the suffix. -/
def LogPersistOk (sprev : entryID) (stored : List raftpb.Entry)
    (sents uents : List raftpb.Entry) (ipo : Int) (pend : List raftpb.Entry) : Prop :=
  (sents ++ uents.take ipo.toNat) <+: storApp sprev stored pend ∧
  (ipo.toNat = uents.length → sents ++ uents = storApp sprev stored pend) ∧
  (uents = [] → pend = [])

def ownRaftLogCore (lv : raftLog) (snap : Option entryID) (prev : entryID)
    (sents uents : List raftpb.Entry) (pend : List raftpb.Entry) : IProp GF :=
  iprop(∃ (sprev : entryID) (stored : List raftpb.Entry) (ss : entryID),
  "%Hidx" ∷ ⌜LogIndicesOk prev (sents ++ uents)⌝ ∗
  "%Hnowrap" ∷ ⌜uint.Z prev.index' + (sents.length : Int)
                  + (uents.length : Int) + 1 < 2^64⌝ ∗
  "#HisStorage" ∷ isStorage lv.storage' ∗
  "HStorage" ∷ ownStorage lv.storage' sprev stored ss ∗
  "%Hstore" ∷ ⌜LogStoreOk snap sprev stored prev sents uents⌝ ∗
  "#Husnap" ∷ ownSnap lv.unstable'.snapshot' snap ∗
  "%Hoffset" ∷ ⌜uint.Z lv.unstable'.offset'
                 = uint.Z prev.index' + (sents.length : Int) + 1⌝ ∗
  "Huents" ∷ lv.unstable'.entries' ↦*□ uents ∗
  "Huents_cap" ∷ ownSliceCap raftpb.Entry lv.unstable'.entries' (DFrac.own 1) ∗
  "%HnoConfChange" ∷ ⌜∀ e ∈ sents ++ uents, e.Type' = EntryNormal⌝ ∗
  "%Happlied" ∷ ⌜uint.Z prev.index' ≤ uint.Z lv.committed' ∧
                  uint.Z lv.applied' ≤ uint.Z lv.committed'⌝ ∗
  "%Hpapplied" ∷ ⌜snap = none → uint.Z prev.index' ≤ uint.Z lv.applied'⌝ ∗
  "%Hcommitted" ∷ ⌜uint.Z lv.committed'
                    ≤ uint.Z prev.index' + (sents.length : Int) + (uents.length : Int)⌝ ∗
  "%Hssnap" ∷ ⌜snap = none → StoredSnapOk ss lv.committed' prev (sents ++ uents)⌝ ∗
  "#Hl_logger" ∷ isLoggerVal lv.logger' ∗
  "#Hu_logger" ∷ isLoggerVal lv.unstable'.logger' ∗
  -- what `Ready`/`Advance` need (2026-10-05): `offsetInProgress` lies between `offset`
  -- and the end of the log (`nextEntries` slices at it); the persistence invariant
  -- (`LogPersistOk`); `applying` between `applied` and `committed` (`nextCommittedEnts`
  -- slices from `applying+1`); and while applying is not paused there is room under
  -- `maxApplyingEntsSize` (`nextCommittedEnts`' `Panicf` on `maxSize <= 0`).
  "%Hipb" ∷ ⌜uint.Z lv.unstable'.offset' ≤ uint.Z lv.unstable'.offsetInProgress' ∧
             uint.Z lv.unstable'.offsetInProgress'
               ≤ uint.Z lv.unstable'.offset' + (uents.length : Int)⌝ ∗
  "%Hpersist" ∷ ⌜snap = none →
                  LogPersistOk sprev stored sents uents
                    (uint.Z lv.unstable'.offsetInProgress' - uint.Z lv.unstable'.offset')
                    pend⌝ ∗
  "%Happlying" ∷ ⌜uint.Z lv.applied' ≤ uint.Z lv.applying' ∧
                   uint.Z lv.applying' ≤ uint.Z lv.committed'⌝ ∗
  "%Hpaused" ∷ ⌜lv.applyingEntsPaused' = false →
                 uint.Z lv.applyingEntsSize' < uint.Z lv.maxApplyingEntsSize'⌝)

/-- The one predicate for a `raftLog`, indexed by its abstract state `ls` (`LogState`,
above). -/
def ownRaftLog (l : Loc) (ls : LogState) : IProp GF :=
  iprop(∃ (lv : raftLog),
  "Hl" ∷ l ↦ lv ∗
  "%Hcm" ∷ ⌜lv.committed' = ls.committed⌝ ∗
  "%Hap" ∷ ⌜lv.applied' = ls.applied⌝ ∗
  "%Hapg" ∷ ⌜lv.applying' = ls.applying⌝ ∗
  "%Hip" ∷ ⌜lv.unstable'.offsetInProgress' = ls.inprogress⌝ ∗
  "%Hasz" ∷ ⌜lv.applyingEntsSize' = ls.apsize⌝ ∗
  "%Hamx" ∷ ⌜lv.maxApplyingEntsSize' = ls.apmax⌝ ∗
  "Hcore" ∷ ownRaftLogCore lv ls.snap ls.prev ls.sents ls.uents ls.unpersisted)

/-- Open and close `ownRaftLog` with the entry list as variables -- the form every
`raftLog` proof works at after `cases ls`. -/
theorem ownRaftLog_unfold (l : Loc) (prev : entryID) (sents uents : List raftpb.Entry)
    (cm ap : w64) (snap : Option entryID) (ip apg : w64) (pend : List raftpb.Entry)
    (asz amx : w64) :
    ownRaftLog (GF := GF) l ⟨prev, sents, uents, cm, ap, snap, ip, apg, pend, asz, amx⟩ ⊣⊢
    ∃ lv, l ↦ lv ∗ ⌜lv.committed' = cm⌝ ∗
          ⌜lv.applied' = ap⌝ ∗
          ⌜lv.applying' = apg⌝ ∗
          ⌜lv.unstable'.offsetInProgress' = ip⌝ ∗
          ⌜lv.applyingEntsSize' = asz⌝ ∗
          ⌜lv.maxApplyingEntsSize' = amx⌝ ∗
          ownRaftLogCore lv snap prev sents uents pend := by
  unfold ownRaftLog; simp only [named]; exact .rfl

/-- Re-seal `ownRaftLog` from the pieces `iNamed Hlog; iNamed Hcore` names. **Use this
rather than `iframe`**: with the existential `stored` in `ownRaftLogCore`, Rocq's
`iFrame` spends ~35 s searching (measured in `proof_raftLog__lastIndex.v`, 2026-10-01).
`st` is the storage as the hypotheses mention it -- `lv.storage'`, or
`interface.ok isv` after a rewrite with `Hstok` -- and the premise `lv.storage' = st` is
then `rfl` or `Hstok`. The `reseal_raftLog` tactic below applies it with the standard
names and closes the pure premises by assumption. -/
theorem ownRaftLog_intro (l : Loc) (lv : raftLog) (st : Storage) (snap : Option entryID)
    (prev : entryID) (sents uents : List raftpb.Entry) (cm ap : w64) (sprev : entryID)
    (stored : List raftpb.Entry) (ss : entryID) (ip apg : w64) (pend : List raftpb.Entry)
    (asz amx : w64) :
    lv.storage' = st →
    lv.committed' = cm →
    lv.applied' = ap →
    LogIndicesOk prev (sents ++ uents) →
    uint.Z prev.index' + (sents.length : Int) + (uents.length : Int) + 1 < 2^64 →
    LogStoreOk snap sprev stored prev sents uents →
    uint.Z lv.unstable'.offset' = uint.Z prev.index' + (sents.length : Int) + 1 →
    (∀ e ∈ sents ++ uents, e.Type' = EntryNormal) →
    uint.Z prev.index' ≤ uint.Z lv.committed' ∧ uint.Z lv.applied' ≤ uint.Z lv.committed' →
    (snap = none → uint.Z prev.index' ≤ uint.Z lv.applied') →
    uint.Z lv.committed' ≤ uint.Z prev.index' + (sents.length : Int) + (uents.length : Int) →
    (snap = none → StoredSnapOk ss lv.committed' prev (sents ++ uents)) →
    lv.applying' = apg →
    lv.unstable'.offsetInProgress' = ip →
    uint.Z lv.unstable'.offset' ≤ uint.Z lv.unstable'.offsetInProgress' ∧
      uint.Z lv.unstable'.offsetInProgress' ≤ uint.Z lv.unstable'.offset' + (uents.length : Int) →
    (snap = none →
      LogPersistOk sprev stored sents uents
        (uint.Z lv.unstable'.offsetInProgress' - uint.Z lv.unstable'.offset') pend) →
    uint.Z lv.applied' ≤ uint.Z lv.applying' ∧ uint.Z lv.applying' ≤ uint.Z lv.committed' →
    (lv.applyingEntsPaused' = false →
      uint.Z lv.applyingEntsSize' < uint.Z lv.maxApplyingEntsSize') →
    lv.applyingEntsSize' = asz →
    lv.maxApplyingEntsSize' = amx →
    ⊢ l ↦ lv -∗
      isStorage (GF := GF) st -∗
      ownStorage st sprev stored ss -∗
      ownSnap lv.unstable'.snapshot' snap -∗
      lv.unstable'.entries' ↦*□ uents -∗
      ownSliceCap raftpb.Entry lv.unstable'.entries' (DFrac.own 1) -∗
      isLoggerVal lv.logger' -∗
      isLoggerVal lv.unstable'.logger' -∗
      ownRaftLog l ⟨prev, sents, uents, cm, ap, snap, ip, apg, pend, asz, amx⟩ := by
  intro Hst Hcm Hap Hidx Hnowrap Hstore Hoffset HnoConfChange Happlied Hpapplied
    Hcommitted Hssnap Hapg Hip Hipb Hpersist Happlying Hpaused Hasz Hamx
  subst Hst
  iintro Hl #HisStorage HStorage #Husnap #Huents Huents_cap #Hl_logger #Hu_logger
  unfold ownRaftLog ownRaftLogCore
  iexists lv
  simp only [named]
  iframe Hl
  isplitr; · ipureintro; exact Hcm
  isplitr; · ipureintro; exact Hap
  isplitr; · ipureintro; exact Hapg
  isplitr; · ipureintro; exact Hip
  isplitr; · ipureintro; exact Hasz
  isplitr; · ipureintro; exact Hamx
  iexists sprev, stored, ss
  iframe HisStorage HStorage Husnap Huents Huents_cap Hl_logger Hu_logger
  ipureintro
  exact ⟨Hidx, Hnowrap, Hstore, Hoffset, HnoConfChange, Happlied, Hpapplied, Hcommitted,
    Hssnap, Hipb, Hpersist, Happlying, Hpaused⟩

/-- The struct, for a field read. `committed` and `applied` are what the state says
they are. -/
theorem ownRaftLog_struct (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ∃ lv : raftLog, l ↦ lv ∗
            ⌜lv.committed' = ls.committed ∧ lv.applied' = ls.applied⌝ ∗
            (l ↦ lv -∗ ownRaftLog l ls) := by
  iintro H
  unfold ownRaftLog
  icases H with ⟨%lv, H⟩
  iNamed H
  iexists lv
  iframe Hl
  isplitr
  · ipureintro; exact ⟨Hcm, Hap⟩
  · iintro Hl
    iexists lv
    iframe Hl Hcore
    ipureintro; exact ⟨Hcm, Hap, Hapg, Hip, Hasz, Hamx⟩

/-- The `Ready`-side facts, read out without consuming the log: `inprogress` between
`offset` and the end of the log, and `applying` between `applied` and `committed`. -/
theorem ownRaftLog_ready_wf (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜(uint.Z ls.prev.index' + (ls.sents.length : Int) + 1 ≤ uint.Z ls.inprogress ∧
        uint.Z ls.inprogress ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
          + (ls.uents.length : Int) + 1) ∧
       (uint.Z ls.applied ≤ uint.Z ls.applying ∧ uint.Z ls.applying ≤ uint.Z ls.committed)⌝ ∗
      ownRaftLog l ls := by
  iintro H0
  unfold ownRaftLog
  icases H0 with ⟨%lv, H0⟩
  iNamed H0
  unfold ownRaftLogCore
  icases Hcore with ⟨%sprev, %stored, %ss, Hcore⟩
  iNamed Hcore
  isplitr
  · ipureintro
    rw [← Hip, ← Hapg, ← Hcm, ← Hap]
    omega
  · iexists lv
    simp only [named]
    iframe Hl
    isplitr; · ipureintro; exact Hcm
    isplitr; · ipureintro; exact Hap
    isplitr; · ipureintro; exact Hapg
    isplitr; · ipureintro; exact Hip
    isplitr; · ipureintro; exact Hasz
    isplitr; · ipureintro; exact Hamx
    iexists sprev, stored, ss
    iframe HisStorage HStorage Husnap Huents Huents_cap Hl_logger Hu_logger
    ipureintro
    exact ⟨Hidx, Hnowrap, Hstore, Hoffset, HnoConfChange, Happlied, Hpapplied, Hcommitted,
      Hssnap, Hipb, Hpersist, Happlying, Hpaused⟩

/-- The storage handshake's application side (2026-10-05): the `Storage` the log owns,
opened so that the application can append the unpersisted entries to it, and closed at
the state that leaves -- `storApp` of the entries `Ready` handed out, which is what
`MemoryStorage.Append(rd.Entries)` does. The log then records nothing unpersisted.

This is an accessor, not a loan: nothing else may be called on the log while it is
open. A loan -- the storage out of `ownRaftLog` across calls, recorded in `LogState` --
was the first design and does not work: `Step` between `Ready` and `Advance` is legal
in Go, and `Step` reads the storage on most of its paths (`term` of a stable index for
`matchTerm`/`findConflict`, `lastIndex` with an empty unstable part, `firstIndex` in
every `term`/`slice`, `slice` and `snapshot` for a leader's `maybeSendAppend`), so
`Step` could not keep its spec with the storage lent out. -/
theorem ownRaftLog_persist (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ∃ (st : Storage) (sprev : entryID) (stored : List raftpb.Entry) (ss : entryID),
        isStorage st ∗ ownStorage st sprev stored ss ∗
        (ownStorage st sprev (storApp sprev stored ls.unpersisted) ss -∗
         ownRaftLog l { ls with unpersisted := [] }) := by
  obtain ⟨prev, sents, uents, cm, ap, snap, ip, apg, pend, asz, amx⟩ := ls
  iintro H
  icases (ownRaftLog_unfold (GF := GF) l prev sents uents cm ap snap ip apg pend asz amx).1 $$ H
    with ⟨%lv, Hl, %Hcm, %Hap, %Hapg, %Hip, %Hasz, %Hamx, Hcore⟩
  unfold ownRaftLogCore
  icases Hcore with ⟨%sprev, %stored, %ss, Hcore⟩
  iNamed Hcore
  iexists lv.storage', sprev, stored, ss
  iframe HisStorage HStorage
  iintro HStorage
  have Hstore' : LogStoreOk snap sprev (storApp sprev stored pend) prev sents uents := by
    cases snap with
    | some sid => exact Hstore
    | none =>
      obtain ⟨Hpre, _, Hpe⟩ := Hpersist rfl
      obtain ⟨Hsp, _, Hsu⟩ := Hstore
      refine ⟨Hsp, (List.prefix_append sents _).trans Hpre, ?_⟩
      intro Hu
      rw [Hpe Hu]
      exact Hsu Hu
  have Hpersist' : snap = none →
      LogPersistOk sprev (storApp sprev stored pend) sents uents
        (uint.Z lv.unstable'.offsetInProgress' - uint.Z lv.unstable'.offset') [] := by
    intro Hs
    obtain ⟨Hpre, Heq, _⟩ := Hpersist Hs
    exact ⟨Hpre, Heq, fun _ => rfl⟩
  iapply ownRaftLog_intro l lv lv.storage' snap prev sents uents cm ap sprev
    (storApp sprev stored pend) ss ip apg [] asz amx rfl Hcm Hap Hidx Hnowrap Hstore'
    Hoffset HnoConfChange Happlied Hpapplied Hcommitted Hssnap Hapg Hip Hipb Hpersist'
    Happlying Hpaused Hasz Hamx $$ Hl HisStorage HStorage Husnap Huents Huents_cap
    Hl_logger Hu_logger

/-- Read a pure fact of `ownRaftLogCore` out of `ownRaftLog`, without consuming it. The
common shape of the `ownRaftLog_*` lemmas below (Rocq proves each by `iNamed`; `iFrame
"∗#%"`). -/
theorem ownRaftLog_pure (l : Loc) (ls : LogState) (φ : Prop)
    (H : ∀ (lv : raftLog) (sprev : entryID) (stored : List raftpb.Entry) (ss : entryID),
      lv.committed' = ls.committed → lv.applied' = ls.applied →
      LogIndicesOk ls.prev (ls.sents ++ ls.uents) →
      uint.Z ls.prev.index' + (ls.sents.length : Int) + (ls.uents.length : Int) + 1 < 2^64 →
      LogStoreOk ls.snap sprev stored ls.prev ls.sents ls.uents →
      (∀ e ∈ ls.sents ++ ls.uents, e.Type' = EntryNormal) →
      uint.Z ls.prev.index' ≤ uint.Z lv.committed' ∧ uint.Z lv.applied' ≤ uint.Z lv.committed' →
      (ls.snap = none → uint.Z ls.prev.index' ≤ uint.Z lv.applied') →
      uint.Z lv.committed' ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
        + (ls.uents.length : Int) →
      φ) :
    ⊢ ownRaftLog (GF := GF) l ls -∗ ⌜φ⌝ ∗ ownRaftLog l ls := by
  iintro H0
  unfold ownRaftLog
  icases H0 with ⟨%lv, H0⟩
  iNamed H0
  unfold ownRaftLogCore
  icases Hcore with ⟨%sprev, %stored, %ss, Hcore⟩
  iNamed Hcore
  isplitr
  · ipureintro
    exact H lv sprev stored ss Hcm Hap Hidx Hnowrap Hstore HnoConfChange Happlied Hpapplied
      Hcommitted
  · iexists lv
    simp only [named]
    iframe Hl
    isplitr; · ipureintro; exact Hcm
    isplitr; · ipureintro; exact Hap
    isplitr; · ipureintro; exact Hapg
    isplitr; · ipureintro; exact Hip
    isplitr; · ipureintro; exact Hasz
    isplitr; · ipureintro; exact Hamx
    iexists sprev, stored, ss
    iframe HisStorage HStorage Husnap Huents Huents_cap Hl_logger Hu_logger
    ipureintro
    exact ⟨Hidx, Hnowrap, Hstore, Hoffset, HnoConfChange, Happlied, Hpapplied, Hcommitted,
      Hssnap, Hipb, Hpersist, Happlying, Hpaused⟩

/-- `Hnowrap`, read out without consuming the log. Needed to know `lastIndex() + 1`
does not wrap, which is what makes the range premises of `raftLog.slice` and
`raftLog.mustCheckOutOfBounds` hold. -/
theorem ownRaftLog_nowrap (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜uint.Z ls.prev.index' + (ls.sents.length : Int)
         + (ls.uents.length : Int) + 1 < 2^64⌝ ∗
      ownRaftLog l ls :=
  ownRaftLog_pure l ls _ fun _ _ _ _ _ _ _ Hnowrap _ _ _ _ _ => Hnowrap

/-- `Hidx` and the commit bounds, read out without consuming the log. -/
theorem ownRaftLog_wf (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜LogIndicesOk ls.prev (ls.sents ++ ls.uents)⌝ ∗
      ownRaftLog l ls :=
  ownRaftLog_pure l ls _ fun _ _ _ _ _ _ Hidx _ _ _ _ _ _ => Hidx

theorem ownRaftLog_committed (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜(uint.Z ls.prev.index' ≤ uint.Z ls.committed ∧
        uint.Z ls.applied ≤ uint.Z ls.committed ∧
        uint.Z ls.committed ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
          + (ls.uents.length : Int)) ∧
       (ls.snap = none → uint.Z ls.prev.index' ≤ uint.Z ls.applied)⌝ ∗
      ownRaftLog l ls :=
  ownRaftLog_pure l ls _ fun lv _ _ _ Hcm Hap _ _ _ _ Happlied Hpapplied Hcommitted => by
    rw [← Hcm, ← Hap]
    exact ⟨⟨Happlied.1, Happlied.2, Hcommitted⟩, Hpapplied⟩

/-- The pending snapshot's facts (`LogStoreOk`), read out without consuming the log:
with a snapshot pending, the log starts at it with no stable part. `appendEntry` and
`raftLog.restore`'s callers need the index bound. -/
theorem ownRaftLog_snap (l : Loc) (ls : LogState) (sid : entryID) (Hs : ls.snap = some sid) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜ls.prev = sid ∧ ls.sents = [] ∧
        (0 < uint.Z sid.index' ∧ uint.Z sid.index' < 2^61)⌝ ∗
      ownRaftLog l ls :=
  ownRaftLog_pure l ls _ fun _ _ _ _ _ _ _ _ Hstore _ _ _ _ => by
    rw [Hs] at Hstore; exact Hstore

theorem ownRaftLog_no_confchange (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜∀ e ∈ ls.sents ++ ls.uents, e.Type' = EntryNormal⌝ ∗
      ownRaftLog l ls :=
  ownRaftLog_pure l ls _ fun _ _ _ _ _ _ _ _ _ HnoConfChange _ _ _ => HnoConfChange

omit [GoGlobalContext] in
/-- An entry `Storage.Entries` hands back for a range ending at or below
`unstable.offset` is an entry of the *visible* stable part `sents` (`isStorage`'s
`HEntries` bounds it by `hi`; `Hstored` makes the prefix below `hi` a prefix of
`sents`). -/
theorem stored_take_visible (prev : entryID) (sents stored : List raftpb.Entry) (hi : w64)
    (e : raftpb.Entry) (Hpre : sents <+: stored)
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
the storage keeps the shadowed tail (`ownRaftLogCore`'s `stored`). Otherwise `sents`
is unchanged and the unstable suffix is cut at `ents[0].Index` and extended.
`Spec/raftLog__append.lean` relates it to `plogTruncateAppend`. -/
def logTruncateAppend (ls : LogState) (ents : List raftpb.Entry) : LogState :=
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
def logAdopts (ls : LogState) (ents : List raftpb.Entry) : Bool :=
  match ents with
  | [] => false
  | e0 :: _ =>
      decide (uint.Z e0.Index' ≤ uint.Z ls.prev.index' + (ls.sents.length : Int) + 1 ∧
              uint.Z e0.Index' ≠ uint.Z ls.prev.index' + (ls.sents.length : Int)
                + (ls.uents.length : Int) + 1)

omit [GoGlobalContext] in
/-- A batch that continues the log is a plain `logAppend`. -/
theorem logTruncateAppend_cont (ls : LogState) (ents : List raftpb.Entry)
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

/-- Read a slice's length as an `Int`, without consuming the slice. -/
theorem slice_len_Z (s : GoSlice) (vs : List raftpb.Entry) (dq : DFrac) :
    ⊢ s ↦*{dq} vs -∗ (⌜(vs.length : Int) = sint.Z s.len⌝ : IProp GF) := by
  iintro H
  icases ownSlice_len s dq vs $$ H with ⟨%H1, %H2⟩
  ipureintro
  rw [H1]; word

/-! ## Reading the log through `scan`

`raftLog.scan lo hi pageSize v` pages through `[lo, hi)` and hands each page to the
callback `v` as a slice of the log's entries, read-only (a sub-slice of
`unstable.entries`, or one the `Storage` handed out, or a fresh concatenation).
`scanClosure f I P` is what `raftLog.wp_scan` asks of the callback: given any such page
whose entries all satisfy `P`, with the caller's invariant `I`, it returns a `nil`
error and hands `I` back. Same shape as `visitClosure` (`InvTracker.lean`).

`P` is how the caller gets a fact about the log's entries into the callback: `scan`'s
spec takes `∀ e ∈ sents ++ uents, P e` as a premise and every page is a sub-list of the
log. `hasUnappliedConfChanges` uses `P := fun e => e.Type' = EntryNormal`, from
`HnoConfChange`.

The callback's own `return err` paths -- `errBreak` in `hasUnappliedConfChanges` -- are
not modelled: the closure has to return `nil`, which is exactly what makes `scan` return
`nil`. -/
def scanClosure (f : GoFunc) (I : IProp GF) (P : raftpb.Entry → Prop) : IProp GF :=
  iprop(∀ (s : GoSlice) (es : List raftpb.Entry) (dq : DFrac),
    {{ s ↦*{dq} es ∗ ⌜∀ e ∈ es, P e⌝ ∗ I }}
      (App (Val #f) (Val #s))
    {{ RET #interface.nil; s ↦*{dq} es ∗ I }})

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
value for it. `split_unstable` (above) is not enough for a call that installs a new
`unstable` value -- `truncateAndAppend`'s new `entries`, `unstable.restore` -- since the
new value is introduced by that call's own postcondition, after the `AccessStrict`
store instance's evar was created (notes/gotchas.md, "The `AccessStrict` store instance
cannot take a value the call has not produced yet"). Moved here from
`proof_raftLog__append.v` on 2026-10-02 for `raftLog.restore`. -/
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


end proof

set_option hygiene false in
/-- Re-seal `ownRaftLog l ⟨…⟩` from the hypotheses `iNamed Hlog; iNamed Hcore`
introduced (`ownRaftLog_intro`). The pure premises are closed by reducible `rfl` or
`assumption` (Rocq `try done`; a plain `assumption` runs out of recursion depth on the
`2^64` bounds). -/
macro "reseal_raftLog" : tactic =>
  `(tactic| (iapply Perennial.EtcdGrove.ownRaftLog_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ $$ Hl HisStorage HStorage Husnap Huents Huents_cap Hl_logger Hu_logger) <;>
    try (first | with_reducible rfl | with_reducible assumption))

end EtcdGrove
end Perennial
