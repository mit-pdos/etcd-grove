/-
Port of `election_proof/inv_raftlog.v`: the raft log.

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
- `prev.index <= applied <= committed <= prev.index + |sents| + |uents|`: raft compacts
  only up to `applied` and commits only what it has.
- **`unstable.snapshot = nil`**: no snapshot is ever received or taken -- a scope
  assumption, see below. This is what makes `hasNextOrInProgressSnapshot` return
  `false`, which `promotable` needs.

### Scope assumptions written into the predicate

Two, both in the same class as `ownRaftPhys`'s `preVote = false`: they are preserved by
everything on the election path, so a predicate may assert them, but they do restrict
the runs covered.

1. **No configuration change is ever requested.** Sanctioned scope. With it, no
   `EntryConfChange`/`EntryConfChangeV2` is ever appended, so `HnoConfChange` is
   preserved by `append` (the only log write on this path is the single empty
   `EntryNormal` a new leader appends).
2. **No snapshot is ever received or applied.** `newLog` starts with
   `unstable.snapshot = nil`; only `unstable.restore` (i.e. handling a `MsgSnap`, or
   `raft.restore`) sets it, and that is not an election message. Recorded here because
   it was *not* in the sanctioned list and is needed for `hasNextOrInProgressSnapshot`.

Note what is **not** assumed: that `term(lastIndex())` succeeds. That is the fact
`lastEntryID` needs, and it is *proved* here from the conjuncts above plus the
`Storage` contract. Assuming it directly would be the `raft.wp_appendEntry` mistake
again -- an assumption about raft's own code in a place where it can be derived.

### Structure

`ownRaftLog l ls` is the one predicate, indexed by `ls : LogState` (below): the entry
list, `committed` and `applied`. The entry list is in the index rather than existential
inside because `raftLog.term` calls `firstIndex` and `lastIndex` on itself, so the proof
has to re-seal and re-open the predicate mid-function and needs the split to come back
unchanged. `ownUnstable` is the predicate for the embedded `unstable` struct.

The `Storage` interface contract lives in `InvStorage.lean`.

Lean notes: the Rocq `Ltac split_unstable l lv` is the tactic macro `split_unstable`
(same arguments; it acts on the hypothesis `Hl`, as the Ltac does). Rocq `Forall P l`
is `∀ e ∈ l, P e`, so `Forall_sublist_of` is `forall_sublist_of`; `own_slice_same_ptr_len`
is `ownSlice_same_ptr_len`. A Rocq lemma `P -∗ Q -∗ R` is `⊢ P -∗ Q -∗ R`.
-/
import EtcdGrove.Raft.ElectionProof.InvStorage

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
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

/-- Everything `ownRaftLog` owns besides the struct itself, at struct value `lv` and
entry list `prev`/`sents`/`uents`. Not a second predicate for the log: nothing is
specified on it. `ownRaftLog_unfold` is how a proof gets at it. The unstable entries
are held read-only, as in `ownUnstable` and for the same reason. -/
def ownRaftLogCore (lv : raftLog) (prev : entryID)
    (sents uents : List raftpb.Entry) : IProp GF :=
  iprop("%Hidx" ∷ ⌜LogIndicesOk prev (sents ++ uents)⌝ ∗
  "%Hnowrap" ∷ ⌜uint.Z prev.index' + (sents.length : Int)
                  + (uents.length : Int) + 1 < 2^64⌝ ∗
  "#HisStorage" ∷ isStorage lv.storage' ∗
  "HStorage" ∷ ownStorage lv.storage' prev sents ∗
  "%Hoffset" ∷ ⌜uint.Z lv.unstable'.offset'
                 = uint.Z prev.index' + (sents.length : Int) + 1⌝ ∗
  "Huents" ∷ lv.unstable'.entries' ↦*□ uents ∗
  "Huents_cap" ∷ ownSliceCap raftpb.Entry lv.unstable'.entries' (DFrac.own 1) ∗
  "%Hnosnap" ∷ ⌜lv.unstable'.snapshot' = null⌝ ∗
  "%HnoConfChange" ∷ ⌜∀ e ∈ sents ++ uents, e.Type' = EntryNormal⌝ ∗
  "%Happlied" ∷ ⌜uint.Z prev.index' ≤ uint.Z lv.applied' ∧
                  uint.Z lv.applied' ≤ uint.Z lv.committed'⌝ ∗
  "%Hcommitted" ∷ ⌜uint.Z lv.committed'
                    ≤ uint.Z prev.index' + (sents.length : Int) + (uents.length : Int)⌝)

/-- The one predicate for a `raftLog`, indexed by its abstract state `ls` (`LogState`,
above). -/
def ownRaftLog (l : Loc) (ls : LogState) : IProp GF :=
  iprop(∃ (lv : raftLog),
  "Hl" ∷ l ↦ lv ∗
  "%Hcm" ∷ ⌜lv.committed' = ls.committed⌝ ∗
  "%Hap" ∷ ⌜lv.applied' = ls.applied⌝ ∗
  "Hcore" ∷ ownRaftLogCore lv ls.prev ls.sents ls.uents)

/-- Open and close `ownRaftLog` with the entry list as variables -- the form every
`raftLog` proof works at after `cases ls`. -/
theorem ownRaftLog_unfold (l : Loc) (prev : entryID) (sents uents : List raftpb.Entry)
    (cm ap : w64) :
    ownRaftLog (GF := GF) l ⟨prev, sents, uents, cm, ap⟩ ⊣⊢
    ∃ lv, l ↦ lv ∗ ⌜lv.committed' = cm⌝ ∗
          ⌜lv.applied' = ap⌝ ∗ ownRaftLogCore lv prev sents uents := by
  unfold ownRaftLog; simp only [named]; exact .rfl

/-- Re-sealing a log a proof has taken apart, as one `iapply` with named hypotheses and
pure side goals:

    iapply ownRaftLog_intro … $$ Hl HisStorage HStorage Huents Huents_cap

Unfolding and closing it with `iframe` instead cost 20-70s per use in Rocq (2026-09-30
measurement; main's notes/gotchas.md) -- the same reason `ownRaftPhys_intro` exists.
The pure premises are in the order the conjuncts appear in `ownRaftLogCore`. `l ↦ lv`
comes first so that it fixes `lv`. The storage is a separate `st` because a proof that
has rewritten with `Hstok` holds `HisStorage` and `HStorage` at `interface.ok _` rather
than at `lv.storage'`; the first premise is then `Hstok`. -/
theorem ownRaftLog_intro (l : Loc) (prev : entryID) (sents uents : List raftpb.Entry)
    (cm ap : w64) (lv : raftLog) (st : Storage) :
    lv.storage' = st →
    lv.committed' = cm →
    lv.applied' = ap →
    LogIndicesOk prev (sents ++ uents) →
    uint.Z prev.index' + (sents.length : Int) + (uents.length : Int) + 1 < 2^64 →
    uint.Z lv.unstable'.offset' = uint.Z prev.index' + (sents.length : Int) + 1 →
    lv.unstable'.snapshot' = null →
    (∀ e ∈ sents ++ uents, e.Type' = EntryNormal) →
    uint.Z prev.index' ≤ uint.Z lv.applied' ∧ uint.Z lv.applied' ≤ uint.Z lv.committed' →
    uint.Z lv.committed' ≤ uint.Z prev.index' + (sents.length : Int) + (uents.length : Int) →
    ⊢ l ↦ lv -∗
      isStorage (GF := GF) st -∗
      ownStorage st prev sents -∗
      lv.unstable'.entries' ↦*□ uents -∗
      ownSliceCap raftpb.Entry lv.unstable'.entries' (DFrac.own 1) -∗
      ownRaftLog l ⟨prev, sents, uents, cm, ap⟩ := by
  intro Hst Hcm Hap Hidx Hnowrap Hoffset Hnosnap HnoConfChange Happlied Hcommitted
  subst Hst
  iintro Hl #HisStorage HStorage #Huents Huents_cap
  unfold ownRaftLog ownRaftLogCore
  iexists lv
  simp only [named]
  iframe Hl HisStorage HStorage Huents Huents_cap
  ipureintro
  exact ⟨Hcm, Hap, Hidx, Hnowrap, Hoffset, Hnosnap, HnoConfChange, Happlied, Hcommitted⟩

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
    ipureintro; exact ⟨Hcm, Hap⟩

/-- `Hnowrap`, read out without consuming the log. Needed to know `lastIndex() + 1`
does not wrap, which is what makes the range premises of `raftLog.slice` and
`raftLog.mustCheckOutOfBounds` hold. -/
theorem ownRaftLog_nowrap (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜uint.Z ls.prev.index' + (ls.sents.length : Int)
         + (ls.uents.length : Int) + 1 < 2^64⌝ ∗
      ownRaftLog l ls := by
  iintro H
  unfold ownRaftLog
  icases H with ⟨%lv, H⟩
  iNamed H
  unfold ownRaftLogCore
  iNamed Hcore
  isplitr
  · ipureintro; exact Hnowrap
  · iexists lv
    simp only [named]
    iframe Hl HisStorage HStorage Huents Huents_cap
    ipureintro
    exact ⟨Hcm, Hap, Hidx, Hnowrap, Hoffset, Hnosnap, HnoConfChange, Happlied, Hcommitted⟩

theorem ownRaftLog_no_confchange (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜∀ e ∈ ls.sents ++ ls.uents, e.Type' = EntryNormal⌝ ∗
      ownRaftLog l ls := by
  iintro H
  unfold ownRaftLog
  icases H with ⟨%lv, H⟩
  iNamed H
  unfold ownRaftLogCore
  iNamed Hcore
  isplitr
  · ipureintro; exact HnoConfChange
  · iexists lv
    simp only [named]
    iframe Hl HisStorage HStorage Huents Huents_cap
    ipureintro
    exact ⟨Hcm, Hap, Hidx, Hnowrap, Hoffset, Hnosnap, HnoConfChange, Happlied, Hcommitted⟩

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

end proof

end EtcdGrove
end Perennial
