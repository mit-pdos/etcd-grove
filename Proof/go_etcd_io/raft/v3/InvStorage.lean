/-
Port of `election_proof/inv_storage.v` (at feb5c73d4): the `Storage` interface.

`raftLog.storage` is a `Storage` **interface value**, supplied by the application (etcd
provides one; raft itself only ships `MemoryStorage` for tests). It is therefore a
legitimate abstraction boundary: there is no raft code to verify behind it, only a
contract that raft relies on. So this file states that contract.

The shape follows `ownAckedIndexer` (`v3_proof/readonly.lean`): a definition bundling
one Hoare triple per method, against an abstract resource describing the stored log.

**This file assumes nothing**: the abstract predicate `ownStorage`, below, is a
parameter (a field of the class `StorageModel`, which the results quantify over), and
everything else is a definition built from it, so the triples are not axioms -- they
are what a client has to supply, and a caller that has no `isStorage` gets nothing.

### The abstraction

`ownStorage st prev ents ss` says: the storage behind the interface value `st` holds
the log entries `ents`, immediately following the entry `prev`, and its most recent
snapshot has metadata `ss` (as an `entryID`: `(Metadata.Term, Metadata.Index)`).
`prev` is the compaction boundary -- the last entry the storage has discarded the
payload of but still knows the term of. This is exactly how `MemoryStorage` represents
its log (a dummy entry at `ents[0]`), and it is what makes `Term` total on
`[prev.index, prev.index + |ents|]` rather than only on `(prev.index, ...]`. `ss` is
`MemoryStorage.snapshot`'s metadata, which `Snapshot()` returns (added 2026-10-03, so
that `raft` can relate the snapshot it forwards to its own commit index -- see
`HSnapshot` and `ownRaftLog`'s `StoredSnapOk`).

Index `prev.index + 1 + k` holds `ents[k]?`, so:
  - `FirstIndex()` = `prev.index + 1`
  - `LastIndex()`  = `prev.index + |ents|`
  - `Term(i)`      = `termAt prev ents i`, defined for
                     `prev.index <= i <= prev.index + |ents|`.

### Which methods are here, and why the others are not

`Storage` has six methods. Four are specified: `FirstIndex`, `LastIndex`, `Term` and
(since 2026-09-19) `Entries`. The first three are what raft's own log code calls on the
leader-election path (`raftLog.firstIndex`, `raftLog.lastIndex`, `raftLog.term`), and
each of them **panics** on an error return, so a proof has to know they succeed.

`Entries` is reached by `raftLog.slice`, which `raftLog.scan` and hence
`raft.hasUnappliedConfChanges` call on the `hup` path whenever the unapplied range
starts in the stable prefix. Its contract:
  - the range premise `firstIndex <= lo < hi <= lastIndex + 1` is exactly what makes
    `MemoryStorage.Entries`'s `ErrCompacted` and `ErrUnavailable` returns unreachable,
    so the error is `nil`;
  - the result is a **non-empty** sub-list of the stored entries of length at most
    `hi - lo` -- `MemoryStorage` applies `limitSize`, which keeps at least one entry;
  - **`cap = len`**: `MemoryStorage.Entries` returns `ents[:len(ents):len(ents)]`
    precisely so that a caller's `append` reallocates instead of writing into
    `ms.ents`. `raftLog.slice` relies on this through `extend`, whose in-place branch
    would otherwise write into storage memory this contract does not grant;
  - the entries are handed out **read-only and for good** (`s ↦*□ es`, no wand back).
    This is the interface's own contract (`storage.go:56-67`, upamanyus/etcd-raft
    531b20c): "The caller of Entries owns the returned slice, and may append to it.
    The individual entries in the slice must not be mutated, neither by the Storage
    implementation nor the caller." `MemoryStorage` keeps it: `Entries` caps the
    result (`storage.go:155`), `Append` rebuilds with `append(ms.ents[:offset:offset],
    ...)` "as they may still be referenced from outside MemoryStorage"
    (`storage.go:303-305`), and `Compact` allocates. The slack is not handed out:
    `cap = len`. (Until 2026-09-29 the slice was *lent*, at an existential fraction,
    with a wand back to `ownStorage`; that forced a page loan on `raftLog.slice`'s
    callers -- `logstate.page`.)
What the returned entries *are* is stated only as membership: every one is a stored
entry **below `hi`** (`ents.take (hi - prev.index - 1)`). The bound was added
2026-10-01, when `ownRaftLog`'s stable part became a *visible prefix* of the stored
entries (`InvRaftlog.lean`): `raftLog.slice` reads only below `unstable.offset`, and
without the bound it could not tell an entry it got back from a shadowed one.
`MemoryStorage.Entries` returns `ms.ents[lo-offset : hi-offset]` cut by `limitSize`,
so it holds.

Besides the four triples the contract has one **pure clause**, `Hbounded`: the stable
log's last index is below `2^61`. It is the assumption that makes appending to the log
possible -- the log's no-wrap invariant is not inductive, and the part of the log an
`append` does not move is exactly the part behind this interface. The long version is
at the clause itself.

`Snapshot` was added on 2026-09-20, by exactly that rule: `raft.maybeSendSnapshot`
calls it, and `maybeSendSnapshot` is reachable from `bcastAppend` because nothing in
`ownProgress` bounds a peer's `Next` against the log, so `raftLog.term(pr.Next-1)` may
legitimately return `ErrCompacted`. Its contract is a disjunction -- the distinguished
`ErrSnapshotTemporarilyUnavailable`, or a non-empty snapshot -- because every other
outcome reaches a `panic`.

`InitialState` is deliberately **omitted**. Nothing on the election path calls it, and
an assumption that is not needed is an assumption not worth making: it would be a fresh
claim about client code. Add it when a proof needs it, with the same "state it, then
use it" discipline.

### The pending append (2026-10-10)

The application appends the entries a `Ready` handed out (`MemoryStorage.Append`) on its
own goroutine, while raft -- `node.go`'s `run` -- keeps reading the storage. So the
storage's state has a pending batch, `StorState.pend` (`[]` when none), and the method
triples answer only what the batch cannot change: `Term(i)` below its first index,
`Entries(lo, hi)` with `hi` at most its first index (`PendFrom`), `LastIndex` with
nothing pending. Two laws, ghost updates of the storage's owner, move the batch in and
out: `Hhandout` (with nothing pending, hand out the right `AT σ p` to append `p` --
`appendTok` for `isStorage` -- and keep reading at `{ σ with pend := p }`) and `Habsorb`
(the receipt `DT σ p` -- `appendedTok` -- of the append, which an implementation's
`Append` returns for the right, makes the owner's state `storAbsorb`: the batch
appended, `storApp`). Raft runs the hand-out in `acceptUnstable` (`Ready`) and the
absorb in `ownRaftLog_absorb`/`ownRawNode_appended`; it reads only below
`unstable.offset`, at or below the batch's first index (`PendLogOk`, `InvRaftlog.lean`).
`MemoryStorage` proves both laws with a ghost protocol under its lock
(`InvMemstorage.lean`). notes/decisions.md, "Storage: a pending append, for node.go".

### Why the triples return `#interface.nil` for the error

That is the contract, not a convenience: raft treats a non-nil error from any of these
three as unrecoverable and calls `panic`/`Logger.Panicf`. `Logger.wp_logf` deliberately
excludes the panicking methods, so a proof cannot step past such a call at all -- the
path must be shown unreachable. Saying "these three do not fail" is therefore the only
honest reading of raft's use of the interface.

Lean notes: `ownStorage` is the field of `class StorageModel GF` (binders `GF` and
`FfiSyntax`, which `Storage`/`entryID` need), exported; a section that uses it has
`[StorageModel GF]`.
Rocq's `l1 `prefix_of` l2` is `l1 <+: l2`, `take n l`/`drop n l` are `l.take n`/`l.drop n`.
The Rocq `ents !! k` is `ents[k]?` and `Z.to_nat` is `Int.toNat`. Inside `iprop(…)` a
Texan triple is `□ (∀ Φ, …)`, as Rocq's `{{{ … }}}` is, so `isStorage` is persistent
by `infer_instance`. A multiple return `(#li, #interface.nil)` is `PairV #li
#interface.nil`; `global_addr` is `globalAddr`.
-/
module

public import Proof.go_etcd_io.raft.v3.Defs

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- What a `Storage` holds, as the interface's contract states it: the compaction
boundary `prev` (index and term of the entry before the first stored one), the stored
entries `ents` after it, the metadata `ss` of its most recent snapshot (`Snapshot`),
and (2026-10-10) the batch `pend` the application may be appending. One record, so that the contract and its clients keep their shape when what is tracked
changes (notes/decisions.md, "Predicate indices"; until 2026-10-08 these were three
arguments of `ownStorage`, `isStorageWith`'s `P`, `memstorageFields` and
`ownMemoryStorage`). -/
structure StorState [FfiSyntax] where
  prev : entryID
  ents : List raftpb.Entry
  ss : entryID
  /-- The batch the application may be appending (2026-10-10, for `node.go`), `[]` when
  none: handed out by the hand-out law (`Hhandout`, below), when raft's `Ready` hands the
  entries out, and absorbed (`Habsorb`) once the application has appended it. While it
  is pending the storage may hold `ents` or `storApp` of it, and the method triples
  answer only what both agree on ("Storage: a pending append, for node.go",
  notes/decisions.md). -/
  pend : List raftpb.Entry

/-- An abstract description of a client-supplied `Storage`'s contents. A *parameter*
of the development, not an assumption: abstract because the implementation is not
raft's and is not in scope, so every result holds for whichever predicate the client
proves `isStorageWith` for (`MemstorageInstance.lean` does it for `MemoryStorage`).
Exclusive (not persistent) by intent, because a `Storage` is mutable -- `Append` and
`Compact` change it; nothing assumes otherwise. There is deliberately no global
instance: one would specialise every result to it. Until 2026-10-08 `ownStorage` was an
`axiom`, which fixed one unknown predicate that no client could ever establish. -/
class StorageModel (GF : BundledGFunctors) [FfiSyntax] where
  ownStorage : Storage → StorState → IProp GF
  /-- `appendTok st σ p` (2026-10-10): the application's right to append the batch `p`
  to the storage `st`, handed out at the state `σ` (with nothing pending) by the
  hand-out law (`isStorageWith`'s `Hhandout`). An implementation's own `Append` consumes
  it (`MemoryStorage.Append`, `Spec/.../MemoryStorage__Append.lean`). -/
  appendTok : Storage → StorState → List raftpb.Entry → IProp GF
  /-- `appendedTok st σ p`: the application did append `p` (what `Append` returns); the
  absorb law (`Habsorb`) gives it back to the storage's owner, whose state then holds
  the batch. -/
  appendedTok : Storage → StorState → List raftpb.Entry → IProp GF

export StorageModel (ownStorage appendTok appendedTok)

section termAt
variable [FfiSyntax]

/-- The term of index `i` in the log `prev :: ents`. `none` outside the range the
storage can answer for. -/
def termAt (prev : entryID) (ents : List raftpb.Entry) (i : w64) : Option w64 :=
  if uint.Z i = uint.Z prev.index' then some prev.term'
  else (fun e : raftpb.Entry => e.Term') <$>
         ents[(uint.Z i - uint.Z prev.index' - 1).toNat]?

/-- What a storage holding `σ.ents` after `σ.prev` holds once the entries `pend` are
appended to it the way `MemoryStorage.Append` does (`storage.go`): everything at or
above the batch's first index is replaced by the batch. `Append` is not part of the
`Storage` interface raft uses; it is how the *application* persists `Ready.Entries`.
(Defined in `InvRaftlog.lean` until 2026-10-10, when the hand-out and absorb laws below
came to mention it.) -/
def storApp (σ : StorState) (pend : List raftpb.Entry) : List raftpb.Entry :=
  match pend with
  | [] => σ.ents
  | e0 :: _ =>
      σ.ents.take (uint.Z e0.Index' - uint.Z σ.prev.index' - 1).toNat ++ pend

/-- `storApp` reads only `prev` and `ents`. -/
theorem storApp_pend (σ : StorState) (q pend : List raftpb.Entry) :
    storApp { σ with pend := q } pend = storApp σ pend := by
  cases pend <;> rfl

/-- The state once the pending batch is appended: the absorb law's result. -/
def storAbsorb (σ : StorState) : StorState :=
  { σ with ents := storApp σ σ.pend, pend := [] }

/-- The pending batch, if any, starts at or above index `n`: what the method triples
ask of a query (`Term(i)` with `n = i + 1`, `Entries(lo, hi)` with `n = hi`), so that
the answer is the same whether or not the application has appended the batch yet. -/
def PendFrom (σ : StorState) (n : Int) : Prop :=
  ∀ e0, σ.pend.head? = some e0 → n ≤ uint.Z e0.Index'

/-- The hand-out law's premise on the batch `p`: non-empty, starting above the
compaction boundary and at most one past the stored entries (so that `Append` neither
cuts the batch nor leaves a gap -- `MemoryStorage.Append`'s `Panicf`). -/
def PendOk (σ : StorState) (p : List raftpb.Entry) : Prop :=
  p ≠ [] ∧
  ∀ e0, p.head? = some e0 →
    uint.Z σ.prev.index' < uint.Z e0.Index' ∧
    uint.Z e0.Index' ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) + 1

end termAt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The interface contract, against an arbitrary ownership predicate `P` for the
storage's contents (a `StorState`, as in `ownStorage`). Persistent: it is a
property of the interface value (which method implementations it dispatches to), not
of the storage's current contents -- those live in `P`. `isStorage` below is the case
`P := ownStorage st` that the rest of the development uses; a concrete implementation
of the interface is shown to satisfy the contract by proving `isStorageWith` for its
own predicate (see `InvMemstorage.lean`). -/
def isStorageWith (P : StorState → IProp GF)
    (AT DT : StorState → List raftpb.Entry → IProp GF) (st : Storage) :
    IProp GF :=
  iprop(∃ (i : GoInterfaceOk),
  "%Hstok" ∷ ⌜st = interface.ok i⌝ ∗
  -- `LastIndex` only with nothing pending: the batch may extend the log (2026-10-10)
  "#HLastIndex" ∷ (∀ (σ : StorState),
     {{ P σ ∗ ⌜σ.pend = []⌝ }}
       (App (Val #(methods i.ty go!"LastIndex" i.v)) (Val #()))
     {{ (li : w64), RET (PairV #li #interface.nil);
         ⌜uint.Z li = uint.Z σ.prev.index' + (σ.ents.length : Int)⌝ ∗
         P σ }}) ∗
  "#HFirstIndex" ∷ (∀ (σ : StorState),
     {{ P σ }}
       (App (Val #(methods i.ty go!"FirstIndex" i.v)) (Val #()))
     {{ (fi : w64), RET (PairV #fi #interface.nil);
         ⌜uint.Z fi = uint.Z σ.prev.index' + 1⌝ ∗
         P σ }}) ∗
  "#HTerm" ∷ (∀ (σ : StorState) (i0 : w64),
     {{ P σ ∗
         ⌜uint.Z σ.prev.index' ≤ uint.Z i0 ∧
            uint.Z i0 ≤ uint.Z σ.prev.index' + (σ.ents.length : Int)⌝ ∗
         -- below the pending batch (2026-10-10)
         ⌜PendFrom σ (uint.Z i0 + 1)⌝ }}
       (App (Val #(methods i.ty go!"Term" i.v)) (Val #i0))
     {{ (t : w64), RET (PairV #t #interface.nil);
         ⌜termAt σ.prev σ.ents i0 = some t⌝ ∗ P σ }}) ∗
  "#HEntries" ∷ (∀ (σ : StorState)
      (lo hi maxSize : w64),
     {{ P σ ∗
         ⌜uint.Z σ.prev.index' + 1 ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
            uint.Z hi ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) + 1⌝ ∗
         -- below the pending batch (2026-10-10)
         ⌜PendFrom σ (uint.Z hi)⌝ }}
       (App (App (App (Val #(methods i.ty go!"Entries" i.v)) (Val #lo)) (Val #hi))
         (Val #maxSize))
     {{ (s : GoSlice) (es : List raftpb.Entry),
         RET (PairV #s #interface.nil);
         s ↦*□ es ∗
         ⌜es ≠ [] ∧
           (es.length : Int) ≤ uint.Z hi - uint.Z lo ∧
           (∀ e, e ∈ es → e ∈ σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat) ∧
           s.cap = s.len ∧
           -- *which* entries: the stored ones at `[lo, lo+1, ...]`, cut short by
           -- `maxSize` (the `Storage` interface's documented contract: "Entries returns a
           -- slice of consecutive log entries in the range [lo, hi)"; `MemoryStorage`
           -- returns `limitSize(ents[lo-offset:hi-offset])`). Added 2026-10-01 for
           -- `AppOk`'s prefix clause.
           es <+: (σ.ents.take (uint.Z hi - uint.Z σ.prev.index' - 1).toNat).drop
                    (uint.Z lo - uint.Z σ.prev.index' - 1).toNat⌝ ∗
         P σ }}) ∗
  /- The stable log's last index is far below `2^64`.

     This is the one *pure* clause of the contract, and it is what makes appending to
     the log possible at all. `ownRaftLog`'s `Hnowrap` says the whole log's last
     index leaves room for one more entry, and that bound is **not inductive**: after
     an append the log is one longer and the same bound is needed at the new length, so
     no invariant of the log alone can supply it (any invariant preserved by `append`
     would have to be closed under `+1` and therefore could not bound anything). The
     log's last index is `prev.index + |sents| + |uents|`, of which `append` only moves
     `|uents|` -- and *that* part is bounded for free, because `unstable.entries` is a
     Go slice and Perennial's `ownSlice_len` gives `length = sint.nat len < 2^63` of
     whatever slice the `append` returns. So the only piece that has to be assumed is
     the part `append` never touches: the compaction boundary and the stable prefix
     behind this interface.

     `2^61` is arbitrary but generous, and it is stated about the client's storage
     rather than about raft: a `Storage` whose last index is `2^61` has been fed
     2·10^18 entries. With it, the log's last index stays below `2^61 + 2^63`, leaving
     `appendEntry` room for a batch of up to `2^61` entries without wrapping -- see
     `spec_raft__appendEntry.v`, which is the only place this clause is used. Added
     2026-09-20, when `raft.wp_appendEntry` stopped being an axiom; before that the gap
     was a documented over-claim in that spec's comment.

     It hands `ownStorage` back because the conclusion is pure and `ownStorage` is not
     persistent: an `icases` against a bare `ownStorage st σ -∗ ⌜…⌝` would
     consume the storage (main's notes/gotchas.md, "Reading a pure fact out of a
     definition without consuming it"). -/
  "#Hbounded" ∷ □ (∀ (σ : StorState),
     P σ -∗
     ⌜uint.Z σ.prev.index' + (σ.ents.length : Int) < 2^61⌝ ∗
     P σ) ∗
  /- `Snapshot()` -- added 2026-09-20 for `raft.maybeSendSnapshot`.

     `raftLog.snapshot` (`new/code/go_etcd_io/raft/v3.v:864`) returns
     `l.unstable.snapshot` when it is non-nil and otherwise forwards to this method. It
     is non-nil only while a received snapshot is pending (`LogState.snap`, since
     2026-10-02; until then it was always nil), so every other snapshot on this path
     comes from the client.

     The contract is the *disjunction* `maybeSendSnapshot` is written against: either
     the distinguished, non-fatal `ErrSnapshotTemporarilyUnavailable` -- for which raft
     has a `return false` -- or success with a **non-empty** snapshot. Both halves are
     needed, and for the same reason as `FirstIndex`/`Term`: any other error reaches
     `panic(err)`, and an empty snapshot on the success path reaches
     `panic("need non-empty snapshot")` (`v3.v:3190-3196`). "Non-empty" is
     `IsEmptySnap`'s test, `Metadata.Index ≠ 0` (`v3.v:2004`).

     The error value is passed in as the package-level variable's points-to, so a proof
     compares the two interface values through `isInitialized` (`Base.lean`) rather
     than through a claim about `errors.New`.

     **What the snapshot is** (2026-10-03). On success the snapshot's metadata is the
     storage's own, `ss` (`snapId`, `Defs.lean`): "Snapshot returns the most recent
     snapshot" (`storage.go:85`), and `MemoryStorage.Snapshot` returns `ms.snapshot` by
     value. That is all this clause says about *which* snapshot; that it is of a
     committed prefix of raft's log is not a property of a `Storage` at all, and is
     kept by raft instead, as an invariant relating `ss` to its commit index
     (`ownRaftLog`'s `StoredSnapOk`, `InvRaftlog.lean`) -- true at `newRaft` by a
     premise on the initial storage, and preserved because nothing in scope changes
     the storage. And the snapshot's `ConfState.Voters` slice is handed out
     **read-only, for good** (`↦*□`), like `Entries`' result: the snapshot comes back
     by value, but its slices are the storage's, which `MemoryStorage` never writes in
     place (`CreateSnapshot` replaces the whole `ConfState`; `ApplySnapshot` the whole
     snapshot). raft puts that slice in a `MsgSnap` (`maybeSendSnapshot`) and the
     abstraction of the queued message reads it (`msgAbs`, `InvRaftPhys.lean`).

     *Client assumptions* in this clause, as before: the snapshot is non-empty on
     success (an empty one is a `panic` in raft; raft only asks after a `Term` or
     `Entries` failed with `ErrCompacted`, i.e. once the storage has compacted, which
     presupposes a snapshot), and the voters' read-only ownership. -/
  "#HSnapshot" ∷ (∀ (σ : StorState)
      (esu : GoInterface),
     {{ P σ ∗
         globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu }}
       (App (Val #(methods i.ty go!"Snapshot" i.v)) (Val #()))
     {{ (snap : raftpb.Snapshot) (err : GoInterface), RET (PairV #snap #err);
         P σ ∗
         (⌜err = esu⌝ ∨
          (⌜err = interface.nil ∧ snapId snap = σ.ss ∧ snap.Metadata'.Index' ≠ W64 0⌝ ∗
           ∃ (voters : List w64), snap.Metadata'.ConfState'.Voters' ↦*□ voters)) }}) ∗
  /- The pending append (2026-10-10, for `node.go`; notes/decisions.md, "Storage: a
     pending append, for node.go"). The application appends a `Ready`'s entries on its own
     goroutine while raft keeps reading the storage. Two laws, ghost updates of the
     storage's owner:

     - **hand-out**: with nothing pending, the owner hands out the right to append a
       batch `p` (`AT σ p`) and keeps reading at `{ σ with pend := p }`, where the method
       triples answer only queries the batch cannot affect (`PendFrom`, `LastIndex` with
       nothing pending);
     - **absorb**: the receipt of the append (`DT σ p`, which an implementation's
       `Append` returns for `AT σ p`) turns the owner's state into the appended one,
       `storAbsorb`; the receipt fixes which state the batch was handed out at.

     `PendOk` is what the hand-out asks of the batch. -/
  "#Hhandout" ∷ □ (∀ (σ : StorState) (p : List raftpb.Entry),
     P σ -∗ ⌜σ.pend = [] ∧ PendOk σ p⌝ ==∗ P { σ with pend := p } ∗ AT σ p) ∗
  "#Habsorb" ∷ □ (∀ (σ1 σ : StorState) (p : List raftpb.Entry),
     P σ1 -∗ DT σ p ==∗ ⌜σ1 = { σ with pend := p }⌝ ∗ P (storAbsorb σ1)))

/-- The contract against the abstract `ownStorage`: what every client of the interface
assumes. -/
def isStorage (st : Storage) : IProp GF :=
  isStorageWith (ownStorage st) (appendTok st) (appendedTok st) st

instance isStorageWith_pers (P : StorState → IProp GF)
    (AT DT : StorState → List raftpb.Entry → IProp GF)
    (st : Storage) : Persistent (isStorageWith P AT DT st) := by
  unfold isStorageWith; infer_instance

instance isStorage_pers (st : Storage) : Persistent (isStorage (GF := GF) st) := by
  unfold isStorage; infer_instance

/-- What a client of raft holds for the entries `p` a `Ready` handed out (2026-10-10):
nothing to do for no entries, otherwise the right to append them (`appendTok`), at the
storage's state when they were handed out. `RawNode.Ready` returns it. -/
def appendRight (st : Storage) (p : List raftpb.Entry) : IProp GF :=
  iprop(⌜p = []⌝ ∨ ∃ σ, appendTok st σ p)

/-- ... and the receipt the client gives back once it has appended them
(`ownRawNode_appended`, `InvRawnode.lean`). -/
def appendReceipt (st : Storage) (p : List raftpb.Entry) : IProp GF :=
  iprop(⌜p = []⌝ ∨ ∃ σ, appendedTok st σ p)

/-- The hand-out law at a batch that may be empty: for `[]` nothing happens (the state
already has nothing pending), otherwise `Hhandout`. What `raftLog.acceptUnstable` runs
for the entries a `Ready` hands out. -/
theorem isStorage_handout (st : Storage) (σ : StorState) (p : List raftpb.Entry)
    (Hpo : σ.pend = [] ∧ (p ≠ [] → PendOk σ p)) :
    ⊢ isStorage (GF := GF) st -∗ ownStorage st σ ==∗
      ownStorage st { σ with pend := p } ∗ appendRight st p := by
  iintro #Hst HS
  unfold appendRight
  by_cases Hne : p = []
  · have Hσ : ({ σ with pend := p } : StorState) = σ := by
      rw [Hne, ← Hpo.1]
    rw [Hσ]
    imodintro
    iframe HS
    ileft
    ipureintro
    exact Hne
  unfold isStorage isStorageWith
  icases Hst with ⟨%i, %Hi, #HL, #HF, #HT, #HE, #Hb, #HSn, #Hho, #Hab⟩
  ihave Hpo' : ⌜σ.pend = [] ∧ PendOk σ p⌝ $$ []
  · ipureintro; exact ⟨Hpo.1, Hpo.2 Hne⟩
  imod Hho $$ HS Hpo' with ⟨HS, Htok⟩
  imodintro
  iframe HS
  iright
  iexists σ
  iexact Htok

end proof

end EtcdGrove
end Perennial
