/-
Port of `election_proof/inv_storage.v`: the `Storage` interface.

`raftLog.storage` is a `Storage` **interface value**, supplied by the application (etcd
provides one; raft itself only ships `MemoryStorage` for tests). It is therefore a
legitimate abstraction boundary: there is no raft code to verify behind it, only a
contract that raft relies on. So this file states that contract.

The shape follows `ownAckedIndexer` (`v3_proof/readonly.lean`): a definition bundling
one Hoare triple per method, against an abstract resource describing the stored log.

**The whole trust surface of this file is one line**: the abstract predicate
`ownStorage`, below. Everything else is a definition built from it, so the triples are
not axioms -- they are what a client has to supply, and a caller that has no
`isStorage` gets nothing.

### The abstraction

`ownStorage st prev ents` says: the storage behind the interface value `st` holds the
log entries `ents`, immediately following the entry `prev`. `prev` is the compaction
boundary -- the last entry the storage has discarded the payload of but still knows the
term of. This is exactly how `MemoryStorage` represents its log (a dummy entry at
`ents[0]`), and it is what makes `Term` total on `[prev.index, prev.index + |ents|]`
rather than only on `(prev.index, ...]`.

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
What the returned entries *are* (which indices) is not stated; nothing on the election
path reads them beyond their `Type`, for which membership in the stored list is enough.

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

### Why the triples return `#interface.nil` for the error

That is the contract, not a convenience: raft treats a non-nil error from any of these
three as unrecoverable and calls `panic`/`Logger.Panicf`. `Logger.wp_logf` deliberately
excludes the panicking methods, so a proof cannot step past such a call at all -- the
path must be shown unreachable. Saying "these three do not fail" is therefore the only
honest reading of raft's use of the interface.

Lean notes: `ownStorage` is an `axiom` with its binders written out (`GF` and
`FfiSyntax`, which `Storage`/`entryID` need); it mentions no other section variable.
The Rocq `ents !! k` is `ents[k]?` and `Z.to_nat` is `Int.toNat`. Inside `iprop(…)` a
Texan triple is `□ (∀ Φ, …)`, as Rocq's `{{{ … }}}` is, so `isStorage` is persistent
by `infer_instance`. A multiple return `(#li, #interface.nil)` is `PairV #li
#interface.nil`; `global_addr` is `globalAddr`.
-/
import EtcdGrove.Raft.ElectionProof.Defs

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- The one assumption in this file: an abstract description of a client-supplied
`Storage`'s contents. Abstract because the implementation is not raft's and is not in
scope; exclusive (not persistent) because a `Storage` is mutable -- `Append` and
`Compact` change it -- so two different contents for the same `st` must not be
simultaneously assertable. -/
axiom ownStorage {GF : BundledGFunctors} [FfiSyntax] :
  Storage → entryID → List raftpb.Entry → IProp GF

section termAt
variable [FfiSyntax]

/-- The term of index `i` in the log `prev :: ents`. `none` outside the range the
storage can answer for. -/
def termAt (prev : entryID) (ents : List raftpb.Entry) (i : w64) : Option w64 :=
  if uint.Z i = uint.Z prev.index' then some prev.term'
  else (fun e : raftpb.Entry => e.Term') <$>
         ents[(uint.Z i - uint.Z prev.index' - 1).toNat]?

end termAt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The interface contract. Persistent: it is a property of the interface value (which
method implementations it dispatches to), not of the storage's current contents --
those live in `ownStorage`. -/
def isStorage (st : Storage) : IProp GF :=
  iprop(∃ (i : GoInterfaceOk),
  "%Hstok" ∷ ⌜st = interface.ok i⌝ ∗
  "#HLastIndex" ∷ (∀ (prev : entryID) (ents : List raftpb.Entry),
     {{ ownStorage st prev ents }}
       (App (Val #(methods i.ty go!"LastIndex" i.v)) (Val #()))
     {{ (li : w64), RET (PairV #li #interface.nil);
         ⌜uint.Z li = uint.Z prev.index' + (ents.length : Int)⌝ ∗
         ownStorage st prev ents }}) ∗
  "#HFirstIndex" ∷ (∀ (prev : entryID) (ents : List raftpb.Entry),
     {{ ownStorage st prev ents }}
       (App (Val #(methods i.ty go!"FirstIndex" i.v)) (Val #()))
     {{ (fi : w64), RET (PairV #fi #interface.nil);
         ⌜uint.Z fi = uint.Z prev.index' + 1⌝ ∗
         ownStorage st prev ents }}) ∗
  "#HTerm" ∷ (∀ (prev : entryID) (ents : List raftpb.Entry) (i0 : w64),
     {{ ownStorage st prev ents ∗
         ⌜uint.Z prev.index' ≤ uint.Z i0 ∧
            uint.Z i0 ≤ uint.Z prev.index' + (ents.length : Int)⌝ }}
       (App (Val #(methods i.ty go!"Term" i.v)) (Val #i0))
     {{ (t : w64), RET (PairV #t #interface.nil);
         ⌜termAt prev ents i0 = some t⌝ ∗ ownStorage st prev ents }}) ∗
  "#HEntries" ∷ (∀ (prev : entryID) (ents : List raftpb.Entry) (lo hi maxSize : w64),
     {{ ownStorage st prev ents ∗
         ⌜uint.Z prev.index' + 1 ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
            uint.Z hi ≤ uint.Z prev.index' + (ents.length : Int) + 1⌝ }}
       (App (App (App (Val #(methods i.ty go!"Entries" i.v)) (Val #lo)) (Val #hi))
         (Val #maxSize))
     {{ (s : GoSlice) (es : List raftpb.Entry),
         RET (PairV #s #interface.nil);
         s ↦*□ es ∗
         ⌜es ≠ [] ∧
           (es.length : Int) ≤ uint.Z hi - uint.Z lo ∧
           (∀ e, e ∈ es → e ∈ ents) ∧
           s.cap = s.len⌝ ∗
         ownStorage st prev ents }}) ∗
  /- The stable log's last index is far below `2^64`.

     This is the one *pure* clause of the contract, and it is what makes appending to
     the log possible at all. `ownRaftLogCore`'s `Hnowrap` says the whole log's last
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
     persistent: an `icases` against a bare `ownStorage st prev ents -∗ ⌜…⌝` would
     consume the storage (main's notes/gotchas.md, "Reading a pure fact out of a
     definition without consuming it"). -/
  "#Hbounded" ∷ □ (∀ (prev : entryID) (ents : List raftpb.Entry),
     ownStorage st prev ents -∗
     ⌜uint.Z prev.index' + (ents.length : Int) < 2^61⌝ ∗
     ownStorage st prev ents) ∗
  /- `Snapshot()` -- added 2026-09-20 for `raft.maybeSendSnapshot`.

     `raftLog.snapshot` (Goose's `v3` code) returns `l.unstable.snapshot` when it is
     non-nil and otherwise forwards to this method; `ownRaftLogCore`'s `Hnosnap` says it
     is always nil here, so every snapshot on this path comes from the client.

     The contract is the *disjunction* `maybeSendSnapshot` is written against: either
     the distinguished, non-fatal `ErrSnapshotTemporarilyUnavailable` -- for which raft
     has a `return false` -- or success with a **non-empty** snapshot. Both halves are
     needed, and for the same reason as `FirstIndex`/`Term`: any other error reaches
     `panic(err)`, and an empty snapshot on the success path reaches
     `panic("need non-empty snapshot")`. "Non-empty" is `IsEmptySnap`'s test,
     `Metadata.Index ≠ 0`.

     The error value is passed in as the package-level variable's points-to, so a proof
     compares the two interface values through `isPkgInit` (`Base.lean`) rather than
     through a claim about `errors.New`. What the snapshot *contains* is unspecified:
     raft only forwards it and takes `Metadata.Index`/`Metadata.Term` for a
     `Progress.BecomeSnapshot` and a `MsgSnap` the model does not see. -/
  "#HSnapshot" ∷ (∀ (prev : entryID) (ents : List raftpb.Entry) (esu : GoInterface),
     {{ ownStorage st prev ents ∗
         globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu }}
       (App (Val #(methods i.ty go!"Snapshot" i.v)) (Val #()))
     {{ (snap : raftpb.Snapshot) (err : GoInterface), RET (PairV #snap #err);
         ownStorage st prev ents ∗
         ⌜err = esu ∨
           (err = interface.nil ∧ snap.Metadata'.Index' ≠ W64 0)⌝ }}))

instance isStorage_pers (st : Storage) : Persistent (isStorage (GF := GF) st) := by
  unfold isStorage; infer_instance

end proof

end EtcdGrove
end Perennial
