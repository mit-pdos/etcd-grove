(** * The [Storage] interface

    [raftLog.storage] is a [Storage] **interface value**, supplied by the
    application (etcd provides one; raft itself only ships [MemoryStorage] for
    tests).  It is therefore a legitimate abstraction boundary: there is no
    raft code to verify behind it, only a contract that raft relies on.  So
    this file states that contract.

    The shape follows [own_AckedIndexer] (`v3_proof/readonly.v`): a
    [Definition] bundling one Hoare triple per method, against an abstract
    resource describing the stored log.

    **The whole trust surface of this file is one line**: the abstract
    predicate [own_Storage], below.  Everything else is a [Definition] built
    from it, so the triples are not axioms -- they are what a client has to
    supply, and a caller that has no [is_Storage] gets nothing.

    *** The abstraction

    [own_Storage st prev ents ss] says: the storage behind the interface
    value [st] holds the log entries [ents], immediately following the entry
    [prev], and its most recent snapshot has metadata [ss] (as an
    [entryID]: [(Metadata.Term, Metadata.Index)]).  [prev] is the compaction
    boundary -- the last entry the storage has discarded the payload of but
    still knows the term of.  This is exactly how [MemoryStorage] represents
    its log (a dummy entry at [ents[0]]), and it is what makes [Term] total
    on [[prev.index, prev.index + |ents|]] rather than only on
    [(prev.index, ...]].  [ss] is [MemoryStorage.snapshot]'s metadata, which
    [Snapshot()] returns (added 2026-10-03, so that [raft] can relate the
    snapshot it forwards to its own commit index -- see [HSnapshot] and
    [own_raftLog]'s [stored_snap_ok]).

    Index [prev.index + 1 + k] holds [ents !! k], so:
      - [FirstIndex()] = [prev.index + 1]
      - [LastIndex()]  = [prev.index + |ents|]
      - [Term(i)]      = [term_at prev ents i], defined for
                         [prev.index <= i <= prev.index + |ents|].

    *** Which methods are here, and why the others are not

    [Storage] has six methods.  Four are specified: [FirstIndex],
    [LastIndex], [Term] and (since 2026-09-19) [Entries].  The first three
    are what raft's own log code calls on the leader-election path
    ([raftLog.firstIndex], [raftLog.lastIndex], [raftLog.term]), and each of
    them **panics** on an error return, so a proof has to know they succeed.

    [Entries] is reached by [raftLog.slice], which [raftLog.scan] and hence
    [raft.hasUnappliedConfChanges] call on the [hup] path whenever the
    unapplied range starts in the stable prefix.  Its contract:
      - the range premise [firstIndex <= lo < hi <= lastIndex + 1] is
        exactly what makes [MemoryStorage.Entries]'s [ErrCompacted] and
        [ErrUnavailable] returns unreachable, so the error is [nil];
      - the result is a **non-empty** sub-list of the stored entries of
        length at most [hi - lo] -- [MemoryStorage] applies [limitSize],
        which keeps at least one entry;
      - **[cap = len]**: [MemoryStorage.Entries] returns
        [ents[:len(ents):len(ents)]] precisely so that a caller's [append]
        reallocates instead of writing into [ms.ents].  [raftLog.slice]
        relies on this through [extend], whose in-place branch would
        otherwise write into storage memory this contract does not grant;
      - the entries are handed out **read-only and for good**
        ([s ↦*□ es], no wand back).  This is the interface's own contract
        ([storage.go:56-67], upamanyus/etcd-raft 531b20c): "The caller of
        Entries owns the returned slice, and may append to it. The
        individual entries in the slice must not be mutated, neither by the
        Storage implementation nor the caller."  [MemoryStorage] keeps it:
        [Entries] caps the result ([storage.go:155]), [Append] rebuilds with
        [append(ms.ents[:offset:offset], ...)] "as they may still be
        referenced from outside MemoryStorage" ([storage.go:303-305]), and
        [Compact] allocates.  The slack is not handed out: [cap = len].
        (Until 2026-09-29 the slice was *lent*, at an existential fraction,
        with a wand back to [own_Storage]; that forced a page loan on
        [raftLog.slice]'s callers -- [logstate.page].)
    What the
    returned entries *are* is stated only as membership: every one is a
    stored entry **below [hi]** ([take (hi - prev.index - 1) ents]).  The
    bound was added 2026-10-01, when [own_raftLog]'s stable part became a
    *visible prefix* of the stored entries ([inv_raftlog.v]): [raftLog.slice]
    reads only below [unstable.offset], and without the bound it could not
    tell an entry it got back from a shadowed one.  [MemoryStorage.Entries]
    returns [ms.ents[lo-offset : hi-offset]] cut by [limitSize], so it
    holds.

    Besides the four triples the contract has one **pure clause**,
    [Hbounded]: the stable log's last index is below [2^61].  It is the
    assumption that makes appending to the log possible -- the log's no-wrap
    invariant is not inductive, and the part of the log an [append] does not
    move is exactly the part behind this interface.  The long version is at
    the clause itself.

    [Snapshot] was added on 2026-09-20, by exactly that rule:
    [raft.maybeSendSnapshot] calls it, and [maybeSendSnapshot] is reachable
    from [bcastAppend] because nothing in [own_progress] bounds a peer's
    [Next] against the log, so [raftLog.term(pr.Next-1)] may legitimately
    return [ErrCompacted].  Its contract is a disjunction -- the
    distinguished [ErrSnapshotTemporarilyUnavailable], or a non-empty
    snapshot -- because every other outcome reaches a [panic].

    [InitialState] is deliberately **omitted**.  Nothing on the election
    path calls it, and an assumption that is not needed is an assumption not
    worth making: it would be a fresh claim about client code.  Add it when
    a proof needs it, with the same "state it, then use it" discipline.

    *** Why the triples return [#interface.nil] for the error

    That is the contract, not a convenience: raft treats a non-nil error from
    any of these three as unrecoverable and calls [panic]/[Logger.Panicf].
    [wp_Logger__logf] deliberately excludes the panicking methods, so a proof
    cannot step past such a call at all -- the path must be shown
    unreachable.  Saying "these three do not fail" is therefore the only
    honest reading of raft's use of the interface. *)

Require Export New.proof.go_etcd_io.raft.election_proof.defs.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** The one assumption in this file: an abstract description of a
    client-supplied [Storage]'s contents.  Abstract because the
    implementation is not raft's and is not in scope; exclusive (not
    persistent) because a [Storage] is mutable -- [Append] and [Compact]
    change it -- so two different contents for the same [st] must not be
    simultaneously assertable. *)
Axiom own_Storage : raft.Storage.t → raft.entryID.t → list raftpb.Entry.t →
                    raft.entryID.t → iProp Σ.

(** The term of index [i] in the log [prev :: ents].  [None] outside the
    range the storage can answer for. *)
Definition term_at (prev : raft.entryID.t) (ents : list raftpb.Entry.t) (i : w64)
  : option w64 :=
  if decide (uint.Z i = uint.Z prev.(raft.entryID.index'))
  then Some prev.(raft.entryID.term')
  else (λ e, e.(raftpb.Entry.Term')) <$>
         (ents !! Z.to_nat (uint.Z i - uint.Z prev.(raft.entryID.index') - 1)).

(** The interface contract, against an arbitrary ownership predicate [P] for
    the storage's contents ([prev], [ents], [ss] as in [own_Storage]).
    Persistent: it is a property of the interface value (which method
    implementations it dispatches to), not of the storage's current contents
    -- those live in [P].  [is_Storage] below is the case [P := own_Storage st]
    that the rest of the development uses; a concrete implementation of the
    interface is shown to satisfy the contract by proving [is_Storage_with]
    for its own predicate (see [inv_memstorage.v]). *)
Definition is_Storage_with
  (P : raft.entryID.t → list raftpb.Entry.t → raft.entryID.t → iProp Σ)
  (st : raft.Storage.t) : iProp Σ :=
  ∃ (i : interface.t_ok),
  "%Hstok" ∷ ⌜ st = interface.ok i ⌝ ∗
  "#HLastIndex" ∷ (∀ prev ents ss,
     {{{ P prev ents ss }}}
       #(methods i.(interface.ty) "LastIndex"%go i.(interface.v)) #()
     {{{ (li : w64), RET (#li, #interface.nil);
         ⌜ (uint.Z li = uint.Z prev.(raft.entryID.index')
                        + Z.of_nat (length ents))%Z ⌝ ∗
         P prev ents ss }}}) ∗
  "#HFirstIndex" ∷ (∀ prev ents ss,
     {{{ P prev ents ss }}}
       #(methods i.(interface.ty) "FirstIndex"%go i.(interface.v)) #()
     {{{ (fi : w64), RET (#fi, #interface.nil);
         ⌜ (uint.Z fi = uint.Z prev.(raft.entryID.index') + 1)%Z ⌝ ∗
         P prev ents ss }}}) ∗
  "#HTerm" ∷ (∀ prev ents ss (i0 : w64),
     {{{ P prev ents ss ∗
         ⌜ (uint.Z prev.(raft.entryID.index') ≤ uint.Z i0 ≤
            uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents))%Z ⌝ }}}
       #(methods i.(interface.ty) "Term"%go i.(interface.v)) #i0
     {{{ (t : w64), RET (#t, #interface.nil);
         ⌜ term_at prev ents i0 = Some t ⌝ ∗ P prev ents ss }}}) ∗
  "#HEntries" ∷ (∀ prev ents ss (lo hi maxSize : w64),
     {{{ P prev ents ss ∗
         ⌜ (uint.Z prev.(raft.entryID.index') + 1 ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
            uint.Z hi ≤ uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents) + 1)%Z ⌝ }}}
       #(methods i.(interface.ty) "Entries"%go i.(interface.v)) #lo #hi #maxSize
     {{{ (s : slice.t) (es : list raftpb.Entry.t),
         RET (#s, #interface.nil);
         s ↦*□ es ∗
         ⌜ es ≠ [] ∧
           (Z.of_nat (length es) ≤ uint.Z hi - uint.Z lo)%Z ∧
           (∀ e, e ∈ es → e ∈ take (Z.to_nat (uint.Z hi - uint.Z prev.(raft.entryID.index') - 1)) ents) ∧
           s.(slice.cap) = s.(slice.len) ∧
           (* *which* entries: the stored ones at [lo, lo+1, ...], cut
              short by [maxSize] (the [Storage] interface's documented
              contract: "Entries returns a slice of consecutive log entries
              in the range [lo, hi)"; [MemoryStorage] returns
              [limitSize(ents[lo-offset:hi-offset])]).  Added 2026-10-01
              for [app_ok]'s prefix clause. *)
           es `prefix_of` drop (Z.to_nat (uint.Z lo - uint.Z prev.(raft.entryID.index') - 1))
                            (take (Z.to_nat (uint.Z hi - uint.Z prev.(raft.entryID.index') - 1)) ents) ⌝ ∗
         P prev ents ss }}}) ∗
  (** The stable log's last index is far below [2^64].

      This is the one *pure* clause of the contract, and it is what makes
      appending to the log possible at all.  [own_raftLog_core]'s [Hnowrap]
      says the whole log's last index leaves room for one more entry, and
      that bound is **not inductive**: after an append the log is one longer
      and the same bound is needed at the new length, so no invariant of the
      log alone can supply it (any invariant preserved by [append] would have
      to be closed under [+1] and therefore could not bound anything).  The
      log's last index is [prev.index + |sents| + |uents|], of which
      [append] only moves [|uents|] -- and *that* part is bounded for free,
      because [unstable.entries] is a Go slice and Perennial's
      [own_slice_len] gives [length = sint.nat len < 2^63] of whatever slice
      the [append] returns.  So the only piece that has to be assumed is the
      part [append] never touches: the compaction boundary and the stable
      prefix behind this interface.

      [2^61] is arbitrary but generous, and it is stated about the client's
      storage rather than about raft: a [Storage] whose last index is
      [2^61] has been fed 2·10^18 entries.  With it, the log's last index
      stays below [2^61 + 2^63], leaving [appendEntry] room for a batch of
      up to [2^61] entries without wrapping -- see
      [spec_raft__appendEntry.v], which is the only place this clause is
      used.  Added 2026-09-20, when [wp_raft__appendEntry] stopped being an
      [Axiom]; before that the gap was a documented over-claim in that
      spec's comment.

      It hands [own_Storage] back because the conclusion is pure and
      [own_Storage] is not persistent: an [iDestruct] against a bare
      [own_Storage st prev ents -∗ ⌜…⌝] would consume the storage
      (notes/gotchas.md, "Reading a pure fact out of a definition without
      consuming it"). *)
  "#Hbounded" ∷ □ (∀ prev ents ss,
     P prev ents ss -∗
     ⌜ (uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents)
        < 2^61)%Z ⌝ ∗
     P prev ents ss) ∗
  (** [Snapshot()] -- added 2026-09-20 for [raft.maybeSendSnapshot].

      [raftLog.snapshot] ([new/code/go_etcd_io/raft/v3.v:864]) returns
      [l.unstable.snapshot] when it is non-nil and otherwise forwards to this
      method.  It is non-nil only while a received snapshot is pending
      ([logstate.snap], since 2026-10-02; until then it was always nil), so
      every other snapshot on this path comes from the client.

      The contract is the *disjunction* [maybeSendSnapshot] is written
      against: either the distinguished, non-fatal
      [ErrSnapshotTemporarilyUnavailable] -- for which raft has a
      [return false] -- or success with a **non-empty** snapshot.  Both
      halves are needed, and for the same reason as [FirstIndex]/[Term]:
      any other error reaches [panic(err)], and an empty snapshot on the
      success path reaches [panic("need non-empty snapshot")]
      ([v3.v:3190-3196]).  "Non-empty" is [IsEmptySnap]'s test,
      [Metadata.Index ≠ 0] ([v3.v:2004]).

      The error value is passed in as the package-level variable's
      points-to, so a proof compares the two interface values through
      [is_initialized] ([base.v]) rather than through a claim about
      [errors.New].

      **What the snapshot is** (2026-10-03).  On success the snapshot's
      metadata is the storage's own, [ss] ([snap_id], [defs.v]): "Snapshot
      returns the most recent snapshot" ([storage.go:85]), and
      [MemoryStorage.Snapshot] returns [ms.snapshot] by value.  That is all
      this clause says about *which* snapshot; that it is of a committed
      prefix of raft's log is not a property of a [Storage] at all, and is
      kept by raft instead, as an invariant relating [ss] to its commit
      index ([own_raftLog]'s [stored_snap_ok], [inv_raftlog.v]) -- true at
      [newRaft] by a premise on the initial storage, and preserved because
      nothing in scope changes the storage.
      And the snapshot's [ConfState.Voters] slice is handed out
      **read-only, for good** ([↦*□]), like [Entries]' result: the
      snapshot comes back by value, but its slices are the storage's, which
      [MemoryStorage] never writes in place ([CreateSnapshot] replaces the
      whole [ConfState]; [ApplySnapshot] the whole snapshot).  raft puts
      that slice in a [MsgSnap] ([maybeSendSnapshot]) and the abstraction of
      the queued message reads it ([msg_abs], [inv_raft_phys.v]).

      *Client assumptions* in this clause, as before: the snapshot is
      non-empty on success (an empty one is a [panic] in raft; raft only
      asks after a [Term] or [Entries] failed with [ErrCompacted], i.e.
      once the storage has compacted, which presupposes a snapshot), and
      the voters' read-only ownership. *)
  "#HSnapshot" ∷ (∀ prev ents ss (esu : interface.t),
     {{{ P prev ents ss ∗
         (global_addr raft.ErrSnapshotTemporarilyUnavailable) ↦□ esu }}}
       #(methods i.(interface.ty) "Snapshot"%go i.(interface.v)) #()
     {{{ (snap : raftpb.Snapshot.t) (err : interface.t), RET (#snap, #err);
         P prev ents ss ∗
         (⌜ err = esu ⌝ ∨
          (⌜ err = interface.nil ∧ snap_id snap = ss ∧
             snap.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.Index')
               ≠ W64 0 ⌝ ∗
           ∃ (voters : list w64),
             snap.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState')
               .(raftpb.ConfState.Voters') ↦*□ voters)) }}}).

(** The contract against the abstract [own_Storage]: what every client of the
    interface assumes. *)
Definition is_Storage (st : raft.Storage.t) : iProp Σ :=
  is_Storage_with (own_Storage st) st.

Global Instance is_Storage_with_pers P st : Persistent (is_Storage_with P st).
Proof. apply _. Qed.

Global Instance is_Storage_pers st : Persistent (is_Storage st).
Proof. apply _. Qed.

End proof.
