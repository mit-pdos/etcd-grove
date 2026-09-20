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

    [own_Storage st prev ents] says: the storage behind the interface value
    [st] holds the log entries [ents], immediately following the entry
    [prev].  [prev] is the compaction boundary -- the last entry the storage
    has discarded the payload of but still knows the term of.  This is exactly
    how [MemoryStorage] represents its log (a dummy entry at [ents[0]]), and
    it is what makes [Term] total on [[prev.index, prev.index + |ents|]]
    rather than only on [(prev.index, ...]].

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
      - the slice is **lent**, not given: the returned points-to comes with
        a wand back to [own_Storage].  [MemoryStorage] hands out a view of
        its own buffer, so ownership cannot be transferred.
    The fraction is existential because the client chooses it.  What the
    returned entries *are* (which indices) is not stated; nothing on the
    election path reads them beyond their [Type], for which membership in
    the stored list is enough.

    [Snapshot] and [InitialState] are deliberately **omitted**.  Nothing on
    the election path calls them, and an assumption that is not needed is an
    assumption not worth making: each would be a fresh claim about client
    code.  Add them when a proof needs them, with the same "state it, then
    use it" discipline.

    *** Why the triples return [#interface.nil] for the error

    That is the contract, not a convenience: raft treats a non-nil error from
    any of these three as unrecoverable and calls [panic]/[Logger.Panicf].
    [wp_Logger__logf] deliberately excludes the panicking methods, so a proof
    cannot step past such a call at all -- the path must be shown
    unreachable.  Saying "these three do not fail" is therefore the only
    honest reading of raft's use of the interface. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.defs.

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
Axiom own_Storage : raft.Storage.t → raft.entryID.t → list raftpb.Entry.t → iProp Σ.

(** The term of index [i] in the log [prev :: ents].  [None] outside the
    range the storage can answer for. *)
Definition term_at (prev : raft.entryID.t) (ents : list raftpb.Entry.t) (i : w64)
  : option w64 :=
  if decide (uint.Z i = uint.Z prev.(raft.entryID.index'))
  then Some prev.(raft.entryID.term')
  else (λ e, e.(raftpb.Entry.Term')) <$>
         (ents !! Z.to_nat (uint.Z i - uint.Z prev.(raft.entryID.index') - 1)).

(** The interface contract.  Persistent: it is a property of the interface
    value (which method implementations it dispatches to), not of the
    storage's current contents -- those live in [own_Storage]. *)
Definition is_Storage (st : raft.Storage.t) : iProp Σ :=
  ∃ (i : interface.t_ok),
  "%Hstok" ∷ ⌜ st = interface.ok i ⌝ ∗
  "#HLastIndex" ∷ (∀ prev ents,
     {{{ own_Storage st prev ents }}}
       #(methods i.(interface.ty) "LastIndex"%go i.(interface.v)) #()
     {{{ (li : w64), RET (#li, #interface.nil);
         ⌜ (uint.Z li = uint.Z prev.(raft.entryID.index')
                        + Z.of_nat (length ents))%Z ⌝ ∗
         own_Storage st prev ents }}}) ∗
  "#HFirstIndex" ∷ (∀ prev ents,
     {{{ own_Storage st prev ents }}}
       #(methods i.(interface.ty) "FirstIndex"%go i.(interface.v)) #()
     {{{ (fi : w64), RET (#fi, #interface.nil);
         ⌜ (uint.Z fi = uint.Z prev.(raft.entryID.index') + 1)%Z ⌝ ∗
         own_Storage st prev ents }}}) ∗
  "#HTerm" ∷ (∀ prev ents (i0 : w64),
     {{{ own_Storage st prev ents ∗
         ⌜ (uint.Z prev.(raft.entryID.index') ≤ uint.Z i0 ≤
            uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents))%Z ⌝ }}}
       #(methods i.(interface.ty) "Term"%go i.(interface.v)) #i0
     {{{ (t : w64), RET (#t, #interface.nil);
         ⌜ term_at prev ents i0 = Some t ⌝ ∗ own_Storage st prev ents }}}) ∗
  "#HEntries" ∷ (∀ prev ents (lo hi maxSize : w64),
     {{{ own_Storage st prev ents ∗
         ⌜ (uint.Z prev.(raft.entryID.index') + 1 ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
            uint.Z hi ≤ uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents) + 1)%Z ⌝ }}}
       #(methods i.(interface.ty) "Entries"%go i.(interface.v)) #lo #hi #maxSize
     {{{ (s : slice.t) (es : list raftpb.Entry.t) (dq : dfrac),
         RET (#s, #interface.nil);
         s ↦*{dq} es ∗
         ⌜ es ≠ [] ∧
           (Z.of_nat (length es) ≤ uint.Z hi - uint.Z lo)%Z ∧
           (∀ e, e ∈ es → e ∈ ents) ∧
           s.(slice.cap) = s.(slice.len) ⌝ ∗
         (s ↦*{dq} es -∗ own_Storage st prev ents) }}}).

Global Instance is_Storage_pers st : Persistent (is_Storage st).
Proof. apply _. Qed.

End proof.
