(** * The raft log

    [own_raftLog l] is full ownership of the [raftLog] struct at [l], together
    with everything that hangs off it: the [unstable] suffix's entry slice and
    the [Storage] behind the stable prefix.

    *** What the predicate guarantees

    It exposes the log as an **entry list** -- a compaction boundary [prev]
    (an [entryID], the last index the log has discarded the payload of but
    still knows the term of) plus the entries after it, split into the stable
    prefix [sents] (in [storage]) and the unstable suffix [uents] (in
    [unstable.entries]).  The whole log is [sents ++ uents] at indices
    [prev.index+1 ...], and:

    - [log_indices_ok]: the indices are contiguous from [prev.index+1], and
      [prev.index + |sents| + |uents| + 1 < 2^64] so nothing wraps.  Both are
      needed to show [lastEntryID] cannot hit its [Panicf]: the [Panicf] fires
      when [term(lastIndex())] errors, and an index that wrapped would come
      back [ErrCompacted].

      **The constant may not be tightened.**  On 2026-09-20 this was changed
      to [2^63] -- [raftLog.slice] wants [|sents| + |uents| < 2^63] so that
      [extend]'s [need := len(dst) + len(vals)] cannot overflow a Go [int]
      -- and changed back the same day, because [2^63] makes
      [wp_raft__appendEntry] **unprovable**.  The argument is worth keeping,
      since it applies to any tightening:

      [append] grows [uents], so this conjunct has to be *re-established* at
      the longer length.  A bound that the predicate merely *carries* can
      never do that: from [last + 1 < C] one has to conclude
      [last + |ents| + 1 < C], which is false for any [C].  So after an
      append the bound can only be *derived*, from facts that survive the
      append, and there are exactly two:

        - [prev.index + |sents|], which [append] does not touch, is bounded
          by [is_Storage]'s [Hbounded] clause ([inv_storage.v]): [< 2^61].
        - [|uents|] is the length of a Go slice, and Perennial's
          [own_slice_len] gives [< 2^63] for *whatever slice the [append]
          returns* -- this is the only bound on the suffix, and it is a free
          one, re-derived rather than carried.

      Their sum gives [last < 2^61 + 2^63], which clears [2^64] with room
      for a batch of up to [2^61] entries (the premise [appendEntry] takes)
      and does **not** clear [2^63].  A "the log fits in memory" assumption
      below [2^63] would therefore have to be carried, which is exactly what
      cannot be preserved.  If [extend] needs one, it has to come from the
      slice [slice] returns ([hi - lo] at the [slice] call, plus
      [Hbounded]) or from a Perennial-level bound on slice lengths -- not
      from here.  See
      [spec_raft__appendEntry.v], "The no-wrap gap, and how it is closed".
    - [unstable.offset = prev.index + |sents| + 1] -- the unstable suffix
      starts exactly where storage ends.  This is what makes [lastIndex()]
      agree with itself in both of its branches (the [unstable] one and the
      [storage] fallback).
    - **no entry anywhere in the log is a configuration change**:
      [HnoConfChange] is [Forall (λ e, e.(Type') = EntryNormal) (sents ++ uents)].
      That is the conjunct [hasUnappliedConfChanges] needs (with [Happlied] /
      [Hcommitted] below placing [(applied, committed]] inside the log).  It
      holds because **no configuration change is ever requested** -- a scope
      assumption, see below.
    - [prev.index <= committed], [applied <= committed <= prev.index +
      |sents| + |uents|], and [prev.index <= applied] when no snapshot is
      pending: raft compacts only up to [applied] and commits only what it
      has.  A received snapshot moves [prev] and [committed] to its index
      and leaves [applied] below it until the application applies it.
    - **a pending snapshot** ([logstate.snap], since 2026-10-02): when
      [unstable.snapshot] is set, the log starts at the snapshot's id with
      no stable part, and the [Storage] is shadowed ([log_store_ok]).

    *** Scope assumptions written into the predicate

    One, in the same class as [own_raft_phys]'s [checkQuorum = false]: it is
    preserved by everything on the election path, so a predicate may assert
    it, but it does restrict the runs covered.

    1. **No configuration change is ever requested.**  Sanctioned scope.  With
       it, no [EntryConfChange]/[EntryConfChangeV2] is ever appended, so
       [HnoConfChange] is preserved by [append] (the only log write on this
       path is the single empty [EntryNormal] a new leader appends).
    (Until 2026-10-02 there was a second: no snapshot is ever received,
    [unstable.snapshot = nil].  [logstate.snap] replaced it when [MsgSnap]
    came into scope.)

    Note what is **not** assumed: that [term(lastIndex())] succeeds.  That is
    the fact [lastEntryID] needs, and it is *proved* here from the conjuncts
    above plus the [Storage] contract.  Assuming it directly would be the
    [wp_raft__appendEntry] mistake again -- an assumption about raft's
    own code in a place where it can be derived.

    *** Structure

    [own_raftLog l ls] is the one predicate, indexed by [ls : logstate.t]
    (below): the entry list, [committed], [applied] and the pending
    snapshot.
    The entry list is in the index rather than existential inside because
    [raftLog.term] calls [firstIndex] and [lastIndex] on itself, so the
    proof has to re-seal and re-open the predicate mid-function and needs
    the split to come back unchanged.  [own_unstable] is the predicate for
    the embedded [unstable] struct.

    The [Storage] interface contract lives in [inv_storage.v]. *)

Require Export New.proof.go_etcd_io.raft.election_proof.inv_storage.
Require Export New.proof.go_etcd_io.raft.election_proof.inv_logger.

(** Split [l.unstable] out of [l ↦ lv] and get a wand to put it back.  The
    three [unstable.maybe*] specs are stated on a bare [*unstable], so every
    [raftLog] method that consults the suffix needs this first.  Exported
    rather than [Local] because those proofs now live in their own files. *)
Ltac split_unstable l lv :=
  iDestruct (access_strict
               (A := l.[raft.raftLog.t, "unstable"] ↦ lv.(raft.raftLog.unstable'))
               (A' := l.[raft.raftLog.t, "unstable"] ↦ lv.(raft.raftLog.unstable'))
               (P := l ↦ lv) (P' := l ↦ lv)
               with "Hl") as "[Huf Hlback]".

(** [logstate.t], the log's abstract state, is defined in [defs.v]: the
    physical raft state [nstate.t] contains one. *)

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** ** The [unstable] struct

    [own_unstable u uv uents] owns the [unstable] at [u] -- in the
    development always the [unstable] field of a [raftLog] -- at value [uv],
    together with its entry slice, holding [uents].

    **The entries are held read-only** ([↦*□]); only the slice's capacity
    slack is owned outright.  That is what the Go code guarantees
    ([log_unstable.go], upamanyus/etcd-raft 531b20c): no statement ever
    writes an element of [u.entries] in place.  Every assignment to
    [u.entries] re-slices it ([stableTo]), copies it into a new array
    ([shrinkEntriesArray]), adopts the caller's slice, or appends -- in
    place only past [len], into the slack; the truncating case appends to
    [u.slice(...)], which caps its result "so that an append will
    reallocate and copy this slice instead of corrupting the neighbouring
    u.entries" ([log_unstable.go:228-234]).  So a sub-slice [unstable.slice]
    hands out is the caller's for good, with nothing to give back.
    ([wp_slice_append_persistent], in [slice.v], is the [append] this
    needs.)  (Until 2026-09-29 the entries were owned outright and [unstable.slice] *lent*
    a sub-slice, tracked by a [page] argument here; until 2026-09-23 the
    [unstable] specs were stated on the raw [u ↦ uv ∗ uv.entries ↦* uents].) *)
Definition own_unstable (u : loc) (uv : raft.unstable.t)
    (uents : list raftpb.Entry.t) : iProp Σ :=
  "Hu" ∷ u ↦ uv ∗
  "Hents_cap" ∷ own_slice_cap raftpb.Entry.t uv.(raft.unstable.entries') (DfracOwn 1) ∗
  "Hents" ∷ uv.(raft.unstable.entries') ↦*□ uents.

(** ** The log *)

Definition log_indices_ok (prev : raft.entryID.t) (ents : list raftpb.Entry.t) : Prop :=
  ∀ (k : nat) e, ents !! k = Some e →
    (uint.Z e.(raftpb.Entry.Index') = uint.Z prev.(raft.entryID.index') + S k)%Z.

Definition EntryNormal : w32 := W32 0.

(** A [Logger] interface value that is non-nil and satisfies [is_Logger].
    One persistent assertion (rather than [∃ lg, ⌜x = ok lg⌝ ∗ is_Logger lg]
    spread over the predicate) so that [iFrame] re-seals it as a unit: with
    two loggers' [is_Logger]s in context it otherwise picks the wrong one. *)
Definition is_Logger_val (x : interface.t) : iProp Σ :=
  ∃ lg, ⌜ x = interface.ok lg ⌝ ∗ is_Logger lg.
Global Instance is_Logger_val_pers x : Persistent (is_Logger_val x).
Proof. apply _. Qed.

(** Everything [own_raftLog] owns besides the struct itself, at struct value
    [lv] and entry list [prev]/[sents]/[uents].  Not a second predicate for
    the log: nothing is specified on it.  [own_raftLog_unfold] is how a
    proof gets at it.  The unstable entries are held read-only, as in
    [own_unstable] and for the same reason.

    **[sents] is the *visible* stable part** (since 2026-10-01).  The
    [Storage] holds [stored], of which [sents] is a prefix: when
    [unstable.truncateAndAppend] takes its [fromIndex <= u.offset] arm
    (a [MsgApp] that conflicts with an entry already handed to storage), the
    new unstable suffix starts at [fromIndex] and *shadows* the tail of
    [stored] from there on -- Go never deletes it from storage, it is just
    no longer read: every read of the stable part ([term], [slice]) is below
    [unstable.offset].  [Hstored_eq] says the shadowing needs a non-empty
    suffix: with [uents = []], [lastIndex()] falls back to
    [storage.LastIndex()], which is [prev.index + |stored|], so the two
    must agree.

    The two [Logger]s ([l.logger], and [l.unstable.logger], which
    [newLogWithSize] sets to the same value) are carried so that the
    [Infof]s of [findConflict] and [unstable.truncateAndAppend] can be
    stepped. *)
(** ** A pending snapshot (since 2026-10-02)

    [unstable.restore(s)] ([log_unstable.go:188]) stores [&s] in
    [u.snapshot], the address of [restore]'s by-value parameter -- a fresh
    heap cell nothing else points to.  Nothing writes through it until
    [stableSnapTo] clears the field ([MsgStorageAppendResp], out of scope),
    and [raftLog.snapshot()] reads it by value, so the log holds it
    read-only.  [own_snap p snap] says what [p = u.snapshot] is: [nil] for
    [None], and for [Some sid] a pointer to a [Snapshot] whose metadata is
    [sid], with its [ConfState.Voters] slice held read-only too (since
    2026-10-03: [raftLog.snapshot()] returns the snapshot by value, so the
    slice it hands [maybeSendSnapshot] is this one). *)
Local Definition own_snap_def (p : loc) (snap : option raft.entryID.t) : iProp Σ :=
  match snap with
  | None => ⌜ p = null ⌝
  | Some sid =>
      ∃ (sv : raftpb.Snapshot.t), p ↦□ sv ∗
        ⌜ sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.Index')
            = sid.(raft.entryID.index') ∧
          sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.Term')
            = sid.(raft.entryID.term') ⌝ ∗
        ∃ (voters : list w64),
          sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState')
            .(raftpb.ConfState.Voters') ↦*□ voters
  end.
(** Sealed: unfolded, a [None]/[Some] instance reduces to its body, and the
    re-seal lemmas ([own_raftLog_intro]) can then no longer infer [snap]
    from the hypothesis.  [own_snap_None]/[own_snap_Some] open it. *)
Local Definition own_snap_aux : seal (@own_snap_def). Proof. by eexists. Qed.
Definition own_snap := own_snap_aux.(unseal).
Local Definition own_snap_unseal : @own_snap = @own_snap_def := own_snap_aux.(seal_eq).

Lemma own_snap_None p : own_snap p None ⊣⊢ ⌜ p = null ⌝.
Proof. rewrite own_snap_unseal //. Qed.
Lemma own_snap_Some p sid :
  own_snap p (Some sid) ⊣⊢
  ∃ (sv : raftpb.Snapshot.t), p ↦□ sv ∗
    ⌜ sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.Index')
        = sid.(raft.entryID.index') ∧
      sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.Term')
        = sid.(raft.entryID.term') ⌝ ∗
    ∃ (voters : list w64),
      sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState')
        .(raftpb.ConfState.Voters') ↦*□ voters.
Proof. rewrite own_snap_unseal //. Qed.
Global Instance own_snap_pers p snap : Persistent (own_snap p snap).
Proof. rewrite own_snap_unseal. destruct snap; apply _. Qed.

(** How the visible log relates to what [Storage] holds, by whether a
    snapshot is pending.  The storage holds [stored] after [sprev]
    ([own_Storage]).

    - No snapshot: [sprev] is the log's [prev], and [sents] is a prefix of
      [stored] -- all of it when the unstable suffix is empty (see
      [own_raftLog_core]).
    - A pending snapshot [sid]: the log starts at [sid] with no stable part
      ([sents = []]); the storage is **shadowed**.  It still holds its old
      boundary and entries, and nothing reads them while the snapshot is
      pending: [firstIndex]/[lastIndex] answer from the snapshot arms of
      [unstable.maybeFirstIndex]/[maybeLastIndex], [term] answers [i <
      sid.index] with [ErrCompacted] (its [firstIndex] test) and
      [i = sid.index] from [maybeTerm], and [slice]'s range starts at
      [firstIndex = offset], above every stored index it could ask
      [Storage.Entries] for.  [sid.index] is non-zero (the snapshot's index
      is above the commit index it replaced) and below [2^61], the bound
      [is_Storage]'s [Hbounded] gives an unshadowed storage: once the
      snapshot is applied it becomes the storage's boundary, and
      [appendEntry]'s no-wrap argument needs it meanwhile. *)
Definition log_store_ok (snap : option raft.entryID.t) (sprev : raft.entryID.t)
    (stored : list raftpb.Entry.t) (prev : raft.entryID.t)
    (sents uents : list raftpb.Entry.t) : Prop :=
  match snap with
  | None => sprev = prev ∧ sents `prefix_of` stored ∧ (uents = [] → sents = stored)
  | Some sid => prev = sid ∧ sents = [] ∧
               (0 < uint.Z sid.(raft.entryID.index') < 2^61)%Z
  end.

(** The storage's own snapshot [ss] ([own_Storage]'s last index;
    [Storage.Snapshot] returns it, [inv_storage.v]) is of a committed
    prefix of the log (2026-10-03): its index is [0] (no snapshot yet), or
    at or below [committed] with the log having [ss.term] at [ss.index]
    (possibly as its base).  Kept only while no snapshot is pending -- a
    pending one shadows the storage, and [raftLog.snapshot()] then returns
    it instead.

    This is how [maybeSendSnapshot]'s [MsgSnap] gets [snap_ok]'s commit
    bound and log fact ([protocol.v]).  It is raft's invariant, not a
    [Storage] property: true at [newLogWithSize] by its premise on the
    initial storage ([ss] is the boundary, or empty), and preserved because
    the storage never changes in scope, [committed] only grows, and an
    [append] only rewrites entries above [committed]
    ([plog_term_at_truncate_append_below]). *)
Definition stored_snap_ok (ss : raft.entryID.t) (cm : w64) (prev : raft.entryID.t)
    (es : list raftpb.Entry.t) : Prop :=
  uint.Z ss.(raft.entryID.index') = 0 ∨
  (uint.Z ss.(raft.entryID.index') ≤ uint.Z cm ∧
   plog_term_at prev es ss.(raft.entryID.index') = Some ss.(raft.entryID.term')).

Lemma stored_snap_ok_commit ss cm cm' prev es :
  uint.Z cm ≤ uint.Z cm' → stored_snap_ok ss cm prev es → stored_snap_ok ss cm' prev es.
Proof. intros ? [?|[? ?]]; [by left|right; split; [lia|done]]. Qed.

(** An [append] keeps the log's terms below the batch. *)
Lemma plog_term_at_truncate_append_below b es ents e0 (i : w64) t :
  ents !! 0%nat = Some e0 →
  uint.Z i < uint.Z e0.(raftpb.Entry.Index') →
  plog_term_at b es i = Some t →
  plog_term_at b (plog_truncate_append b es ents) i = Some t.
Proof.
  destruct ents as [|e0' ents']; [done|]. intros [= <-] Hlt.
  rewrite /plog_truncate_append /plog_term_at.
  case_decide; [done|]. case_decide; [done|].
  destruct (es !! _) as [e|] eqn:He; [|done]. intros Ht.
  rewrite lookup_app_l.
  - rewrite lookup_take_lt; [|lia]. rewrite He. done.
  - apply lookup_lt_Some in He. rewrite length_take. lia.
Qed.

Definition own_raftLog_core (lv : raft.raftLog.t) (snap : option raft.entryID.t)
                            (prev : raft.entryID.t)
                            (sents uents : list raftpb.Entry.t) : iProp Σ :=
  ∃ (sprev : raft.entryID.t) (stored : list raftpb.Entry.t) (ss : raft.entryID.t),
  "%Hidx" ∷ ⌜ log_indices_ok prev (sents ++ uents) ⌝ ∗
  "%Hnowrap" ∷ ⌜ (uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                  + Z.of_nat (length uents) + 1 < 2^64)%Z ⌝ ∗
  "#HisStorage" ∷ is_Storage lv.(raft.raftLog.storage') ∗
  "HStorage" ∷ own_Storage lv.(raft.raftLog.storage') sprev stored ss ∗
  "%Hstore" ∷ ⌜ log_store_ok snap sprev stored prev sents uents ⌝ ∗
  "#Husnap" ∷ own_snap lv.(raft.raftLog.unstable').(raft.unstable.snapshot') snap ∗
  "%Hoffset" ∷ ⌜ (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                 = uint.Z prev.(raft.entryID.index')
                   + Z.of_nat (length sents) + 1)%Z ⌝ ∗
  "Huents" ∷ lv.(raft.raftLog.unstable').(raft.unstable.entries') ↦*□ uents ∗
  "Huents_cap" ∷ own_slice_cap raftpb.Entry.t
                   lv.(raft.raftLog.unstable').(raft.unstable.entries') (DfracOwn 1) ∗
  "%HnoConfChange" ∷ ⌜ Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal)
                         (sents ++ uents) ⌝ ∗
  "%Happlied" ∷ ⌜ (uint.Z prev.(raft.entryID.index') ≤ uint.Z lv.(raft.raftLog.committed') ∧
                  uint.Z lv.(raft.raftLog.applied') ≤ uint.Z lv.(raft.raftLog.committed'))%Z ⌝ ∗
  "%Hpapplied" ∷ ⌜ snap = None →
                   (uint.Z prev.(raft.entryID.index') ≤ uint.Z lv.(raft.raftLog.applied'))%Z ⌝ ∗
  "%Hcommitted" ∷ ⌜ (uint.Z lv.(raft.raftLog.committed')
                    ≤ uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                      + Z.of_nat (length uents))%Z ⌝ ∗
  "%Hssnap" ∷ ⌜ snap = None →
                stored_snap_ok ss lv.(raft.raftLog.committed') prev (sents ++ uents) ⌝ ∗
  "#Hl_logger" ∷ is_Logger_val lv.(raft.raftLog.logger') ∗
  "#Hu_logger" ∷ is_Logger_val lv.(raft.raftLog.unstable').(raft.unstable.logger').

(** The one predicate for a [raftLog], indexed by its abstract state [ls]
    ([logstate.t], above). *)
Definition own_raftLog (l : loc) (ls : logstate.t) : iProp Σ :=
  ∃ (lv : raft.raftLog.t),
  "Hl" ∷ l ↦ lv ∗
  "%Hcm" ∷ ⌜ lv.(raft.raftLog.committed') = ls.(logstate.committed) ⌝ ∗
  "%Hap" ∷ ⌜ lv.(raft.raftLog.applied') = ls.(logstate.applied) ⌝ ∗
  "Hcore" ∷ own_raftLog_core lv ls.(logstate.snap) ls.(logstate.prev)
              ls.(logstate.sents) ls.(logstate.uents).

(** Open and close [own_raftLog] with the entry list as variables -- the
    form every [raftLog] proof works at after [destruct ls;
    logstate_simpl]. *)
Lemma own_raftLog_unfold l prev sents uents cm ap snap :
  own_raftLog l (logstate.mk prev sents uents cm ap snap) ⊣⊢
  ∃ lv, l ↦ lv ∗ ⌜ lv.(raft.raftLog.committed') = cm ⌝ ∗
        ⌜ lv.(raft.raftLog.applied') = ap ⌝ ∗ own_raftLog_core lv snap prev sents uents.
Proof. rewrite /own_raftLog /=. done. Qed.

(** Re-seal [own_raftLog] from the pieces [iNamed "Hlog"; iNamed "Hcore"]
    names.  **Use this rather than [iFrame "∗#%"]**: with the existential
    [stored] in [own_raftLog_core], [iFrame] spends ~35 s searching
    (measured in [proof_raftLog__lastIndex.v], 2026-10-01).  [st] is the
    storage as the hypotheses mention it -- [lv.storage], or [interface.ok
    isv] after a [rewrite Hstok] -- and the premise [lv.storage = st] is then
    [eq_refl] or [Hstok].  The [reseal_raftLog] tactic below applies it with
    the standard names and closes the pure premises by assumption. *)
Lemma own_raftLog_intro l lv st snap prev sents uents cm ap sprev stored ss :
  lv.(raft.raftLog.storage') = st →
  lv.(raft.raftLog.committed') = cm →
  lv.(raft.raftLog.applied') = ap →
  log_indices_ok prev (sents ++ uents) →
  (uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
   + Z.of_nat (length uents) + 1 < 2^64)%Z →
  log_store_ok snap sprev stored prev sents uents →
  (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
   = uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents) + 1)%Z →
  Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) (sents ++ uents) →
  (uint.Z prev.(raft.entryID.index') ≤ uint.Z lv.(raft.raftLog.committed') ∧
   uint.Z lv.(raft.raftLog.applied') ≤ uint.Z lv.(raft.raftLog.committed'))%Z →
  (snap = None → uint.Z prev.(raft.entryID.index') ≤ uint.Z lv.(raft.raftLog.applied'))%Z →
  (uint.Z lv.(raft.raftLog.committed') ≤ uint.Z prev.(raft.entryID.index')
     + Z.of_nat (length sents) + Z.of_nat (length uents))%Z →
  (snap = None → stored_snap_ok ss lv.(raft.raftLog.committed') prev (sents ++ uents)) →
  l ↦ lv -∗
  is_Storage st -∗
  own_Storage st sprev stored ss -∗
  own_snap lv.(raft.raftLog.unstable').(raft.unstable.snapshot') snap -∗
  lv.(raft.raftLog.unstable').(raft.unstable.entries') ↦*□ uents -∗
  own_slice_cap raftpb.Entry.t lv.(raft.raftLog.unstable').(raft.unstable.entries') (DfracOwn 1) -∗
  is_Logger_val lv.(raft.raftLog.logger') -∗
  is_Logger_val lv.(raft.raftLog.unstable').(raft.unstable.logger') -∗
  own_raftLog l (logstate.mk prev sents uents cm ap snap).
Proof.
  intros <- Hcm Hap ?????????.
  iIntros "Hl #Hst HSt #Hsn Hu Hucap #Hl1 #Hl2".
  iExists lv. iFrame "Hl". iSplit; [done|]. iSplit; [done|].
  iExists sprev, stored, ss. iFrame "Hst HSt Hsn Hu Hucap Hl1 Hl2". iPureIntro. done.
Qed.

(** The struct, for a field read.  [committed] and [applied]
    are what the state says they are. *)
Lemma own_raftLog_struct l ls :
  own_raftLog l ls -∗
  ∃ lv, l ↦ lv ∗
        ⌜ lv.(raft.raftLog.committed') = ls.(logstate.committed) ∧
          lv.(raft.raftLog.applied') = ls.(logstate.applied) ⌝ ∗
        (l ↦ lv -∗ own_raftLog l ls).
Proof.
  iIntros "H". iNamed "H". iExists lv. iFrame "Hl". iSplitR; first done.
  iIntros "Hl". iExists lv. iFrame "Hl Hcore". done.
Qed.

(** [Hnowrap], read out without consuming the log.  Needed to know
    [lastIndex() + 1] does not wrap, which is what makes the range premises
    of [raftLog.slice] and [raftLog.mustCheckOutOfBounds] hold. *)
Lemma own_raftLog_nowrap l ls :
  own_raftLog l ls -∗
  ⌜ (uint.Z ls.(logstate.prev).(raft.entryID.index')
     + Z.of_nat (length ls.(logstate.sents))
     + Z.of_nat (length ls.(logstate.uents)) + 1 < 2^64)%Z ⌝ ∗
  own_raftLog l ls.
Proof.
  iIntros "H". iNamed "H". iNamed "Hcore".
  iSplitR; first done. iExists lv. iFrame "∗#%".
Qed.

(** [Hidx] and the commit bounds, read out without consuming the log. *)
Lemma own_raftLog_wf l ls :
  own_raftLog l ls -∗
  ⌜ log_indices_ok ls.(logstate.prev) (ls.(logstate.sents) ++ ls.(logstate.uents)) ⌝ ∗
  own_raftLog l ls.
Proof.
  iIntros "H". iNamed "H". iNamed "Hcore".
  iSplitR; first done. iExists lv. iFrame "∗#%".
Qed.

Lemma own_raftLog_committed l ls :
  own_raftLog l ls -∗
  ⌜ (uint.Z ls.(logstate.prev).(raft.entryID.index') ≤ uint.Z ls.(logstate.committed) ∧
     uint.Z ls.(logstate.applied) ≤ uint.Z ls.(logstate.committed)
     ≤ uint.Z ls.(logstate.prev).(raft.entryID.index')
       + Z.of_nat (length ls.(logstate.sents))
       + Z.of_nat (length ls.(logstate.uents)))%Z ∧
    (ls.(logstate.snap) = None →
     uint.Z ls.(logstate.prev).(raft.entryID.index') ≤ uint.Z ls.(logstate.applied))%Z ⌝ ∗
  own_raftLog l ls.
Proof.
  iIntros "H". iNamed "H". iNamed "Hcore".
  iSplitR.
  { iPureIntro. rewrite -Hcm -Hap. split; [lia|]. intros Hs. specialize (Hpapplied Hs). lia. }
  iExists lv. iFrame "∗#%".
Qed.

(** The pending snapshot's facts ([log_store_ok]), read out without
    consuming the log: with a snapshot pending, the log starts at it with no
    stable part.  [appendEntry] and [raftLog.restore]'s callers need the
    index bound. *)
Lemma own_raftLog_snap l ls sid :
  ls.(logstate.snap) = Some sid →
  own_raftLog l ls -∗
  ⌜ ls.(logstate.prev) = sid ∧ ls.(logstate.sents) = [] ∧
    (0 < uint.Z sid.(raft.entryID.index') < 2^61)%Z ⌝ ∗
  own_raftLog l ls.
Proof.
  iIntros (Hs) "H". iNamed "H". iNamed "Hcore".
  pose proof Hstore as Hst'. rewrite Hs in Hst'.
  iSplitR; first (iPureIntro; exact Hst').
  iExists lv. iFrame "∗#%".
Qed.

Lemma own_raftLog_no_confchange l ls :
  own_raftLog l ls -∗
  ⌜ Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal)
      (ls.(logstate.sents) ++ ls.(logstate.uents)) ⌝ ∗
  own_raftLog l ls.
Proof.
  iIntros "H". iNamed "H". iNamed "Hcore".
  iSplitR; first done. iExists lv. iFrame "∗#%".
Qed.

(** An entry [Storage.Entries] hands back for a range ending at or below
    [unstable.offset] is an entry of the *visible* stable part [sents]
    ([is_Storage]'s [HEntries] bounds it by [hi]; [Hstored] makes the
    prefix below [hi] a prefix of [sents]). *)
Lemma stored_take_visible (prev : raft.entryID.t) (sents stored : list raftpb.Entry.t)
    (hi : w64) e :
  sents `prefix_of` stored →
  (uint.Z hi ≤ uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents) + 1)%Z →
  e ∈ take (Z.to_nat (uint.Z hi - uint.Z prev.(raft.entryID.index') - 1)) stored →
  e ∈ sents.
Proof.
  intros [k ->] Hhi He. rewrite take_app_le in He; [|lia].
  rewrite -(take_drop (Z.to_nat (uint.Z hi - uint.Z prev.(raft.entryID.index') - 1)) sents).
  apply elem_of_app. by left.
Qed.

(** ** Appending with truncation ([raftLog.append])

    [log_truncate_append ls ents] is the log state [raftLog.append(ents)]
    leaves: everything below [ents[0].Index] is kept, then [ents].  When
    the batch starts inside the stable part ([unstable.truncateAndAppend]'s
    [fromIndex <= u.offset] arm) the *visible* stable part [sents] shrinks
    to the entries below it and [ents] becomes the whole unstable suffix;
    the storage keeps the shadowed tail ([own_raftLog_core]'s [stored]).
    Otherwise [sents] is unchanged and the unstable suffix is cut at
    [ents[0].Index] and extended.  [spec_raftLog__append.v] relates it to
    [plog_truncate_append]. *)
Definition log_truncate_append (ls : logstate.t) (ents : list raftpb.Entry.t) : logstate.t :=
  match ents with
  | [] => ls
  | e0 :: _ =>
      ls <| logstate.sents :=
              take (Z.to_nat (uint.Z e0.(raftpb.Entry.Index')
                              - uint.Z ls.(logstate.prev).(raft.entryID.index') - 1))
                ls.(logstate.sents) |>
         <| logstate.uents :=
              take (Z.to_nat (uint.Z e0.(raftpb.Entry.Index')
                              - uint.Z ls.(logstate.prev).(raft.entryID.index') - 1
                              - Z.of_nat (length ls.(logstate.sents))))
                ls.(logstate.uents) ++ ents |>
  end.

(** Whether [unstable.truncateAndAppend] takes its replace arm and adopts
    the caller's slice as [u.entries]: the batch starts at or below
    [u.offset] and does not simply continue the suffix (with an empty
    suffix and [ents[0].Index = u.offset] the first arm, [append], wins). *)
Definition log_adopts (ls : logstate.t) (ents : list raftpb.Entry.t) : bool :=
  match ents with
  | [] => false
  | e0 :: _ =>
      bool_decide (uint.Z e0.(raftpb.Entry.Index')
                     ≤ uint.Z ls.(logstate.prev).(raft.entryID.index')
                       + Z.of_nat (length ls.(logstate.sents)) + 1 ∧
                   uint.Z e0.(raftpb.Entry.Index')
                     ≠ uint.Z ls.(logstate.prev).(raft.entryID.index')
                       + Z.of_nat (length ls.(logstate.sents))
                       + Z.of_nat (length ls.(logstate.uents)) + 1)%Z
  end.

(** A batch that continues the log is a plain [log_append]. *)
Lemma log_truncate_append_cont ls ents :
  (∀ e0, ents !! 0%nat = Some e0 →
     uint.Z e0.(raftpb.Entry.Index') = uint.Z ls.(logstate.prev).(raft.entryID.index')
       + Z.of_nat (length ls.(logstate.sents)) + Z.of_nat (length ls.(logstate.uents)) + 1)%Z →
  log_truncate_append ls ents = log_append ls ents ∧ log_adopts ls ents = false.
Proof.
  destruct ls as [prev sents uents cm ap]. rewrite /log_append /=.
  destruct ents as [|e0 ents']; intros H.
  - rewrite app_nil_r. split; done.
  - specialize (H e0 eq_refl). simpl in H. rewrite /log_truncate_append /log_adopts /=.
    split.
    + rewrite take_ge; [|lia]. rewrite take_ge; [|lia]. done.
    + apply bool_decide_eq_false_2. lia.
Qed.

(** Read a slice's length as a [Z], without consuming the slice. *)
Lemma slice_len_Z (s : slice.t) (vs : list raftpb.Entry.t) dq :
  s ↦*{dq} vs -∗ ⌜ (Z.of_nat (length vs) = sint.Z s.(slice.len))%Z ⌝.
Proof.
  iIntros "H". iDestruct (own_slice_len with "H") as %[H1 H2].
  iPureIntro. rewrite H1. word.
Qed.

(** ** Reading the log through [scan]

    [raftLog.scan lo hi pageSize v] pages through [[lo, hi)] and hands each
    page to the callback [v] as a slice of the log's entries, read-only (a
    sub-slice of [unstable.entries], or one the [Storage] handed out, or a
    fresh concatenation).  [scan_closure f I P] is what [wp_raftLog__scan]
    asks of the callback: given any such page whose entries all satisfy
    [P], with the caller's invariant [I], it returns a [nil] error and
    hands [I] back.
    Same shape as [visit_closure] ([inv_tracker.v]).

    [P] is how the caller gets a fact about the log's entries into the
    callback: [scan]'s spec takes [Forall P (sents ++ uents)] as a premise
    and every page is a sub-list of the log.  [hasUnappliedConfChanges] uses
    [P := λ e, e.(Type') = EntryNormal], from [HnoConfChange].

    The callback's own [return err] paths -- [errBreak] in
    [hasUnappliedConfChanges] -- are not modelled: the closure has to return
    [nil], which is exactly what makes [scan] return [nil]. *)
Definition scan_closure (f : func.t) (I : iProp Σ) (P : raftpb.Entry.t → Prop) : iProp Σ :=
  ∀ (s : slice.t) (es : list raftpb.Entry.t) (dq : dfrac),
    {{{ s ↦*{dq} es ∗ ⌜ Forall P es ⌝ ∗ I }}}
      #f #s
    {{{ RET #interface.nil; s ↦*{dq} es ∗ I }}}.

Lemma Forall_sublist_of {A} (P : A → Prop) (l es : list A) :
  Forall P l → (∀ e, e ∈ es → e ∈ l) → Forall P es.
Proof.
  intros Hl Hin. rewrite List.Forall_forall in Hl. rewrite List.Forall_forall.
  intros e He. apply Hl, list_elem_of_In, Hin, list_elem_of_In, He.
Qed.

(** Two slice values with the same pointer and length own the same
    elements.  [unstable.slice] and [raftLog.slice] return three-index
    slices ([s[lo:hi:hi]]) whose capacity differs from the [slice.slice]
    form the ownership lemmas ([own_slice_slice]) speak about; this moves the
    points-to across.  Needs a non-empty list, because for an empty one
    [own_slice] may hold through its [slice.nil] disjunct, which fixes the
    capacity too. *)
Lemma own_slice_same_ptr_len {V} `{!ZeroVal V} `{!TypedPointsto V}
    (s1 s2 : slice.t) (dq : dfrac) (vs : list V) :
  vs ≠ [] →
  s1.(slice.ptr) = s2.(slice.ptr) →
  s1.(slice.len) = s2.(slice.len) →
  (sint.Z s2.(slice.len) ≤ sint.Z s2.(slice.cap))%Z →
  s1 ↦*{dq} vs -∗ s2 ↦*{dq} vs.
Proof.
  intros Hne Hptr Hlen Hcap.
  destruct s1 as [p1 l1 c1], s2 as [p2 l2 c2]; simpl in *; subst.
  rewrite own_slice_unseal /own_slice_def /=.
  iIntros "[%H | [H %]]".
  { destruct H as [_ ->]. done. }
  iRight. iFrame. done.
Qed.


(** Split the [unstable] field out of [l ↦ lv], keeping a wand that accepts
    *any* new value for it.  [split_unstable] (above) is not enough for a
    call that installs a new [unstable] value -- [truncateAndAppend]'s new
    [entries], [unstable.restore] -- since the new value is introduced by
    that call's own postcondition, after the [AccessStrict] store
    instance's evar was created (notes/gotchas.md, "The [AccessStrict]
    store instance cannot take a value the call has not produced yet").
    Moved here from [proof_raftLog__append.v] on 2026-10-02 for
    [raftLog.restore]. *)
Lemma raftLog_split_unstable (l : loc) (lv : raft.raftLog.t) :
  l ↦ lv -∗
  l.[raft.raftLog.t, "unstable"] ↦ lv.(raft.raftLog.unstable') ∗
  (∀ uv, l.[raft.raftLog.t, "unstable"] ↦ uv -∗
         l ↦ (lv <| raft.raftLog.unstable' := uv |>)).
Proof.
  iIntros "Hl".
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=) in "Hl".
  iDestruct "Hl" as "[Hf %Hnn]". iNamed "Hf".
  iFrame "unstable".
  iIntros (uv) "Huv".
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=).
  iFrame "∗%".
Qed.

End proof.

(** Re-seal [own_raftLog l (logstate.mk …)] from the hypotheses
    [iNamed "Hlog"; iNamed "Hcore"] introduced ([own_raftLog_intro]). *)
Ltac reseal_raftLog :=
  iApply (own_raftLog_intro with
           "Hl HisStorage HStorage Husnap Huents Huents_cap Hl_logger Hu_logger");
  try done.
