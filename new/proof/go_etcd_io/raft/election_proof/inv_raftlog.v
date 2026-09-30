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
    - [prev.index <= applied <= committed <= prev.index + |sents| + |uents|]:
      raft compacts only up to [applied] and commits only what it has.
    - **[unstable.snapshot = nil]**: no snapshot is ever received or taken --
      a scope assumption, see below.  This is what makes
      [hasNextOrInProgressSnapshot] return [false], which [promotable] needs.

    *** Scope assumptions written into the predicate

    Two, both in the same class as [own_raft_phys]'s [preVote = false]: they
    are preserved by everything on the election path, so a predicate may
    assert them, but they do restrict the runs covered.

    1. **No configuration change is ever requested.**  Sanctioned scope.  With
       it, no [EntryConfChange]/[EntryConfChangeV2] is ever appended, so
       [HnoConfChange] is preserved by [append] (the only log write on this
       path is the single empty [EntryNormal] a new leader appends).
    2. **No snapshot is ever received or applied.**  [newLog] starts with
       [unstable.snapshot = nil]; only [unstable.restore] (i.e. handling a
       [MsgSnap], or [raft.restore]) sets it, and that is not an election
       message.  Recorded here because it was *not* in the sanctioned list and
       is needed for [hasNextOrInProgressSnapshot].

    Note what is **not** assumed: that [term(lastIndex())] succeeds.  That is
    the fact [lastEntryID] needs, and it is *proved* here from the conjuncts
    above plus the [Storage] contract.  Assuming it directly would be the
    [wp_raft__appendEntry] mistake again -- an assumption about raft's
    own code in a place where it can be derived.

    *** Structure

    [own_raftLog l ls] is the one predicate, indexed by [ls : logstate.t]
    (below): the entry list, [committed] and [applied].
    The entry list is in the index rather than existential inside because
    [raftLog.term] calls [firstIndex] and [lastIndex] on itself, so the
    proof has to re-seal and re-open the predicate mid-function and needs
    the split to come back unchanged.  [own_unstable] is the predicate for
    the embedded [unstable] struct.

    The [Storage] interface contract lives in [inv_storage.v]. *)

Require Export New.proof.go_etcd_io.raft.election_proof.inv_storage.

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

(** Everything [own_raftLog] owns besides the struct itself, at struct value
    [lv] and entry list [prev]/[sents]/[uents].  Not a second predicate for
    the log: nothing is specified on it.  [own_raftLog_unfold] is how a
    proof gets at it.  The unstable entries are held read-only, as in
    [own_unstable] and for the same reason. *)
Definition own_raftLog_core (lv : raft.raftLog.t) (prev : raft.entryID.t)
                            (sents uents : list raftpb.Entry.t) : iProp Σ :=
  "%Hidx" ∷ ⌜ log_indices_ok prev (sents ++ uents) ⌝ ∗
  "%Hnowrap" ∷ ⌜ (uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                  + Z.of_nat (length uents) + 1 < 2^64)%Z ⌝ ∗
  "#HisStorage" ∷ is_Storage lv.(raft.raftLog.storage') ∗
  "HStorage" ∷ own_Storage lv.(raft.raftLog.storage') prev sents ∗
  "%Hoffset" ∷ ⌜ (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                 = uint.Z prev.(raft.entryID.index')
                   + Z.of_nat (length sents) + 1)%Z ⌝ ∗
  "Huents" ∷ lv.(raft.raftLog.unstable').(raft.unstable.entries') ↦*□ uents ∗
  "Huents_cap" ∷ own_slice_cap raftpb.Entry.t
                   lv.(raft.raftLog.unstable').(raft.unstable.entries') (DfracOwn 1) ∗
  "%Hnosnap" ∷ ⌜ lv.(raft.raftLog.unstable').(raft.unstable.snapshot') = null ⌝ ∗
  "%HnoConfChange" ∷ ⌜ Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal)
                         (sents ++ uents) ⌝ ∗
  "%Happlied" ∷ ⌜ (uint.Z prev.(raft.entryID.index') ≤ uint.Z lv.(raft.raftLog.applied')
                  ≤ uint.Z lv.(raft.raftLog.committed'))%Z ⌝ ∗
  "%Hcommitted" ∷ ⌜ (uint.Z lv.(raft.raftLog.committed')
                    ≤ uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                      + Z.of_nat (length uents))%Z ⌝.

(** The one predicate for a [raftLog], indexed by its abstract state [ls]
    ([logstate.t], above). *)
Definition own_raftLog (l : loc) (ls : logstate.t) : iProp Σ :=
  ∃ (lv : raft.raftLog.t),
  "Hl" ∷ l ↦ lv ∗
  "%Hcm" ∷ ⌜ lv.(raft.raftLog.committed') = ls.(logstate.committed) ⌝ ∗
  "%Hap" ∷ ⌜ lv.(raft.raftLog.applied') = ls.(logstate.applied) ⌝ ∗
  "Hcore" ∷ own_raftLog_core lv ls.(logstate.prev)
              ls.(logstate.sents) ls.(logstate.uents).

(** Open and close [own_raftLog] with the entry list as variables -- the
    form every [raftLog] proof works at after [destruct ls;
    logstate_simpl]. *)
Lemma own_raftLog_unfold l prev sents uents cm ap :
  own_raftLog l (logstate.mk prev sents uents cm ap) ⊣⊢
  ∃ lv, l ↦ lv ∗ ⌜ lv.(raft.raftLog.committed') = cm ⌝ ∗
        ⌜ lv.(raft.raftLog.applied') = ap ⌝ ∗ own_raftLog_core lv prev sents uents.
Proof. rewrite /own_raftLog /=. done. Qed.

(** Re-sealing a log a proof has taken apart, as one [iApply] with named
    hypotheses and pure side goals:

      iApply (own_raftLog_intro with "Hl HisStorage HStorage Huents Huents_cap"); done.

    Unfolding and closing it with [iFrame "∗#%"] instead cost 20-70s per use
    (2026-09-30 measurement; notes/gotchas.md) -- the same reason
    [own_raft_phys_intro] exists.  The pure premises are in the order the
    conjuncts appear in [own_raftLog_core].  [l ↦ lv] comes first so that it
    fixes [lv].  The storage is a separate [st] because a proof that has done
    [rewrite Hstok] holds [HisStorage] and [HStorage] at [interface.ok _]
    rather than at [lv.(storage')]; the first premise is then [Hstok]. *)
Lemma own_raftLog_intro l prev sents uents cm ap (lv : raft.raftLog.t) st :
  lv.(raft.raftLog.storage') = st →
  lv.(raft.raftLog.committed') = cm →
  lv.(raft.raftLog.applied') = ap →
  log_indices_ok prev (sents ++ uents) →
  (uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
   + Z.of_nat (length uents) + 1 < 2^64)%Z →
  (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
   = uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents) + 1)%Z →
  lv.(raft.raftLog.unstable').(raft.unstable.snapshot') = null →
  Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) (sents ++ uents) →
  (uint.Z prev.(raft.entryID.index') ≤ uint.Z lv.(raft.raftLog.applied')
   ≤ uint.Z lv.(raft.raftLog.committed'))%Z →
  (uint.Z lv.(raft.raftLog.committed')
   ≤ uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
     + Z.of_nat (length uents))%Z →
  l ↦ lv -∗
  is_Storage st -∗
  own_Storage st prev sents -∗
  lv.(raft.raftLog.unstable').(raft.unstable.entries') ↦*□ uents -∗
  own_slice_cap raftpb.Entry.t lv.(raft.raftLog.unstable').(raft.unstable.entries')
    (DfracOwn 1) -∗
  own_raftLog l (logstate.mk prev sents uents cm ap).
Proof.
  intros <- Hcm Hap Hidx Hnowrap Hoffset Hnosnap HnoConfChange Happlied Hcommitted.
  iIntros "Hl #HisStorage HStorage #Huents Huents_cap".
  iApply own_raftLog_unfold. iExists lv. iFrame "Hl HisStorage HStorage Huents Huents_cap".
  iPureIntro. repeat split; first [done | lia].
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

Lemma own_raftLog_no_confchange l ls :
  own_raftLog l ls -∗
  ⌜ Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal)
      (ls.(logstate.sents) ++ ls.(logstate.uents)) ⌝ ∗
  own_raftLog l ls.
Proof.
  iIntros "H". iNamed "H". iNamed "Hcore".
  iSplitR; first done. iExists lv. iFrame "∗#%".
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


End proof.
