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

    [own_raftLog_at l prev sents uents] is the workhorse; [own_raftLog l]
    existentially quantifies the three.  The split is a parameter rather than
    an existential inside because [raftLog.term] calls [firstIndex] and
    [lastIndex] on itself, so the proof has to re-seal and re-open the
    predicate mid-function and needs the split to come back unchanged.

    The [Storage] interface contract lives in [inv_storage.v]. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_storage.

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

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Definition log_indices_ok (prev : raft.entryID.t) (ents : list raftpb.Entry.t) : Prop :=
  ∀ (k : nat) e, ents !! k = Some e →
    (uint.Z e.(raftpb.Entry.Index') = uint.Z prev.(raft.entryID.index') + S k)%Z.

Definition EntryNormal : w32 := W32 0.

Definition own_raftLog_at (l : loc) (prev : raft.entryID.t)
                          (sents uents : list raftpb.Entry.t) : iProp Σ :=
  ∃ (lv : raft.raftLog.t),
  "Hl" ∷ l ↦ lv ∗
  "%Hidx" ∷ ⌜ log_indices_ok prev (sents ++ uents) ⌝ ∗
  "%Hnowrap" ∷ ⌜ (uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                  + Z.of_nat (length uents) + 1 < 2^64)%Z ⌝ ∗
  "#HisStorage" ∷ is_Storage lv.(raft.raftLog.storage') ∗
  "HStorage" ∷ own_Storage lv.(raft.raftLog.storage') prev sents ∗
  "%Hoffset" ∷ ⌜ (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                 = uint.Z prev.(raft.entryID.index')
                   + Z.of_nat (length sents) + 1)%Z ⌝ ∗
  "Huents" ∷ lv.(raft.raftLog.unstable').(raft.unstable.entries') ↦* uents ∗
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

Definition own_raftLog (l : loc) : iProp Σ :=
  ∃ prev sents uents, own_raftLog_at l prev sents uents.

(** Open [own_raftLog] at some split and get a wand to close it again.  A
    caller that holds only the existential form -- which is what
    [own_raft_phys] carries -- needs this to use any of the indexed
    ([_at]) log specs, since those are stated at a fixed split.  Same shape as
    [own_raft_misc_option] in [inv_misc.v]. *)
Lemma own_raftLog_acc l :
  own_raftLog l -∗
  ∃ prev sents uents,
    own_raftLog_at l prev sents uents ∗
    (own_raftLog_at l prev sents uents -∗ own_raftLog l).
Proof.
  iIntros "H". iDestruct "H" as (prev sents uents) "H".
  iExists prev, sents, uents. iFrame "H".
  iIntros "H". iExists prev, sents, uents. iFrame "H".
Qed.

Lemma own_raftLog_at_no_confchange l prev sents uents :
  own_raftLog_at l prev sents uents -∗
  ⌜ Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) (sents ++ uents) ⌝ ∗
  own_raftLog_at l prev sents uents.
Proof.
  iIntros "H". iDestruct "H" as (lv) "H". iNamed "H".
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
    page to the callback [v] as a slice *lent* out of the log (a sub-slice of
    [unstable.entries], or one the [Storage] lent, or a fresh concatenation).
    [scan_closure f I P] is what [wp_raftLog__scan_at] asks of the callback:
    given any lent page whose entries all satisfy [P], with the caller's
    invariant [I], it returns a [nil] error and hands the page and [I] back.
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
