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
    [wp_raft__appendEmptyEntry] mistake again -- an assumption about raft's
    own code in a place where it can be derived.

    *** Structure

    [own_raftLog_at l prev sents uents] is the workhorse; [own_raftLog l]
    existentially quantifies the three.  The split is a parameter rather than
    an existential inside because [raftLog.term] calls [firstIndex] and
    [lastIndex] on itself, so the proof has to re-seal and re-open the
    predicate mid-function and needs the split to come back unchanged.

    The [Storage] interface contract lives in [inv_storage.v]. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_storage.

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

(** ** The [unstable] suffix

    Three [maybe*] methods, all on a bare [*unstable] so they can be reused
    wherever the field is split out.  Each takes [snapshot = nil] as a
    premise -- with a snapshot present all three have an extra branch, and
    none of them is reachable under our scope. *)

Lemma wp_unstable__maybeFirstIndex (u : loc) (uv : raft.unstable.t) :
  uv.(raft.unstable.snapshot') = null →
  {{{ is_pkg_init raft ∗ u ↦ uv }}}
    u @! (go.PointerType raft.unstable) @! "maybeFirstIndex" #()
  {{{ (i : w64), RET (#i, #false); u ↦ uv }}}.
Proof.
  intros Hns. wp_start as "Hu". wp_auto.
  rewrite Hns bool_decide_eq_true_2 //=. wp_auto.
  iApply "HΦ". iFrame.
Qed.

Lemma wp_unstable__maybeLastIndex (u : loc) (uv : raft.unstable.t)
      (uents : list raftpb.Entry.t) :
  uv.(raft.unstable.snapshot') = null →
  (uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents) < 2^64)%Z →
  {{{ is_pkg_init raft ∗ "Hu" ∷ u ↦ uv ∗
      "Hents" ∷ uv.(raft.unstable.entries') ↦* uents }}}
    u @! (go.PointerType raft.unstable) @! "maybeLastIndex" #()
  {{{ (i : w64) (ok : bool), RET (#i, #ok);
      u ↦ uv ∗ uv.(raft.unstable.entries') ↦* uents ∗
      ⌜ uents = [] → ok = false ⌝ ∗
      ⌜ uents ≠ [] → ok = true ∧
        (uint.Z i = uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents) - 1)%Z ⌝ }}}.
Proof.
  intros Hns Hnw. wp_start as "H". iNamed "H". wp_auto.
  iDestruct (slice_len_Z with "Hents") as %Hlen.
  assert (bool_decide (uv.(raft.unstable.snapshot') = null) = true) as Hbsnap
    by (apply bool_decide_eq_true_2; done).
  destruct (decide (uents = [])) as [He|Hne].
  - rewrite He in Hlen. simpl in Hlen.
    assert (uv.(raft.unstable.entries').(slice.len) = W64 0) as Hz by word.
    assert (bool_decide (uv.(raft.unstable.entries').(slice.len) = W64 0) = true)
      as Hb1 by (apply bool_decide_eq_true_2; exact Hz).
    rewrite Hb1 /=. wp_auto.
    rewrite Hbsnap /=. wp_auto.
    iApply ("HΦ" $! (W64 0) false). iFrame. iPureIntro.
    split; [done | intros Hc; exfalso; apply Hc; exact He].
  - assert (uv.(raft.unstable.entries').(slice.len) ≠ W64 0) as Hz.
    { destruct uents as [|x xs]; [done|]. intros Hc. rewrite Hc in Hlen.
      simpl in Hlen. word. }
    assert (bool_decide (uv.(raft.unstable.entries').(slice.len) = W64 0) = false)
      as Hb1 by (apply bool_decide_eq_false_2; exact Hz).
    rewrite Hb1 /=. wp_auto.
    iApply ("HΦ" $! _ true). iFrame. iPureIntro.
    split; [intros Hc; exfalso; apply Hne; exact Hc | intros _; split; [done|word]].
Qed.

Lemma wp_unstable__maybeTerm (u : loc) (uv : raft.unstable.t)
      (uents : list raftpb.Entry.t) (i : w64) :
  uv.(raft.unstable.snapshot') = null →
  (uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents) < 2^64)%Z →
  {{{ is_pkg_init raft ∗ "Hu" ∷ u ↦ uv ∗
      "Hents" ∷ uv.(raft.unstable.entries') ↦* uents }}}
    u @! (go.PointerType raft.unstable) @! "maybeTerm" #i
  {{{ (t : w64) (ok : bool), RET (#t, #ok);
      u ↦ uv ∗ uv.(raft.unstable.entries') ↦* uents ∗
      ⌜ ok = true ↔ (uint.Z uv.(raft.unstable.offset') ≤ uint.Z i <
                     uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents))%Z ⌝ }}}.
Proof.
  intros Hns Hnw. wp_start as "H". iNamed "H". wp_auto.
  iDestruct (own_slice_len with "Hents") as %[Hlen Hlen2].
  assert (bool_decide (uv.(raft.unstable.snapshot') = null) = true) as Hbsnap
    by (apply bool_decide_eq_true_2; done).
  destruct (decide (uint.Z i < uint.Z uv.(raft.unstable.offset'))%Z) as [Hlt|Hge].
  - assert (bool_decide (uint.Z i < uint.Z uv.(raft.unstable.offset'))%Z = true)
      as Hb1 by (apply bool_decide_eq_true_2; done).
    rewrite Hb1 /=. wp_auto.
    rewrite Hbsnap /=. wp_auto.
    iApply ("HΦ" $! (W64 0) false). iFrame. iPureIntro.
    split; [done | lia].
  - assert (bool_decide (uint.Z i < uint.Z uv.(raft.unstable.offset'))%Z = false)
      as Hb1 by (apply bool_decide_eq_false_2; done).
    rewrite Hb1 /=. wp_auto.
    wp_apply (wp_unstable__maybeLastIndex _ _ _ Hns Hnw with "[$Hu $Hents]")
      as "%last %ok (Hu & Hents & %Hok1 & %Hok2)".
    destruct (decide (uents = [])) as [He|Hne].
    + rewrite (Hok1 He) /=. wp_auto.
      iApply ("HΦ" $! (W64 0) false). iFrame. iPureIntro.
      rewrite He /=. split; [done | lia].
    + destruct (Hok2 Hne) as [Hokt Hlast]. rewrite Hokt /=. wp_auto.
      destruct (decide (uint.Z last < uint.Z i)%Z) as [Hgt|Hle].
      * assert (bool_decide (uint.Z last < uint.Z i)%Z = true) as Hb2
          by (apply bool_decide_eq_true_2; exact Hgt).
        rewrite Hb2 /=. wp_auto.
        iApply ("HΦ" $! (W64 0) false). iFrame. iPureIntro.
        split; [done | lia].
      * assert (bool_decide (uint.Z last < uint.Z i)%Z = false) as Hb2
          by (apply bool_decide_eq_false_2; exact Hle).
        rewrite Hb2 /=. wp_auto.
        assert (0 ≤ sint.Z (word.sub i uv.(raft.unstable.offset')) <
                sint.Z uv.(raft.unstable.entries').(slice.len))%Z as Hbnd by word.
        rewrite decide_True //.
        destruct (uents !! Z.to_nat (sint.Z (word.sub i uv.(raft.unstable.offset'))))
          as [e|] eqn:He_lk; last first.
        { exfalso. apply lookup_ge_None_1 in He_lk. word. }
        iDestruct (own_slice_elem_acc
                     (sint.Z (word.sub i uv.(raft.unstable.offset')))
                     with "Hents") as "[He Hback]"; [word | exact He_lk | ].
        wp_auto.
        iDestruct ("Hback" with "He") as "Hents".
        rewrite (list_insert_id _ _ _ He_lk).
        iApply ("HΦ" $! e.(raftpb.Entry.Term') true). iFrame. iPureIntro.
        split; [intros _; lia | done].
Qed.

(** ** The [raftLog] methods that can fail

    [firstIndex], [lastIndex] and [term] each end in a [panic]/[Panicf] on an
    error from [Storage].  [wp_Logger__logf] deliberately does not cover the
    panicking methods, so these proofs have to *reach* the [Storage] call with
    its precondition satisfied -- that is the whole content of these three
    lemmas, and why they pin the returned error to [interface.nil]. *)

Local Ltac split_unstable l lv :=
  iDestruct (access_strict
               (A := l.[raft.raftLog.t, "unstable"] ↦ lv.(raft.raftLog.unstable'))
               (A' := l.[raft.raftLog.t, "unstable"] ↦ lv.(raft.raftLog.unstable'))
               (P := l ↦ lv) (P' := l ↦ lv)
               with "Hl") as "[Huf Hlback]".

Lemma wp_raftLog__firstIndex_at (l : loc) prev sents uents :
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog_at l prev sents uents }}}
    l @! (go.PointerType raft.raftLog) @! "firstIndex" #()
  {{{ (i : w64), RET #i;
      own_raftLog_at l prev sents uents ∗
      ⌜ (uint.Z i = uint.Z prev.(raft.entryID.index') + 1)%Z ⌝ }}}.
Proof.
  wp_start as "H". iNamed "H". iNamed "Hlog". wp_auto.
  iAssert (is_Storage lv.(raft.raftLog.storage')) as "#Hsto".
  { iExact "HisStorage". }
  iDestruct "Hsto" as (isv) "(%Hstok & #HLI & #HFI & #HT)".
  split_unstable l lv.
  wp_apply (wp_unstable__maybeFirstIndex _ _ Hnosnap with "[$Huf]") as "%fi Huf".
  iDestruct ("Hlback" with "Huf") as "Hl".
  wp_auto. rewrite Hstok /=.
  wp_apply ("HFI" with "HStorage") as "%fi2 [%Hfi HStorage]".
  iApply ("HΦ" $! fi2).
  iSplitL "Hl HStorage Huents Huents_cap".
  { rewrite /own_raftLog_at. iExists lv. rewrite Hstok.
    iFrame "∗#%". all: (iPureIntro; done). }
  iPureIntro. word.
Qed.

Lemma wp_raftLog__lastIndex_at (l : loc) prev sents uents :
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog_at l prev sents uents }}}
    l @! (go.PointerType raft.raftLog) @! "lastIndex" #()
  {{{ (i : w64), RET #i;
      own_raftLog_at l prev sents uents ∗
      ⌜ (uint.Z i = uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                    + Z.of_nat (length uents))%Z ⌝ }}}.
Proof.
  wp_start as "H". iNamed "H". iNamed "Hlog". wp_auto.
  assert (Hnw : (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset') +
                 Z.of_nat (length uents) < 2^64)%Z) by lia.
  iAssert (is_Storage lv.(raft.raftLog.storage')) as "#Hsto".
  { iExact "HisStorage". }
  iDestruct "Hsto" as (isv) "(%Hstok & #HLI & #HFI & #HT)".
  split_unstable l lv.
  wp_apply (wp_unstable__maybeLastIndex _ _ _ Hnosnap Hnw with "[$Huf $Huents]")
    as "%li %ok (Huf & Huents & %Hok1 & %Hok2)".
  iDestruct ("Hlback" with "Huf") as "Hl".
  destruct (decide (uents = [])) as [He|Hne].
  - rewrite (Hok1 He) /=. wp_auto. rewrite Hstok /=.
    wp_apply ("HLI" with "HStorage") as "%li2 [%Hli HStorage]".
    iApply ("HΦ" $! li2).
    iSplitL "Hl HStorage Huents Huents_cap".
    { rewrite /own_raftLog_at. iExists lv. rewrite Hstok.
      iFrame "∗#%". all: (iPureIntro; done). }
    iPureIntro. rewrite He /=. lia.
  - destruct (Hok2 Hne) as [Hokt Hli]. rewrite Hokt /=. wp_auto.
    iApply ("HΦ" $! li).
    iSplitL "Hl HStorage Huents Huents_cap".
    { rewrite /own_raftLog_at. iExists lv. rewrite Hstok.
      iFrame "∗#%". all: (iPureIntro; done). }
    iPureIntro. lia.
Qed.

Lemma wp_raftLog__term_at (l : loc) prev sents uents (i : w64) :
  (uint.Z prev.(raft.entryID.index') ≤ uint.Z i ≤
   uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
   + Z.of_nat (length uents))%Z →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog_at l prev sents uents }}}
    l @! (go.PointerType raft.raftLog) @! "term" #i
  {{{ (t : w64), RET (#t, #interface.nil);
      own_raftLog_at l prev sents uents }}}.
Proof.
  intros Hi. wp_start as "H". iNamed "H". iNamed "Hlog". wp_auto.
  assert (Hnw : (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset') +
                 Z.of_nat (length uents) < 2^64)%Z) by lia.
  iAssert (is_Storage lv.(raft.raftLog.storage')) as "#Hsto".
  { iExact "HisStorage". }
  iDestruct "Hsto" as (isv) "(%Hstok & #HLI & #HFI & #HT)".
  split_unstable l lv.
  wp_apply (wp_unstable__maybeTerm _ _ _ _ Hnosnap Hnw with "[$Huf $Huents]")
    as "%t %ok (Huf & Huents & %Hok)".
  iDestruct ("Hlback" with "Huf") as "Hl".
  destruct ok.
  - wp_auto.
    iApply ("HΦ" $! t). rewrite /own_raftLog_at. iExists lv. rewrite Hstok.
    iFrame "∗#%". all: (iPureIntro; done).
  - assert (Hnotin : ¬ (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                        ≤ uint.Z i <
                        uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                        + Z.of_nat (length uents))%Z).
    { intros Hc. apply Hok in Hc. done. }
    assert (Hile : (uint.Z i ≤ uint.Z prev.(raft.entryID.index')
                    + Z.of_nat (length sents))%Z) by lia.
    wp_auto.
    iAssert (own_raftLog_at l prev sents uents)
      with "[Hl HStorage Huents Huents_cap]" as "Hlog".
    { rewrite /own_raftLog_at. iExists lv. rewrite Hstok.
      iFrame "∗#%". all: (iPureIntro; done). }
    wp_apply (wp_raftLog__firstIndex_at with "[$Hlog]") as "%fi [Hlog %Hfi]".
    assert (Hb1 : bool_decide (uint.Z (word.add i (W64 1)) < uint.Z fi)%Z = false).
    { apply bool_decide_eq_false_2. word. }
    rewrite Hb1 /=. wp_auto.
    wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]") as "%li [Hlog %Hli]".
    assert (Hb2 : bool_decide (uint.Z li < uint.Z i)%Z = false).
    { apply bool_decide_eq_false_2. lia. }
    rewrite Hb2 /=. wp_auto.
    assert (Hrange : (uint.Z prev.(raft.entryID.index') ≤ uint.Z i ≤
                      uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents))%Z)
      by lia.
    clear Hnotin Hnw Hok Hoffset Hnosnap Hstok Happlied Hcommitted
          Hidx Hnowrap HnoConfChange Hb1 Hb2 Hfi Hli Hile.
    iClear "HisStorage HLI HFI HT".
    clear lv isv fi li.
    iNamed "Hlog". wp_auto.
    iAssert (is_Storage lv.(raft.raftLog.storage')) as "#Hsto".
    { iExact "HisStorage". }
    iDestruct "Hsto" as (isv) "(%Hstok & #HLI & #HFI & #HT)".
    rewrite Hstok /=.
    wp_apply ("HT" $! prev sents i with "[$HStorage]").
    { iPureIntro. lia. }
    iIntros (t2) "[%Ht2 HStorage]".
    wp_auto.
    iApply ("HΦ" $! t2). rewrite /own_raftLog_at. iExists lv. rewrite Hstok.
    iFrame "∗#%". all: (iPureIntro; done).
Qed.

(** ** The interface other files use

    These four statements are what [inv_raft_phys.v], [inv_misc.v] and the
    [proof_*.v] files call.  The first three are unchanged from when they were
    [Axiom]s: they say nothing about the value returned, only that the call
    returns and gives the log back.  That is all the election path needs --
    [isUpToDate] returning a wrong answer can only make the node decline to
    vote, which is always protocol-legal. *)

Lemma wp_raftLog__lastEntryID_at (l : loc) prev sents uents :
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog_at l prev sents uents }}}
    l @! (go.PointerType raft.raftLog) @! "lastEntryID" #()
  {{{ (e : raft.entryID.t), RET #e; own_raftLog_at l prev sents uents }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]") as "%li [Hlog %Hli]".
  assert (Hb : (uint.Z prev.(raft.entryID.index') ≤ uint.Z li ≤
                uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                + Z.of_nat (length uents))%Z) by lia.
  wp_apply (wp_raftLog__term_at _ _ _ _ _ Hb with "[$Hlog]") as "%t Hlog".
  iApply ("HΦ" $! (raft.entryID.mk t li)). iFrame.
Qed.

Lemma wp_raftLog__lastIndex (l : loc) :
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    l @! (go.PointerType raft.raftLog) @! "lastIndex" #()
  {{{ (i : w64), RET #i; own_raftLog l }}}.
Proof.
  iIntros (Φ) "[#Hinit Hlog] HΦ".
  iDestruct "Hlog" as (prev sents uents) "Hlog".
  wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]") as "%i [Hlog %]".
  iApply "HΦ". iExists prev, sents, uents. iFrame.
Qed.

Lemma wp_raftLog__lastEntryID (l : loc) :
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    l @! (go.PointerType raft.raftLog) @! "lastEntryID" #()
  {{{ (e : raft.entryID.t), RET #e; own_raftLog l }}}.
Proof.
  iIntros (Φ) "[#Hinit Hlog] HΦ".
  iDestruct "Hlog" as (prev sents uents) "Hlog".
  wp_apply (wp_raftLog__lastEntryID_at with "[$Hlog]") as "%e Hlog".
  iApply "HΦ". iExists prev, sents, uents. iFrame.
Qed.

Lemma wp_raftLog__isUpToDate (l : loc) (e : raft.entryID.t) :
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    l @! (go.PointerType raft.raftLog) @! "isUpToDate" #e
  {{{ (b : bool), RET #b; own_raftLog l }}}.
Proof.
  wp_start as "Hlog". wp_auto.
  wp_apply (wp_raftLog__lastEntryID with "[$Hlog]") as "%our Hlog".
  repeat (case_bool_decide; try wp_auto).
  all: iApply "HΦ"; iFrame.
Qed.

(** Added back 2026-09-16: deleted earlier that day as "reachable from no
    proof", which was only true because [promotable] was an [Axiom].
    [promotable]'s body calls this, and its postcondition
    [b = bool_decide (id ∈ cfg)] is only derivable if this returns [false]. *)
Lemma wp_raftLog__hasNextOrInProgressSnapshot (l : loc) :
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    l @! (go.PointerType raft.raftLog) @! "hasNextOrInProgressSnapshot" #()
  {{{ (b : bool), RET #b; own_raftLog l ∗ ⌜ b = false ⌝ }}}.
Proof.
  wp_start as "Hlog". iDestruct "Hlog" as (prev sents uents) "Hlog".
  iNamed "Hlog". wp_auto.
  rewrite Hnosnap bool_decide_eq_true_2 //=.
  iApply ("HΦ" $! false). iSplit; last done.
  iExists prev, sents, uents. rewrite /own_raftLog_at. iExists lv.
  iFrame "∗#%".
Qed.

End proof.
