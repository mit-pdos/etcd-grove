(** * [append] to a slice whose elements are held read-only

    [wp_slice_append] ([new/golang/theory/slice.v]) takes the destination at
    full ownership, [s ↦* vs].  That is more than Go's [append] needs: when
    it appends in place it writes only the capacity slack past [len(s)], and
    when it reallocates it only *reads* the old elements.  So the elements
    themselves may be held at any fraction -- here, persistently
    ([s ↦*□ vs]) -- as long as the slack is owned ([own_slice_cap], full).

    The raft log needs exactly this.  Entries, once in [unstable.entries],
    are never written again ([log_unstable.go]: every assignment to
    [u.entries] re-slices, allocates, or appends past [len]), so
    [own_raftLog] holds them at [↦*□] and can hand out sub-slices of them
    without a loan; [truncateAndAppend]'s [append(u.entries, ents...)] is
    then this lemma.  Kept here, not in [slice.v], until a second user
    appears. *)

From New.golang.theory Require Import slice.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.
Local Set Default Proof Using "All".
Context [V] `[!ZeroVal V] `[!TypedPointsto (Σ:=Σ) V].

Lemma wp_slice_append_persistent `[!st ↓u go.SliceType t] `[!IntoValTyped V t]
    (s: slice.t) (vs: list V) (s2: slice.t) (vs': list V) dq :
  {{{ s ↦*□ vs ∗ own_slice_cap V s (DfracOwn 1) ∗ s2 ↦*{dq} vs' }}}
    #(functions go.append [st]) #s #s2
  {{{ (s' : slice.t), RET #s';
      s' ↦*□ (vs ++ vs') ∗ own_slice_cap V s' (DfracOwn 1) ∗ s2 ↦*{dq} vs' }}}.
Proof.
  wp_start as "(#Hs & Hcap & Hs2)".
  iDestruct (own_slice_len with "Hs") as %Hs.
  iDestruct (own_slice_len with "Hs2") as %Hs2.
  iDestruct (own_slice_wf with "Hs") as %Hwf1.
  iDestruct (own_slice_wf with "Hs2") as %Hwf2.
  wp_apply wp_sum_assume_no_overflow_signed as "%Hoverflow".
  wp_if_destruct.
  - rewrite decide_True; last word. wp_auto.
    rewrite decide_True; last word. wp_auto.
    rewrite slice_slice; last word.
    do 2 ereplace (word.add (W64 0) ?[e]) with ?e by word.
    (* the slack up to [high], at full ownership; the old elements stay
       where they are, read-only *)
    iDestruct (own_slice_cap_split (word.add s.(slice.len) s2.(slice.len)) with "[$Hcap]") as (vs'') "[Hs_new Hcap]".
    { word. }
    iDestruct (own_slice_len with "Hs_new") as %Hlen.
    simpl in Hlen; autorewrite with len in Hlen.
    wp_apply (wp_slice_copy with "[$Hs_new $Hs2]").
    rewrite -> !Nat.min_l by word.
    iIntros (n) "(%Hn & Hs_new & Hs2)".
    rewrite -> drop_ge, app_nil_r by len.
    rewrite -> take_ge by len.
    iMod (own_slice_persist with "Hs_new") as "#Hs_new".
    wp_auto.
    iApply "HΦ".
    iFrame "Hs2".
    iSplitL "".
    { iDestruct (own_slice_trivial_slice with "Hs") as "Hs0".
      iDestruct (own_slice_combine s.(slice.len) with "Hs0 Hs_new") as "Hall".
      { len. }
      iExact "Hall". }
    iApply (own_slice_cap_slice_change_first with "Hcap").
    move: l; word.
  - (* [(V:=V)] is a workaround: [wp__new_cap] ([slice.v:905]) is stated
       under the section's [Context [V] …] although it never mentions [V],
       so outside that section it quantifies over an unused type and its
       instances, which [wp_apply] leaves as shelved goals.  The fix is to
       state it before that [Context]; notes/todo.md. *)
    wp_apply (wp__new_cap (V:=V)) as "%x %Hcap_ge".
    wp_apply wp_slice_make3.
    { word. }
    iIntros (sl) "(Hnew & Hnew_cap & %Hcap)".
    iDestruct (own_slice_wf with "Hnew") as %Hsl_wf.
    iDestruct (own_slice_len with "Hnew") as %Hsl_len.
    autorewrite with len in Hsl_len.
    assert (word.add (slice.len s) (slice.len s2) = slice.len sl) as Hsl_len'.
    { apply word.unsigned_inj.
      move: Hsl_len; word. }
    wp_auto.
    wp_apply (wp_slice_copy with "[$Hnew $Hs]").
    autorewrite with len.
    rewrite -> !Nat.min_r by word.
    iIntros (n') "(%Hn' & Hnew & _)".
    rewrite -> take_ge by len.
    rewrite drop_replicate.
    wp_auto. rewrite decide_True; last word.
    iDestruct (own_slice_slice
                 s.(slice.len) (word.add s.(slice.len) s2.(slice.len)) with "Hnew") as
        "(Hnew1 & Hnew2 & _)".
    { word. }
    wp_auto.
    wp_apply (wp_slice_copy with "[$Hnew2 $Hs2]").
    autorewrite with len.
    rewrite -> !Nat.min_r by word.
    iIntros (n'') "(%Hn'' & Hnew2 & Hs2)".
    rewrite -> !drop_ge, app_nil_r by len.
    rewrite -> !take_app_le, !take_ge by word.
    iDestruct (own_slice_combine with "Hnew1 Hnew2") as "Hnew".
    { len. }
    iDestruct (own_slice_len with "Hnew") as %Hlen.
    simpl in Hlen.
    autorewrite with len in Hlen.
    iAssert (sl ↦* (vs ++ vs'))%I with "[Hnew]" as "Hnew".
    { iExactEq "Hnew".
      f_equal.
      rewrite {2}(slice_slice_trivial sl (V:=V)).
      f_equal.
      word. }
    iMod (own_slice_persist with "Hnew") as "#Hnew".
    wp_auto.
    iApply "HΦ".
    iFrame "Hs2 Hnew Hnew_cap".
Qed.

End wps.
