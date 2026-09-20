Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_ProgressTracker__Visit.
(* [wp_map_for_range_keep]: the framework's [wp_map_for_range] with the map
   handed back -- [Visit] needs [p.Progress] again after the first range.
   Proof structure only; see the file's header. *)
Require Import New.proof.go_etcd_io.raft.v3_proof.election.proof_ProgressTracker__Visit_helpers.map_for_range_keep.

Module ProgressTrackerVisitProof (P : PROGRESSTRACKER__VISIT_POSTULATES) : PROGRESSTRACKER__VISIT.
Import P.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

(** The body, as Goose translates it ([new/code/go_etcd_io/raft/v3/tracker.v],
    [ProgressTracker__Visitⁱᵐᵖˡ]):

      n := len(p.Progress)
      var sl [7]uint64
      var ids []uint64
      if len(sl) >= n { ids = sl[:n] } else { ids = make([]uint64, n) }
      for id := range p.Progress { n--; ids[n] = id }
      slices.Sort(ids)
      for _, id := range ids { f(id, p.Progress[id]) }

    Three phases.  The [if] is joined ([wp_if_join]) at "[ids] is a slice of
    [n] slots": on the fast path it aliases the stack array ([slice_array] +
    [own_slice_split_all] give the [sl[:n]] prefix), on the slow path
    [wp_slice_make2].  The map range fills the slots from the back; its
    invariant says the last [i] slots hold the first [i] enumerated keys,
    reversed, so at the end [ids] is [reverse keys].  [slices.Sort] permutes
    it.  The slice range then lends [trk ↦ tv], one [own_progress] (out of
    [Hprogs] by [big_sepM_lookup_acc]) and [I] to the closure for every
    entry; every entry is a key of [prs], which is what makes the
    [p.Progress[id]] lookup hit. *)
Lemma wp_visit (trk : loc) tv votes (f : func.t) (I : iProp Σ) :
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker cfg tv votes ∗ I ∗
      □ visit_closure trk tv f I }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "Visit" #f
  {{{ RET #(); trk ↦ tv ∗ own_tracker cfg tv votes ∗ I }}}.
Proof.
  wp_start as "(Htrk & Hown & HI & #Hf)". iNamed "Hown". wp_auto.
  (* [n := len(p.Progress)] *)
  wp_apply (wp_ProgressMap_len with "[$Hprs]") as "Hprs".
  assert (Z.of_nat (size prs) < 2 ^ 63) as Hsz.
  { rewrite -Hprs_dom size_dom in Hcfg_size. exact Hcfg_size. }
  (* Both arms of the [if] end with [ids] pointing at a slice of [n] slots. *)
  wp_if_join (λ v, (∃ (sl : slice.t) (xs : list w64),
      ⌜ v = execute_val ⌝ ∗
      "n" ∷ n_ptr ↦ W64 (size prs) ∗
      "ids" ∷ ids_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* xs ∗
      "%Hxs_len" ∷ ⌜ length xs = size prs ⌝)%I) with "[n ids sl]".
  - (* fast path: [ids = sl[:n]] aliases the stack array *)
    rewrite decide_True; last word.
    wp_auto.
    iDestruct (slice_array with "sl") as "Hsl"; first (simpl; lia).
    iDestruct (own_slice_split_all (W64 (size prs)) with "Hsl") as "[Hsl _]";
      first (simpl; word).
    iExists _, _. iFrame "n ids". iSplitR; first done.
    rewrite /slice.slice /slice_index_ref /=. iFrame "Hsl".
    iPureIntro. rewrite length_take /=. word.
  - (* slow path: [ids = make([]uint64, n)] *)
    wp_apply (wp_slice_make2 (V:=w64) (t:=go.uint64)) as "%sl [Hsl _]"; first word.
    iExists _, _. iFrame. iPureIntro. split; first done.
    rewrite length_replicate. word.
  - iIntros (v) "H". iDestruct "H" as (sl xs) "(-> & H)". iNamed "H".
    wp_auto.
    iDestruct (own_slice_len with "Hsl") as "%Hsl_len".
    assert (sint.Z sl.(slice.len) = Z.of_nat (size prs)) as Hsllen.
    { destruct Hsl_len as [H1 H2]. rewrite -Hxs_len H1 Z2Nat.id //. }
    (* The map range fills [ids] from the back: after [i] iterations the
       last [i] slots hold the first [i] keys, reversed.  [0 ≤ i] has to be
       in the invariant (the body is quantified over every [i] whose lookup
       succeeds), and [id] -- assigned on every iteration -- inside it. *)
    set (Pmap := (λ (keys : list w64) (i : Z),
      ∃ (xs' : list w64) (x : w64),
        "%Hi" ∷ ⌜ 0 ≤ i ≤ Z.of_nat (size prs) ⌝ ∗
        "n" ∷ n_ptr ↦ W64 (Z.of_nat (size prs) - i) ∗
        "ids" ∷ ids_ptr ↦ sl ∗
        "Hsl" ∷ sl ↦* xs' ∗
        "%Hxs'_len" ∷ ⌜ length xs' = size prs ⌝ ∗
        "%Hxs'_suffix" ∷ ⌜ drop (Z.to_nat (Z.of_nat (size prs) - i)) xs'
                           = reverse (take (Z.to_nat i) keys) ⌝ ∗
        "id" ∷ id_ptr ↦ x)%I).
    wp_apply (wp_map_for_range_keep Pmap with "Hprs").
    iIntros (keys) "(%Hkset & %Hklen & %Hknodup)".
    iSplitL "n ids Hsl id".
    { rewrite /Pmap. iExists xs, (W64 0).
      rewrite Z.sub_0_r Nat2Z.id -Hxs_len drop_all take_0 /=. iFrame.
      iPureIntro. split_and!; solve [ done | lia ]. }
    iSplitL "".
    { iIntros "!>" (i key vv) "[%Hkey %Hvv] HP". rewrite /Pmap. iNamed "HP".
      pose proof (lookup_lt_Some _ _ _ Hkey) as Hi_lt.
      wp_auto.
      (* [n--; ids[n] = id] *)
      rewrite decide_True; last word.
      replace (word.sub (W64 (Z.of_nat (size prs) - i)) (W64 1))
        with (W64 (Z.of_nat (size prs) - (i + 1))) by word.
      wp_auto.
      wp_apply (wp_store_slice_index (V:=w64) (t:=go.uint64) sl _ xs' key
                  with "[$Hsl]").
      { iPureIntro. word. }
      iIntros "Hsl".
      replace (sint.Z (W64 (Z.of_nat (size prs) - (i + 1))))
        with (Z.of_nat (size prs) - (i + 1)) by word.
      wp_auto.
      iRight. iLeft. iSplitR; first done.
      iExists _, key. iFrame.
      iPureIntro. split_and!; [ lia | lia | by rewrite -> length_insert | ].
      (* the newly written slot is followed by the slots already filled *)
      assert (Z.to_nat (Z.of_nat (size prs) - i)
              = S (Z.to_nat (Z.of_nat (size prs) - (i + 1)))) as Hsucc by lia.
      assert (∃ old, xs' !! Z.to_nat (Z.of_nat (size prs) - (i + 1)) = Some old)
        as [old Hold].
      { apply lookup_lt_is_Some_2. lia. }
      assert (Z.to_nat (i + 1) = S (Z.to_nat i)) as Hsucc'.
      { exact (Z2Nat.inj_succ i ltac:(lia)). }
      rewrite -> drop_insert_ge by lia.
      rewrite -> Nat.sub_diag.
      rewrite -> (drop_S _ _ _ Hold), <- Hsucc, Hxs'_suffix. simpl.
      rewrite -> Hsucc', (take_S_r _ _ key) by done.
      rewrite -> reverse_snoc. reflexivity. }
    (* the range is over: [ids] holds the keys of [prs], reversed *)
    iIntros "HP Hprs". rewrite /Pmap. iNamed "HP".
    replace (Z.to_nat (Z.of_nat (size prs) - Z.of_nat (size prs))) with 0%nat
      in Hxs'_suffix by lia.
    replace (Z.to_nat (Z.of_nat (size prs))) with (length keys)
      in Hxs'_suffix by lia.
    rewrite drop_0 firstn_all in Hxs'_suffix.
    subst xs'.
    wp_auto.
    (* [slices.Sort(ids)]: a permutation is all the postcondition needs *)
    wp_apply (P.wp_slices_Sort with "[$Hsl]") as "%ys (Hsl & %Hperm)".
    (* every entry of [ids] is a key of [prs] *)
    assert (∀ y, y ∈ ys → is_Some (prs !! y)) as Hys_dom.
    { intros y Hy. apply elem_of_dom. rewrite -Hkset elem_of_list_to_set.
      rewrite -elem_of_reverse. by rewrite Hperm. }
    iDestruct (own_slice_len with "Hsl") as "%Hys_len".
    assert (length ys = size prs) as Hys_size.
    { rewrite -(Permutation_length Hperm) length_reverse Hklen //. }
    iRename "id" into "idold".
    wp_alloc cur_ptr as "cur".
    wp_auto.
    (* The range variable [cur] is written on every iteration, so it lives
       inside the invariant (notes/gotchas.md, "A [for … range] loop
       variable must be inside the [wp_for] invariant"). *)
    iAssert (∃ (j c : w64),
       "i" ∷ i_ptr ↦ j ∗
       "cur" ∷ cur_ptr ↦ c ∗
       "%Hj" ∷ ⌜ 0 ≤ sint.Z j ≤ Z.of_nat (length ys) ⌝ ∗
       "Htrk" ∷ trk ↦ tv ∗
       "HI" ∷ I ∗
       "Hprs" ∷ tv.(tracker.ProgressTracker.Progress') ↦$ prs ∗
       "Hprogs" ∷ ([∗ map] pr ∈ prs, own_progress pr) ∗
       "Hsl" ∷ sl ↦* ys)%I
      with "[i cur Htrk HI Hprs Hprogs Hsl]" as "IH".
    { iExists (W64 0), (W64 0). iFrame. iPureIntro. word. }
    assert (sint.Z sl.(slice.len) = Z.of_nat (length ys)) as Hsllen'.
    { destruct Hys_len as [H1 H2]. rewrite H1 Z2Nat.id //. }
    wp_for "IH".
    wp_if_destruct.
    + (* another id to visit: [f(id, p.Progress[id])] *)
      assert (∃ y, ys !! Z.to_nat (sint.Z j) = Some y) as [y Hy].
      { apply lookup_lt_is_Some_2. word. }
      rewrite decide_True; last word.
      wp_apply (wp_load_slice_index (V:=w64) (t:=go.uint64)
                  sl (sint.Z j) ys (DfracOwn 1) y with "[$Hsl]") as "Hsl";
        try first [ word | iPureIntro; exact Hy | tc_solve | done ].
      wp_apply (wp_map_lookup1 with "Hprs") as "Hprs".
      destruct (Hys_dom y) as [pr Hpr]; first by eapply list_elem_of_lookup_2.
      rewrite Hpr /=.
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hpr with "Hprogs") as "[Hpr Hprogs]".
      wp_apply ("Hf" with "[$Htrk $Hpr $HI]") as "(Htrk & Hpr & HI)".
      iDestruct ("Hprogs" with "Hpr") as "Hprogs".
      wp_for_post.
      iFrame. iPureIntro. word.
    + (* every id visited *)
      iApply "HΦ". iFrame "Htrk HI".
      rewrite /own_tracker.
      iExists prs, voters_ref, voters, learners, learnersNext.
      iFrame "∗%". done.
Qed.

End helpers.

Set Default Proof Using "Type".

  Lemma wp_ProgressTracker__Visit : wp_ProgressTracker__Visit_body.
  Proof.
    intros_ambient.
    intros cfg trk tv votes f I.
    apply wp_visit.
  Qed.

End ProgressTrackerVisitProof.
