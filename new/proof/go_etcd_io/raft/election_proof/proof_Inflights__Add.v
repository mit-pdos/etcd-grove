Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Inflights__Add.

Module InflightsAddProof (P : INFLIGHTS__ADD_POSTULATES) : INFLIGHTS__ADD.
Import P.

  (** The tail shared by the three reachable leaves: write the new
      [inflight] into slot [next] of whatever buffer [Hbuf] now holds, bump
      [count] and [bytes], and hand back [own_inflights].

      The [v] parameter is the value being stored.  It has to be passed
      explicitly: with [v'] left as an evar, [wp_apply] cannot unify
      [# ?v'] with the struct literal in the goal and reports "iApply: cannot
      apply".

      The two [wp_auto]s around [decide_True] are both needed and both
      fragile.  The leading one is [try] because after [wp_if_destruct] the
      goal is already at the [decide], while after the [grow] call it is
      still at the [IndexRef]; the trailing one turns the expression pair
      [(index_ref, value)] into a *value* pair, which is the form
      [wp_store_slice_index] is stated at. *)
  Local Ltac add_store v :=
    try wp_auto;
    iDestruct (own_slice_len with "Hbuf") as %[Hbl2 Hbl2'];
    rewrite decide_True; last word;
    wp_auto;
    wp_apply (wp_store_slice_index (V:=tracker.inflight.t)
                (t:=tracker.inflight) _ _ _ v with "[$Hbuf]");
    [ iPureIntro; word | ];
    iIntros "Hbuf";
    wp_auto;
    iApply "HΦ"; iExists _, _; rewrite /own_inflights;
    iFrame "Hiv Hbuf Hbuf_cap"; iPureIntro;
    rewrite /inflights_ok /= length_insert;
    split_and!; solve [ word | left; word | right; word ].

  (** [in.Add(index, bytes)].

      The premise [inflights_full iv = false] does two jobs.  Directly it
      rules out the opening [panic].  Indirectly it gives [count < size],
      hence [0 < size], hence (by [inflights_ok]'s fifth conjunct)
      [start < size] -- and those are what make the index arithmetic
      bounded: [start + count < 2 * size < 2^63], so the [go.int] addition
      cannot overflow, and the wrapped [next] lands in [[0, size)].

      Three reachable leaves, by the two [if]s:

      - [start + count ≥ size] (the ring wraps).  Then
        [len(buffer) ≤ size ≤ start + count], so the first disjunct of
        [inflights_ok]'s last conjunct is only satisfiable together with the
        second, i.e. [len(buffer) = size]: the buffer is already the whole
        ring.  Hence [next < size = len(buffer)] and the [grow] arm is
        **dead** -- that is the [exfalso].  The invariant survives
        [count++] through [len(buffer) = size].
      - no wrap, [next < len(buffer)].  Here [next = start + count], so
        [start + count + 1 ≤ len(buffer)]: the invariant survives through
        its *first* disjunct.
      - no wrap, [next ≥ len(buffer)]: [grow].  [inflights_ok] gives
        [start + count ≤ len(buffer)] (the second disjunct would make
        [len(buffer) = size > next ≥ len(buffer)]), so with the test
        [next = start + count = len(buffer) < size] -- which is exactly
        [grow]'s premise.  [grow] returns a buffer of
        [max 1 (min (2 * len(buffer)) size)] slots, strictly more than
        [len(buffer)], so the write is in range and
        [start + count + 1 ≤ len(buffer')] again. *)
  Lemma wp_Inflights__Add : wp_Inflights__Add_body.
  Proof.
    intros_ambient.
    intros l iv buf index bytes Hfull.
    wp_start as "H". iNamed "H". wp_auto.
    wp_apply (wp_Inflights__Full with "[$Hin]") as "Hin".
    rewrite Hfull.
    iNamed "Hin".
    iDestruct (own_slice_len with "Hbuf") as %[Hblen Hblen0].
    (* not full ⇒ [count ≠ size], and with [inflights_ok] that is
       [count < size], [0 < size] and [start < size]. *)
    rewrite /inflights_full in Hfull.
    apply orb_false_elim in Hfull as [Hcnt _].
    apply bool_decide_eq_false in Hcnt.
    destruct Hinfl_ok as (Hs0 & Hc & Hbl & Hsz & Hstart & Hring).
    assert (sint.Z iv.(tracker.Inflights.count')
            < sint.Z iv.(tracker.Inflights.size'))%Z as Hclt.
    { assert (iv.(tracker.Inflights.count') ≠ iv.(tracker.Inflights.size'))
        by exact Hcnt. word. }
    assert (0 < sint.Z iv.(tracker.Inflights.size'))%Z as Hszpos by word.
    assert (sint.Z iv.(tracker.Inflights.start')
            < sint.Z iv.(tracker.Inflights.size'))%Z as Hslt
        by (destruct Hstart; word).
    wp_auto.
    wp_if_destruct.
    - (* [start + count ≥ size]: the ring wraps, so the buffer is already
         the full ring. *)
      assert (Z.of_nat (length buf) = sint.Z iv.(tracker.Inflights.size'))%Z
        as HL by (destruct Hring; word).
      wp_if_destruct.
      + (* unreachable: [next < size = len(buffer)] *)
        exfalso. word.
      + add_store (tracker.inflight.mk index bytes).
    - (* no wrap: [next = start + count] *)
      wp_if_destruct.
      + (* the occupied range reaches the end of the buffer: grow *)
        iAssert (own_inflights l iv buf) with "[Hiv Hbuf Hbuf_cap]" as "Hin".
        { rewrite /own_inflights. iFrame. iPureIntro.
          exact (conj Hs0 (conj Hc (conj Hbl (conj Hsz (conj Hstart Hring))))). }
        wp_apply (wp_Inflights__grow with "[$Hin]")
          as "%sl %buf' Hg".
        { word. }
        { word. }
        iNamed "Hg". iNamed "Hin".
        (* [own_inflights] states the buffer as [(iv <| buffer' := sl |>).(buffer')];
           [add_store]'s [word] needs it as [sl] *)
        iEval (rewrite /=) in "Hbuf".
        add_store (tracker.inflight.mk index bytes).
      + add_store (tracker.inflight.mk index bytes).
  Qed.

End InflightsAddProof.
