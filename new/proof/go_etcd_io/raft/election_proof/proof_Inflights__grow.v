Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Inflights__grow.

Module InflightsGrowProof (P : INFLIGHTS__GROW_POSTULATES) : INFLIGHTS__GROW.

  (** The three branches of the [newSize] computation differ only in the
      literal that reaches [make]; everything after it -- the [make], the
      [copy], and the two pure obligations -- is the same script, so it is
      factored into this tactic.

      Two things to know about it.  (1) [wp_slice_make2] already steps the
      store of the fresh slice into [newBuffer], and [wp_slice_copy] steps
      the field write and the [return:], so there is no [wp_auto] anywhere
      after the [if] chain: adding one fails with "Failed to progress".
      (2) [wp_slice_copy] leaves the destination at
      [take (len dst) src ++ drop (len src) dst]; with [dst] a [replicate]
      and [len src ≤ len dst] that is [take_ge] then [drop_replicate], i.e.
      exactly [buf ++ replicate (new - old) zero]. *)
  Local Ltac grow_tail :=
    wp_apply (wp_slice_make2 (V:=tracker.inflight.t) (t:=tracker.inflight))
      as "%sl (Hsl & Hsl_cap)"; first word;
    wp_apply (wp_slice_copy (V:=tracker.inflight.t) (t:=tracker.inflight)
                with "[$Hsl $Hbuf]") as "%ncopy (%Hncopy & Hsl & Hbuf)";
    rewrite length_replicate take_ge; last word;
    rewrite drop_replicate;
    iApply "HΦ"; iFrame "Hiv Hsl Hsl_cap"; iPureIntro; split;
    rewrite ?length_app ?length_replicate;
    [ word | f_equal; f_equal; lia ].

  Lemma wp_Inflights__grow : wp_Inflights__grow_body.
  Proof.
    intros_ambient.
    intros l iv buf Hsmall Hsize.
    wp_start as "H". iNamed "H".
    (* [len(in.buffer)] is the [slice.len] field; the pure length of [buf] is
       what both premises and the postcondition speak about. *)
    iDestruct (own_slice_len with "Hbuf") as %[Hblen Hblen0].
    wp_auto.
    wp_if_destruct.
    - (* [len(buffer) * 2 == 0].  The product cannot wrap -- [len(buffer)] is
         below [size < 2^62] -- so this says the buffer is empty, and the new
         size is the literal 1.  [size ≥ 1] by [Hsmall], so 1 ≤ size. *)
      grow_tail.
    - wp_if_destruct.
      + (* [2 * len(buffer) > size]: cap at [size]. *)
        grow_tail.
      + (* [2 * len(buffer) ≤ size]: double. *)
        grow_tail.
  Qed.

End InflightsGrowProof.
