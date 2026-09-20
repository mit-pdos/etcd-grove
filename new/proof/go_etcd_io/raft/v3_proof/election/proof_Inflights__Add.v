Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_Inflights__Add.

Module InflightsAddProof (P : INFLIGHTS__ADD_POSTULATES) : INFLIGHTS__ADD.
Import P.

  (** **Admitted, and only this.**  The statement is the true one -- the
      [Full] premise rules out the [panic], and [inflights_ok] (carried by
      [own_inflights_at]) rules out the out-of-range [buffer] write -- and
      the argument is written out below; what is missing is the script.

      What is left to do:

      - a collection for [Inflights.grow] (tracker.v:131), whose triple is
        [own_inflights_at l iv ∗ ⌜ next ≥ len(buffer) ⌝ ∗
         ⌜ inflights_ok iv (len buf) ⌝ ⊢ … own_inflights_at l iv' with
         len(buffer') = min(2*len(buffer), size)] (or [1] when the buffer is
         empty), which needs [wp_slice_make2] and [wp_copy];
      - the arithmetic that re-establishes [inflights_ok] after
        [count := count + 1], which is spelled out in [inflights_ok]'s
        comment in [inv_tracker.v] and is four cases: buffer already at full
        ring size; occupied range does not reach the end of the buffer;
        occupied range ends exactly at the buffer end (grow); empty buffer.

      Nothing above this depends on the *proof*, only on the statement:
      [SentEntries], [maybeSendAppend], [sendAppend] and [bcastAppend] are
      all [Qed] against it. *)
  Lemma wp_Inflights__Add : wp_Inflights__Add_body.
  Proof.
    intros_ambient.
    intros l iv index bytes Hfull.
  Admitted.

End InflightsAddProof.
