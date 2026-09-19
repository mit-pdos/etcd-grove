Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__hasUnappliedConfChanges.

Module RaftHasUnappliedConfChangesProof (P : RAFT__HASUNAPPLIEDCONFCHANGES_POSTULATES) : RAFT__HASUNAPPLIEDCONFCHANGES.

  (** Returns [false] because **no configuration change is ever requested** --
      a scope assumption sanctioned 2026-09-16 and now listed in
      [election_protocol.v].  Note what it is *not*: the function's early
      [return false] is guarded by [applied >= committed], which the election
      scope does not imply, so the result does not follow from "the voter set is
      fixed".  It follows from the log containing no [EntryConfChange] or
      [EntryConfChangeV2] entry, which makes the [scan] over
      [(applied, committed]] find nothing.

      Blocked on [own_raftLog] only: that assumption has to be a conjunct of
      the log predicate, and [own_raftLog] is still an opaque [Axiom] in
      [inv_raftlog.v].  Once it is a real definition carrying "no conf-change
      entries", this is a walk over [scan] with an empty result. *)
  Lemma wp_raft__hasUnappliedConfChanges : wp_raft__hasUnappliedConfChanges_body.
  Proof.
    intros_ambient.
    intros r l.

  Admitted.

End RaftHasUnappliedConfChangesProof.
