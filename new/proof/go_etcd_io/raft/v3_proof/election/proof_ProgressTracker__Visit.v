Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_ProgressTracker__Visit.

Module ProgressTrackerVisitProof (P : PROGRESSTRACKER__VISIT_POSTULATES) : PROGRESSTRACKER__VISIT.

  Lemma wp_ProgressTracker__Visit : wp_ProgressTracker__Visit_body.
  Proof.
    intros_ambient.
    intros cfg trk tv votes f I.

    (* Machine-checked as far as it goes.  With [trk ↦ tv] in hand the receiver
       alloc, the [p.Progress] load and the [len] call's argument all step --
       that is the part the old precondition could not reach at all.  It parks
       on [len] of the [[7]uint64] array, for which no instance exists; see (1)
       in the note above. *)
    wp_start as "(Htrk & Hown & HI & #Hf)". iNamed "Hown". wp_auto.
    (* [n := len(p.Progress)].  No [wp_auto] after this: the next statement is
       [len] of the [[7]uint64] array and it has no instance, so [wp_auto]
       fails with "Failed to progress" rather than parking. *)
    wp_apply (wp_ProgressMap_len with "[$Hprs]") as "Hprs".
  Admitted.

End ProgressTrackerVisitProof.
