Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_ProgressTracker__Visit.

Module ProgressTrackerVisitProof (P : PROGRESSTRACKER__VISIT_POSTULATES) : PROGRESSTRACKER__VISIT.

  Lemma wp_ProgressTracker__Visit : wp_ProgressTracker__Visit_body.
  Proof.
    intros_ambient.
    intros cfg trk tv votes f I.

    (* Machine-checked as far as it goes.  Both obstacles named in the spec
       are gone as of 2026-09-17, so a [wp_auto] after the [len] call now
       gets through [len(sl) >= n] and, on the fast path, through
       [ids = sl[:n]]; what is left is the proof itself, sketched at the end
       of the note in [spec_ProgressTracker__Visit.v]. *)
    wp_start as "(Htrk & Hown & HI & #Hf)". iNamed "Hown". wp_auto.
    (* [n := len(p.Progress)] *)
    wp_apply (wp_ProgressMap_len with "[$Hprs]") as "Hprs".
  Admitted.

End ProgressTrackerVisitProof.
