Require Export New.proof.go_etcd_io.raft.election_proof.postulates_MakeProgressTracker.

Module MakeProgressTrackerProof (P : MAKEPROGRESSTRACKER_POSTULATES) : MAKEPROGRESSTRACKER.

  Lemma wp_MakeProgressTracker : wp_MakeProgressTracker_body.
  Proof.
    intros_ambient.
    intros mi mb.
    wp_start as "_". wp_auto.
    wp_apply wp_map_make1. iIntros "%v0 Hv0". wp_auto.
    wp_apply wp_map_make1. iIntros "%vm Hvm". wp_auto.
    wp_apply wp_map_make1. iIntros "%pm Hpm". wp_auto.
    iApply "HΦ". iFrame. done.
  Qed.

End MakeProgressTrackerProof.
