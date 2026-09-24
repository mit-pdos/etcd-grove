Require Export New.proof.go_etcd_io.raft.election_proof.proof_MakeProgressTracker.

Module MakeProgressTrackerPostulates : MAKEPROGRESSTRACKER_POSTULATES.
End MakeProgressTrackerPostulates.

Module MakeProgressTracker := MakeProgressTrackerProof MakeProgressTrackerPostulates.
