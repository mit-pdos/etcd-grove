Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_tracker_NewInflights.

Module TrackerNewInflightsPostulates : TRACKER_NEWINFLIGHTS_POSTULATES.
End TrackerNewInflightsPostulates.

Module TrackerNewInflights := TrackerNewInflightsProof TrackerNewInflightsPostulates.
