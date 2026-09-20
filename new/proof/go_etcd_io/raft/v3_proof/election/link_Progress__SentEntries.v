Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_Progress__SentEntries.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_Inflights__Add.

Module ProgressSentEntriesPostulates : PROGRESS__SENTENTRIES_POSTULATES.
  Include InflightsAdd.
  Include InflightsFull.
End ProgressSentEntriesPostulates.

Module ProgressSentEntries :=
  ProgressSentEntriesProof ProgressSentEntriesPostulates.
