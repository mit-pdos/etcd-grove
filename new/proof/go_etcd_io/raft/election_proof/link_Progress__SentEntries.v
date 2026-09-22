Require Export New.proof.go_etcd_io.raft.election_proof.proof_Progress__SentEntries.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Inflights__Add.

Module ProgressSentEntriesPostulates : PROGRESS__SENTENTRIES_POSTULATES.
  Include InflightsAdd.
  Include InflightsFull.
End ProgressSentEntriesPostulates.

Module ProgressSentEntries :=
  ProgressSentEntriesProof ProgressSentEntriesPostulates.
