Require Export New.proof.go_etcd_io.raft.election_proof.proof_logSliceFromMsgApp.

Module LogSliceFromMsgAppPostulates : LOGSLICEFROMMSGAPP_POSTULATES.
End LogSliceFromMsgAppPostulates.

Module LogSliceFromMsgApp := LogSliceFromMsgAppProof LogSliceFromMsgAppPostulates.
