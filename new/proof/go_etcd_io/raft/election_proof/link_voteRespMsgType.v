Require Export New.proof.go_etcd_io.raft.election_proof.proof_voteRespMsgType.

Module VoteRespMsgTypePostulates : VOTERESPMSGTYPE_POSTULATES.
End VoteRespMsgTypePostulates.

Module VoteRespMsgType := VoteRespMsgTypeProof VoteRespMsgTypePostulates.
