Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__send_vote.

Module SendVotePostulates : SEND_VOTE_POSTULATES.
End SendVotePostulates.

Module SendVote := SendVoteProof SendVotePostulates.
