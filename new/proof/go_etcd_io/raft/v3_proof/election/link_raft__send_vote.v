Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__send_vote.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_traceSendMessage.

Module SendVotePostulates : SEND_VOTE_POSTULATES.
  Include TraceSendMessage.
End SendVotePostulates.

Module SendVote := SendVoteProof SendVotePostulates.
