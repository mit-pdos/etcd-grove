Require Export New.proof.go_etcd_io.raft.election_proof.proof_JointConfig__VoteResult.
Require Export New.proof.go_etcd_io.raft.election_proof.link_MajorityConfig__VoteResult.

Module JointConfigVoteResultPostulates : JOINTCONFIG__VOTERESULT_POSTULATES.
  Include MajorityConfigVoteResult.
End JointConfigVoteResultPostulates.

Module JointConfigVoteResult :=
  JointConfigVoteResultProof JointConfigVoteResultPostulates.
