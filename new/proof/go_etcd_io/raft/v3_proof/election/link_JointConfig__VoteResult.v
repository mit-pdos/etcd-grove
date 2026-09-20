Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_JointConfig__VoteResult.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_MajorityConfig__VoteResult.

Module JointConfigVoteResultPostulates : JOINTCONFIG__VOTERESULT_POSTULATES.
  Include MajorityConfigVoteResult.
End JointConfigVoteResultPostulates.

Module JointConfigVoteResult :=
  JointConfigVoteResultProof JointConfigVoteResultPostulates.
