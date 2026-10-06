Require Export New.proof.go_etcd_io.raft.election_proof.proof_RawNode__Propose.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__Step.

Module RawNodeProposePostulates : RAWNODE__PROPOSE_POSTULATES.
  Include Step.
End RawNodeProposePostulates.

Module RawNodePropose := RawNodeProposeProof RawNodeProposePostulates.
