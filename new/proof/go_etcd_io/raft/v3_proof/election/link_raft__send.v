Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__send.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_traceSendMessage.

Module SendPostulates : SEND_POSTULATES.
  Include TraceSendMessage.
End SendPostulates.

Module Send := SendProof SendPostulates.
