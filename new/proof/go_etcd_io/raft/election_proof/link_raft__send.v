Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__send.
Require Export New.proof.go_etcd_io.raft.election_proof.link_traceSendMessage.

Module SendPostulates : SEND_POSTULATES.
  Include TraceSendMessage.
End SendPostulates.

Module Send := SendProof SendPostulates.
