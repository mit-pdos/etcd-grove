Require Export New.proof.go_etcd_io.raft.election_proof.proof_IsEmptySnap.

Module IsEmptySnapPostulates : ISEMPTYSNAP_POSTULATES.
End IsEmptySnapPostulates.

Module IsEmptySnap := IsEmptySnapProof IsEmptySnapPostulates.
