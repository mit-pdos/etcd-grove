Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_IsEmptySnap.

Module IsEmptySnapPostulates : ISEMPTYSNAP_POSTULATES.
End IsEmptySnapPostulates.

Module IsEmptySnap := IsEmptySnapProof IsEmptySnapPostulates.
