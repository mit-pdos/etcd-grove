Require Export New.proof.go_etcd_io.raft.election_proof.proof_strings_Join.

Module StringsJoinPostulates : STRINGS_JOIN_POSTULATES.
End StringsJoinPostulates.

Module StringsJoin := StringsJoinProof StringsJoinPostulates.
