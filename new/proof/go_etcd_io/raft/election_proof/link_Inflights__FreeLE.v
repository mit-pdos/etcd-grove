Require Export New.proof.go_etcd_io.raft.election_proof.proof_Inflights__FreeLE.

Module InflightsFreeLEPostulates : INFLIGHTS__FREELE_POSTULATES.
End InflightsFreeLEPostulates.

Module InflightsFreeLE := InflightsFreeLEProof InflightsFreeLEPostulates.
