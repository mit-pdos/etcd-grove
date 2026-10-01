Require Export New.proof.go_etcd_io.raft.election_proof.proof_Progress__BecomeProbe.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__ResetState.

Module ProgressBecomeProbePostulates : PROGRESS__BECOMEPROBE_POSTULATES.
  Include ProgressResetState.
End ProgressBecomeProbePostulates.

Module ProgressBecomeProbe := ProgressBecomeProbeProof ProgressBecomeProbePostulates.
