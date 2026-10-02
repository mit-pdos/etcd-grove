Require Export New.proof.go_etcd_io.raft.election_proof.proof_stepLeader.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__bcastHeartbeat.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__sendAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__maybeSendAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__bcastAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__appendEntry.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__maybeCommit.
Require Export New.proof.go_etcd_io.raft.election_proof.link_releasePendingReadIndexMessages.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__MaybeUpdate.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__MaybeDecrTo.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__BecomeProbe.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__BecomeReplicate.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Progress__CanBumpCommit.
Require Export New.proof.go_etcd_io.raft.election_proof.link_Inflights__FreeLE.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__findConflictByTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__firstIndex.

Module StepLeaderPostulates : STEPLEADER_POSTULATES.
  Include RaftBcastHeartbeat.
  Include RaftSendAppend.
  Include RaftMaybeSendAppend.
  Include RaftBcastAppend.
  Include RaftAppendEntry.
  Include RaftMaybeCommit.
  Include ReleasePendingReadIndexMessages.
  Include ProgressMaybeUpdate.
  Include ProgressMaybeDecrTo.
  Include ProgressBecomeProbe.
  Include ProgressBecomeReplicate.
  Include ProgressCanBumpCommit.
  Include InflightsFreeLE.
  Include RaftLogFindConflictByTerm.
  Include RaftLogLastIndex.
  Include RaftLogFirstIndex.
End StepLeaderPostulates.

Module StepLeader := StepLeaderProof StepLeaderPostulates.
