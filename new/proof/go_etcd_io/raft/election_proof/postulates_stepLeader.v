Require Export New.proof.go_etcd_io.raft.election_proof.spec_stepLeader.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__bcastHeartbeat.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__sendAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__maybeSendAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__bcastAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__appendEntry.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__maybeCommit.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_releasePendingReadIndexMessages.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__MaybeUpdate.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__MaybeDecrTo.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__BecomeProbe.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__BecomeReplicate.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__CanBumpCommit.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Inflights__FreeLE.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__findConflictByTerm.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__firstIndex.

(** The callees on the paths [spec_stepLeader.v] covers:
    [MsgBeat] → [bcastHeartbeat]; [MsgHeartbeatResp] → [raftLog.lastIndex],
    [sendAppend]; [MsgAppResp] → the [Progress] updates, [Inflights.FreeLE],
    [raftLog.findConflictByTerm]/[firstIndex]/[lastIndex], [sendAppend],
    [maybeCommit], [releasePendingReadIndexMessages], [bcastAppend] and
    [maybeSendAppend]; [MsgProp] → [appendEntry], [bcastAppend].  The map
    lookup and the logging calls have lemmas in scope already ([wp_map_lookup1], [wp_Logger__logf]). *)
Module Type STEPLEADER_POSTULATES.
  Include RAFT__BCASTHEARTBEAT.
  Include RAFT__SENDAPPEND.
  Include RAFT__MAYBESENDAPPEND.
  Include RAFT__BCASTAPPEND.
  Include RAFT__APPENDENTRY.
  Include RAFT__MAYBECOMMIT.
  Include RELEASEPENDINGREADINDEXMESSAGES.
  Include PROGRESS__MAYBEUPDATE.
  Include PROGRESS__MAYBEDECRTO.
  Include PROGRESS__BECOMEPROBE.
  Include PROGRESS__BECOMEREPLICATE.
  Include PROGRESS__CANBUMPCOMMIT.
  Include INFLIGHTS__FREELE.
  Include RAFTLOG__FINDCONFLICTBYTERM.
  Include RAFTLOG__LASTINDEX.
  Include RAFTLOG__FIRSTINDEX.
End STEPLEADER_POSTULATES.
