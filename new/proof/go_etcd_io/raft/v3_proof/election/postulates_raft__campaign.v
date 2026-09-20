Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__campaign.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__becomeCandidate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__poll.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__send.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_voteRespMsgType.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__promotable.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_JointConfig__IDs.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__lastEntryID.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_slices_Sort.

Module Type CAMPAIGN_POSTULATES.
  Include BECOMECANDIDATE.
  Include POLL.
  Include SEND.
  (* [campaign] calls [voteRespMsgType] for the self-addressed response.
     Missing until 2026-09-16, which made that send unprovable. *)
  Include VOTERESPMSGTYPE.  Include RAFT__PROMOTABLE.
  Include JOINTCONFIG__IDS.
  Include RAFTLOG__LASTENTRYID.
  Include SLICES_SORT.
End CAMPAIGN_POSTULATES.
