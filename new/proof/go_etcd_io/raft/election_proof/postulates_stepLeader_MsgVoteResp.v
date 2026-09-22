Require Export New.proof.go_etcd_io.raft.election_proof.spec_stepLeader_MsgVoteResp.

(** No direct callees among the raft functions with their own specs.  On the
    [MsgVoteResp] path [stepLeader] does a map lookup and possibly one
    [Logger.Debugf]; both have lemmas in scope already
    ([wp_map_lookup1], [wp_Logger__logf]). *)
Module Type STEPLEADER_POSTULATES.
End STEPLEADER_POSTULATES.
