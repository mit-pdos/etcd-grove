//go:build ignore

// Requirement snippets for raft's core (batch R2): configuration changes.
package raft

import (
	pb "go.etcd.io/raft/v3/raftpb"
)

// REQ raftcore/apply-conf: applying a decided conf change does not panic and returns the new
// configuration.
// Users: rawnode.go:121 (ApplyConfChange), node.go:399 (run's confc arm).
// Assumes: cc is the decision on a delivered conf entry, defined at the node's configuration view
// (R1's confDecided, Membership.applyChange ... = some m').
// Specs: raft.applyConfChange.spec.
func ReqApplyConf(r *raft, cc pb.ConfChangeI) *pb.ConfState {
	cs := r.applyConfChange(cc.AsV2())
	if cs == nil {
		panic("apply-conf: no ConfState")
	}
	return cs
}
