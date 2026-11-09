package raftnode

import (
	"context"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// REQ raftnode/propose-v1: etcd proposes legacy changes (add, add learner, remove, update,
// promotion as add); the error is a node error only.
// Users: server/etcdserver/server.go:1785 (EtcdServer.configure), examples/raft/kvdurable/reconf.go:90.
// Assumes: n is a node of the cluster; the client's update for the change is supplied.
// Specs: node.ProposeConfChange.spec, confChangeToMsg.spec.
func ReqProposeV1(ctx context.Context, n raft.Node, id uint64, typ pb.ConfChangeType) {
	cc := &pb.ConfChange{Type: typ.Enum(), NodeId: proto.Uint64(id)}
	if err := n.ProposeConfChange(ctx, cc); err != nil && err != raft.ErrStopped && ctx.Err() == nil {
		panic("propose conf change: unexpected error")
	}
}

// REQ raftnode/propose-v2-joint: v2 changes, joint consensus entered explicitly or
// automatically, and left with an empty v2 change.
// Users: examples/raft/kvreconf/reconf.go, examples/raft/kvdurable/reconf.go.
// Assumes: as ReqProposeV1.
// Specs: node.ProposeConfChange.spec.
func ReqProposeV2Joint(ctx context.Context, n raft.Node, add, remove uint64) {
	cc := &pb.ConfChangeV2{
		Transition: pb.ConfChangeTransitionJointExplicit.Enum(),
		Changes: []*pb.ConfChangeSingle{
			{Type: pb.ConfChangeAddNode.Enum(), NodeId: proto.Uint64(add)},
			{Type: pb.ConfChangeRemoveNode.Enum(), NodeId: proto.Uint64(remove)},
		},
	}
	_ = n.ProposeConfChange(ctx, cc)
	_ = n.ProposeConfChange(ctx, &pb.ConfChangeV2{}) // leave the joint configuration
}

// REQ raftnode/apply-or-refuse: a committed conf change is applied, or refused -- by applying it
// with NodeId 0 (etcd: a no-op) or by not calling ApplyConfChange (raft's documentation) -- the
// same way at every node; ApplyConfChange then returns the new configuration.
// Users: server/etcdserver/server.go:2032-2053 (applyConfChange), examples/raft/kvdurable/kv.go:700.
// Assumes: e is a committed conf-change entry at position k, delivered to n, at or past n's view,
// whose decision valid (the client's, cluster-wide: confDecide) was taken before; refuseByZero is
// etcd's mode, used only at configurations that are not joint (etcd proposes v1 only); the caller
// holds a nodeRunning share of n (it runs the Ready loop).
// Specs: node.ApplyConfChange.spec; laws: confDecide.spec, confAt_decided.spec, confAt_valid.spec,
// committedLb_confDecodes.spec, Membership.applyChange_v1.spec.
func ReqApplyOrRefuse(n raft.Node, e *pb.Entry, valid, refuseByZero bool) *pb.ConfState {
	if e.GetType() != pb.EntryConfChange {
		return nil
	}
	var cc pb.ConfChange
	if err := proto.Unmarshal(e.GetData(), &cc); err != nil {
		panic("a committed conf change that does not decode")
	}
	if !valid {
		if !refuseByZero {
			return nil
		}
		cc.NodeId = proto.Uint64(raft.None)
	}
	cs := n.ApplyConfChange(&cc)
	if cs == nil {
		panic("ApplyConfChange: nil from a running node")
	}
	return cs
}

// REQ raftnode/entry-types: a client that never proposes a v2 change and never enters a joint
// configuration sees only EntryNormal and EntryConfChange entries committed (etcd's apply panics on
// any other type).
// Users: server/etcdserver/server.go:1958-1962 (EtcdServer.apply), apply/apply.go:29-36.
// Assumes: no client of the cluster proposes a ConfChangeV2; every configuration of the cluster
// is not joint (confAt facts the client keeps: v1 changes from a non-joint configuration give a
// non-joint one, Membership.applyChange_v1); ents are committed entries delivered to a node.
// Specs: readyChan_recv.spec (committedLb); laws: committedLb_emptyV2.spec, committedOps_lb.spec,
// committedLb_confDecodes.spec.
func ReqEntryTypes(ents []*pb.Entry) {
	for _, e := range ents {
		switch e.GetType() {
		case pb.EntryNormal, pb.EntryConfChange:
		default:
			panic("an entry type no client proposed")
		}
	}
}
