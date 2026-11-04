package kvreconf

import (
	"context"
	"time"

	pb "go.etcd.io/raft/v3/raftpb"
)

// pick is a random element of ids (which is not empty).
func pick(ids []uint64) uint64 {
	return ids[below(uint64(len(ids)))]
}

// randomID is the id a random change names: one of the configuration's (cs's voters, outgoing
// voters and learners), another replica's (one removed earlier, or started and never added),
// or, for a change that adds one (add), sometimes a fresh replica's, started now.
func (c *Cluster) randomID(cs *pb.ConfState, add bool) uint64 {
	if add && oneIn(4) {
		if id, ok := c.startNew(); ok {
			return id
		}
	}
	ids := append(append(append([]uint64(nil), cs.GetVoters()...), cs.GetVotersOutgoing()...), cs.GetLearners()...)
	if len(ids) == 0 || oneIn(4) {
		return c.random().id
	}
	return pick(ids)
}

// randomChange is a random configuration change, chosen with a random replica's configuration
// in view (which may be out of date, or not yet any) so that it is often valid where it is
// applied, but not always: the leaving of a joint configuration (an empty ConfChangeV2, one
// time in eight), or one to three single changes -- add a voter, add a learner, remove, update
// (a no-op) -- each of a random id (randomID), of a random transition, as a ConfChangeV2, or, for
// one change of the automatic transition, one time in two as a ConfChange.
func (c *Cluster) randomChange() pb.ConfChangeI {
	cs, _ := c.random().conf()
	if oneIn(8) {
		return &pb.ConfChangeV2{}
	}
	count := 1
	if oneIn(2) {
		count = 1 + int(below(3))
	}
	var changes []*pb.ConfChangeSingle
	for i := 0; i < count; i++ {
		var t pb.ConfChangeType
		switch below(16) {
		case 0, 1, 2, 3, 4:
			t = pb.ConfChangeAddNode
		case 5, 6, 7, 8:
			t = pb.ConfChangeAddLearnerNode
		case 9, 10, 11, 12, 13, 14:
			t = pb.ConfChangeRemoveNode
		default:
			t = pb.ConfChangeUpdateNode
		}
		id := c.randomID(cs, t != pb.ConfChangeRemoveNode)
		changes = append(changes, &pb.ConfChangeSingle{Type: t.Enum(), NodeId: new(id)})
	}
	transition := []pb.ConfChangeTransition{pb.ConfChangeTransitionAuto,
		pb.ConfChangeTransitionJointImplicit, pb.ConfChangeTransitionJointExplicit}[below(3)]
	if count == 1 && transition == pb.ConfChangeTransitionAuto && oneIn(2) {
		return &pb.ConfChange{Type: changes[0].Type, NodeId: changes[0].NodeId}
	}
	return &pb.ConfChangeV2{Transition: transition.Enum(), Changes: changes}
}

// sleep waits a random time below 2*pause, or until stop; it says whether stop came.
func sleep(pause time.Duration, stop <-chan struct{}) bool {
	select {
	case <-stop:
		return true
	case <-time.After(time.Duration(below(uint64(2 * pause)))):
		return false
	}
}

// Reconfigure proposes random configuration changes (randomChange) through random replicas,
// at random times (pause apart on average), until stop. It never waits for a change to be
// committed or applied, nor for another to be done: raft refuses some (another change pending,
// a joint configuration to leave first), the network loses some, and a replica rejects a
// committed one that is invalid where it is applied (Replica.applyConf). Several may run at once.
func (c *Cluster) Reconfigure(pause time.Duration, stop <-chan struct{}) {
	for !sleep(pause, stop) {
		cc := c.randomChange()
		c.Stats.add(&c.Stats.ConfChangesProposed)
		ctx, cancel := context.WithTimeout(context.Background(), opTimeout)
		c.random().node.ProposeConfChange(ctx, cc)
		cancel()
	}
}

// Disrupt makes random calls of raft's that move leadership, at random times (pause apart on
// average), until stop: a leadership transfer to a random replica, asked of a random replica
// (a follower forwards it to its leader); a campaign; a leader forgotten (Node.ForgetLeader).
func (c *Cluster) Disrupt(pause time.Duration, stop <-chan struct{}) {
	for !sleep(pause, stop) {
		r := c.random()
		ctx, cancel := context.WithTimeout(context.Background(), opTimeout)
		switch below(3) {
		case 0:
			r.node.TransferLeadership(ctx, r.node.Status().Lead, c.random().id)
		case 1:
			r.node.Campaign(ctx)
		default:
			r.node.ForgetLeader(ctx)
		}
		cancel()
	}
}
