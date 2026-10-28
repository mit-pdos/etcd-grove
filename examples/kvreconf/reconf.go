package kvreconf

import (
	"context"
	"time"

	"github.com/goose-lang/primitive"
	pb "go.etcd.io/raft/v3/raftpb"
)

// The bounds of a configuration the reconfigurer keeps to: at most maxVoters voters and
// maxMembers voters and learners, and at least one voter (raft panics applying a change that
// removes them all).
const (
	maxVoters  = 5
	maxMembers = 7
)

// config is a configuration's voters and learners, as the reconfigurer plans changes on it.
type config struct {
	voters   []uint64
	learners []uint64
}

// without is ids without id.
func without(ids []uint64, id uint64) []uint64 {
	var out []uint64
	for _, x := range ids {
		if x != id {
			out = append(out, x)
		}
	}
	return out
}

// pick is a random element of ids (which is not empty).
func pick(ids []uint64) uint64 {
	return ids[primitive.RandomUint64()%uint64(len(ids))]
}

// single is one change on cfg, chosen at random among those that keep it within the bounds and
// touch no id of used (the ids a joint change already touches: one change per id), with the
// configuration after it; ok is false if there is none. A change that adds a replica names a
// fresh id from fresh, which it calls only then.
func single(cfg config, used []uint64, fresh func() uint64) (*pb.ConfChangeSingle, config, bool) {
	var vs, ls []uint64
	for _, id := range cfg.voters {
		if !hasID(used, id) {
			vs = append(vs, id)
		}
	}
	for _, id := range cfg.learners {
		if !hasID(used, id) {
			ls = append(ls, id)
		}
	}
	members := len(cfg.voters) + len(cfg.learners)
	// the kinds that apply: 0 add a voter, 1 add a learner, 2 promote a learner, 3 demote a
	// voter, 4 remove a voter, 5 remove a learner
	var kinds []uint64
	if len(cfg.voters) < maxVoters && members < maxMembers {
		kinds = append(kinds, 0)
	}
	if members < maxMembers {
		kinds = append(kinds, 1)
	}
	if len(ls) > 0 && len(cfg.voters) < maxVoters {
		kinds = append(kinds, 2)
	}
	if len(vs) > 0 && len(cfg.voters) > 1 {
		kinds = append(kinds, 3, 4, 4)
	}
	if len(ls) > 0 {
		kinds = append(kinds, 5)
	}
	if len(kinds) == 0 {
		return nil, cfg, false
	}
	switch pick(kinds) {
	case 0:
		id := fresh()
		return change(pb.ConfChangeAddNode, id), config{append(cfg.voters, id), cfg.learners}, true
	case 1:
		id := fresh()
		return change(pb.ConfChangeAddLearnerNode, id), config{cfg.voters, append(cfg.learners, id)}, true
	case 2:
		id := pick(ls)
		return change(pb.ConfChangeAddNode, id), config{append(cfg.voters, id), without(cfg.learners, id)}, true
	case 3:
		id := pick(vs)
		return change(pb.ConfChangeAddLearnerNode, id), config{without(cfg.voters, id), append(cfg.learners, id)}, true
	case 4:
		id := pick(vs)
		return change(pb.ConfChangeRemoveNode, id), config{without(cfg.voters, id), cfg.learners}, true
	default:
		id := pick(ls)
		return change(pb.ConfChangeRemoveNode, id), config{cfg.voters, without(cfg.learners, id)}, true
	}
}

// change is the single change of kind t to node id.
func change(t pb.ConfChangeType, id uint64) *pb.ConfChangeSingle {
	return &pb.ConfChangeSingle{Type: t.Enum(), NodeId: new(id)}
}

// Reconfigure makes steps random configuration changes, one after the other, each pause apart:
// half of them simple (one change: a ConfChange, or a ConfChangeV2 of the automatic
// transition), half joint (a ConfChangeV2 of one to three changes and of a random transition:
// automatic, implicit or explicit; one change of a transition other than the automatic one
// enters a joint configuration too). A replica a change adds is started (fresh, empty) before
// the change is proposed; a replica a change removes is stopped once the configuration is out
// of its joint state. Each change is carried to its end (proposed again until applied; a joint
// one, left: by raft on its own for the automatic and implicit transitions, by an explicit
// change otherwise) before the next one is chosen, on the configuration it reached: so every
// change the cluster proposes is valid where it is applied.
func (c *Cluster) Reconfigure(steps int, pause time.Duration, stop <-chan struct{}) {
	cfg := config{voters: append([]uint64(nil), initialVoters...)}
	for i := 0; i < steps; i++ {
		select {
		case <-stop:
			return
		case <-time.After(pause):
		}
		cfg = c.reconfigureOnce(cfg)
	}
}

// reconfigureOnce makes one random change on cfg (Reconfigure) and returns the configuration it
// reached.
func (c *Cluster) reconfigureOnce(cfg config) config {
	n := primitive.RandomUint64()
	joint := n%2 == 0
	count := 1
	if joint {
		count = 1 + int((n/2)%3)
	}
	fresh := c.startNew
	var changes []*pb.ConfChangeSingle
	var used []uint64
	next := cfg
	for j := 0; j < count; j++ {
		ch, after, ok := single(next, used, fresh)
		if !ok {
			break
		}
		changes = append(changes, ch)
		used = append(used, ch.GetNodeId())
		next = after
	}
	if len(changes) == 0 {
		return cfg
	}
	c.mu.Lock()
	c.confSeq++
	seq := c.confSeq
	c.mu.Unlock()
	transition := pb.ConfChangeTransitionAuto
	if joint {
		transition = []pb.ConfChangeTransition{pb.ConfChangeTransitionAuto,
			pb.ConfChangeTransitionJointImplicit, pb.ConfChangeTransitionJointExplicit}[(n/6)%3]
	}
	var cc pb.ConfChangeI
	if !joint && (n/2)%2 == 0 {
		cc = &pb.ConfChange{Type: changes[0].Type, NodeId: changes[0].NodeId, Context: confCtx(seq)}
	} else {
		cc = &pb.ConfChangeV2{Transition: transition.Enum(), Changes: changes, Context: confCtx(seq)}
	}
	entersJoint := len(changes) > 1 || transition != pb.ConfChangeTransitionAuto
	if entersJoint {
		c.Stats.add(&c.Stats.JointChanges)
	} else {
		c.Stats.add(&c.Stats.SimpleChanges)
	}
	cs := c.carry(cc, seq)
	if entersJoint {
		if transition == pb.ConfChangeTransitionJointExplicit {
			c.mu.Lock()
			c.confSeq++
			leave := c.confSeq
			c.mu.Unlock()
			cs = c.carry(&pb.ConfChangeV2{Context: confCtx(leave)}, leave)
		} else {
			cs = c.leftJoint(seq)
		}
	}
	c.setMembers(cs)
	return config{voters: cs.GetVoters(), learners: cs.GetLearners()}
}

// carry proposes the configuration change cc, of sequence number seq, until a running replica
// has applied it, and returns that replica's configuration then. It proposes at the leader, or
// at a random member when none is known; raft drops a change proposed while another is not yet
// applied, and a change can be lost with its messages, so it proposes again after a while (a
// copy committed twice is not applied twice: Replica.applyConf).
func (c *Cluster) carry(cc pb.ConfChangeI, seq uint64) *pb.ConfState {
	for {
		r := c.leader()
		if r == nil {
			r = c.randomMember()
		}
		if r != nil {
			ctx, cancel := context.WithTimeout(context.Background(), opTimeout)
			r.node.ProposeConfChange(ctx, cc)
			cancel()
		}
		deadline := time.Now().Add(2 * opTimeout)
		for time.Now().Before(deadline) {
			if cs := c.appliedConf(seq, false); cs != nil {
				return cs
			}
			time.Sleep(5 * time.Millisecond)
		}
	}
}

// leftJoint waits until a running replica has applied change seq and left the joint
// configuration it entered (raft's leader proposes the leaving on its own), and returns that
// replica's configuration then.
func (c *Cluster) leftJoint(seq uint64) *pb.ConfState {
	for {
		if cs := c.appliedConf(seq, true); cs != nil {
			return cs
		}
		time.Sleep(5 * time.Millisecond)
	}
}

// appliedConf is the configuration of a running replica that has applied change seq (and is
// out of the joint state, if notJoint), or nil if there is none.
func (c *Cluster) appliedConf(seq uint64, notJoint bool) *pb.ConfState {
	for _, r := range c.running() {
		_, s, cs := r.state()
		if s >= seq && cs != nil && (!notJoint || len(cs.GetVotersOutgoing()) == 0) {
			return cs
		}
	}
	return nil
}

// Faults injects faults every pause until stop: a random running replica cut off the network
// for a few pauses, or a leadership transfer to a random voter.
func (c *Cluster) Faults(pause time.Duration, stop <-chan struct{}) {
	for {
		select {
		case <-stop:
			c.heal()
			return
		case <-time.After(pause):
		}
		n := primitive.RandomUint64()
		rs := c.running()
		if len(rs) == 0 {
			continue
		}
		victim := rs[n%uint64(len(rs))]
		if (n/16)%2 == 0 {
			c.Stats.add(&c.Stats.Partitions)
			c.setCut(victim.id, true)
			select {
			case <-stop:
			case <-time.After(pause * time.Duration(1+(n/32)%4)):
			}
			c.setCut(victim.id, false)
			continue
		}
		if l := c.leader(); l != nil {
			st := l.node.Status()
			voters := st.Config.Voters.IDs()
			var to []uint64
			for id := range voters {
				if id != l.id {
					to = append(to, id)
				}
			}
			if len(to) > 0 {
				c.Stats.add(&c.Stats.Transfers)
				l.node.TransferLeadership(context.Background(), l.id, pick(to))
			}
		}
	}
}
