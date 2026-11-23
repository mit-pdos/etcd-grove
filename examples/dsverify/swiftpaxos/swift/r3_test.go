package swift

import (
	"testing"

	"github.com/imdea-software/swiftpaxos/state"
)

func reported(m *MNewLeaderAckN, c CommandId) (int, state.Command, Dep, bool) {
	for i, id := range m.CmdIds {
		if id == c {
			return m.Phases[i], m.Cmds[i], Dep(m.Deps[i].Dep), true
		}
	}
	return 0, state.Command{}, nil, false
}

// R3: a replica reports to the new leader the commands it executed. A
// descriptor is removed after its command executes (its history slot), so
// fillNewLeaderAckN did not report it, and the new ballot could order it
// after others (or drop it, with its client's result).
//
// Replica 1 of three (follower) commits and executes c (the leader's fast ack
// and its own slow ack); its report must have c, committed, with the
// leader's dependencies.
func TestIssueR3_ExecutedReported(t *testing.T) {
	seqDescs(t)
	r := newTestReplica(t, 3, 1, 0, true)
	c, d := cid(1, 0), cid(2, 0)
	propose(r, put(d, 7, "d"))
	r.getCmdDescSeq(d, &MFastAck{Replica: 0, Ballot: 0, CmdId: d, Dep: []CommandId{},
		Checksum: []SHash{{}}}, nil, nil, false)
	propose(r, put(c, 7, "c"))
	r.getCmdDescSeq(c, &MFastAck{Replica: 0, Ballot: 0, CmdId: c, Dep: []CommandId{d},
		Checksum: []SHash{{}}}, nil, nil, false)
	if !r.delivered.Has(c.String()) {
		t.Fatal("c not executed")
	}
	m := &MNewLeaderAckN{}
	r.fillNewLeaderAckN(m)
	phase, _, dep, ok := reported(m, c)
	if !ok || phase != COMMIT || !dep.Equals(Dep{d}) {
		t.Fatalf("c reported %v, phase %d, dependencies %v; want COMMIT with {d}", ok, phase, dep)
	}
}

// R2: a proposal without a handled descriptor (its goroutine was stopped
// before taking it) is reported with its command, not as a no-op in ACCEPT,
// which the new leader committed in its place (its client got the no-op's
// empty result).
func TestIssueR2_NoNoop(t *testing.T) {
	r := newTestReplica(t, 3, 1, 0, false)
	c := cid(1, 0)
	r.proposes[c] = put(c, 7, "c")
	m := &MNewLeaderAckN{}
	r.fillNewLeaderAckN(m)
	phase, cmd, _, ok := reported(m, c)
	if !ok || cmd.Op != state.PUT || string(cmd.V) != "c" || phase == ACCEPT || phase == COMMIT {
		t.Fatalf("c reported %v, phase %d, command %v; want its command, not accepted", ok, phase, cmd)
	}
}
