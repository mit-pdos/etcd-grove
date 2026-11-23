package swift

import (
	"reflect"
	"testing"
	"time"
	"unsafe"

	fastrpc "github.com/imdea-software/swiftpaxos/rpc"
	"github.com/imdea-software/swiftpaxos/state"
)

// sent returns the messages r's sender was given so far (SendArg's fields
// are replica's; read them by reflection).
func sent(r *Replica) []fastrpc.Serializable {
	out := []fastrpc.Serializable{}
	for {
		select {
		case arg := <-r.sender:
			v := reflect.ValueOf(&arg).Elem().FieldByName("msg")
			m := reflect.NewAt(v.Type(), unsafe.Pointer(v.UnsafeAddr())).Elem().Interface()
			out = append(out, m.(fastrpc.Serializable))
		default:
			return out
		}
	}
}

// R1: the recovery keeps a command that a fast quorum pre-accepted with the
// same dependencies (the paper's Figure 5, l. 58-61): it may have been
// chosen on the fast path, and its client may have its result.
//
// Three replicas; ballot 0's leader is 0, its fast quorum {0, 1}. Replica 2
// becomes the leader of ballot 5 with the reports of {1, 2}: replica 1
// pre-accepted c in ballot 0 (no dependencies); replica 2 knows nothing of
// it. c must be in the MSync.
func TestIssueR1_FastPathCommandKept(t *testing.T) {
	r := newTestReplica(t, 3, 2, 5, false)
	r.status = RECOVERING
	c := cid(1, 0)
	cmd := state.Command{Op: state.PUT, K: 3, V: state.Value("c")}
	r.handleNewLeaderAckNs(nil, []interface{}{
		&MNewLeaderAckN{Replica: 2, Ballot: 5, Cballot: 0},
		&MNewLeaderAckN{Replica: 1, Ballot: 5, Cballot: 0, CmdIds: []CommandId{c},
			Phases: []int{PRE_ACCEPT}, Cmds: []state.Command{cmd}, Deps: []SDep{{Dep: []CommandId{}}}},
	})
	var sync *MSync
	for _, m := range sent(r) {
		if s, ok := m.(*MSync); ok {
			sync = s
		}
	}
	if sync == nil {
		t.Fatal("no MSync sent")
	}
	if _, ok := sync.Phases[c]; !ok {
		t.Fatalf("c, pre-accepted by the fast quorum's reporter, was dropped: %v", sync.Phases)
	}
}

// R1 (the client's side): the client's fast path must mean that the fast
// quorum pre-accepted the command with the leader's dependencies, the
// condition the recovery checks. It compared only the dependency paths'
// hashes, and equal paths do not give equal dependencies.
//
// The leader (replica 0) and replica 1 have the same path for c's key, but
// replica 1's dependencies for c differ (here: its key information lost p,
// as when its arrival order differs from the leader's). The hashes the
// leader's MReply and replica 1's MFastAckClient carry must differ.
func TestIssueR1_ClientHashesCoverDependencies(t *testing.T) {
	seqDescs(t)
	l := newTestReplica(t, 3, 0, 0, true)
	f := newTestReplica(t, 3, 1, 0, false)
	f.batcher = NewBatcher(f, 16, releaseFastAck, func(_ *MLightSlowAck) {})
	p, c := cid(1, 0), cid(2, 0)
	for _, r := range []*Replica{l, f} {
		propose(r, put(p, 3, "p"))
	}
	f.keys = make(map[state.Key]keyInfo)
	for _, r := range []*Replica{l, f} {
		propose(r, put(c, 3, "c"))
	}
	time.Sleep(100 * time.Millisecond)
	var reply *MReply
	for _, m := range sent(l) {
		if x, ok := m.(*MReply); ok && x.CmdId == c {
			reply = x
		}
	}
	var ack *MFastAckClient
	for _, m := range sent(f) {
		if x, ok := m.(*MFastAckClient); ok && x.CmdId == c {
			ack = x
		}
	}
	if reply == nil || ack == nil {
		t.Fatalf("reply %v, ack %v", reply, ack)
	}
	if SHashesEq(reply.Checksum, ack.Checksum) {
		t.Fatalf("equal client hashes with different dependencies")
	}
}
