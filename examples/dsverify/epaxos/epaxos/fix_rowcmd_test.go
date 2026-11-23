package epaxos

import (
	"testing"

	"github.com/imdea-software/swiftpaxos-epaxos/state"
)

// TestPreAcceptStoresCommandsInItsInstance: replica 2 holds 1.0 ACCEPTED without commands and
// receives a PreAccept for 1.0 from a recovering replica 3. handlePreAccept must store the
// commands in 1.0 (InstanceSpace[Replica]), not in 3.0 (InstanceSpace[LeaderId]): the parent
// dereferences the nil 3.0 and panics. The state (ACCEPTED, no commands) is built by hand: no
// handler of this code reaches it (every path that sets a status >= ACCEPTED also sets non-nil
// commands), so this test documents the verification workaround, not a reachable failure.
func TestPreAcceptStoresCommandsInItsInstance(t *testing.T) {
	c := newCluster(t, 5)
	r := c.r[2]
	in := r.newInstanceDefault(1, 0)
	in.Status = ACCEPTED
	in.Seq, in.Deps = 0, r.newNilDeps()
	r.InstanceSpace[1][0] = in
	r.crtInstance[1] = 0
	pa := &PreAccept{LeaderId: 3, Replica: 1, Instance: 0, Ballot: 8, Command: []state.Command{put(1, "a")}, Seq: 0, Deps: r.newNilDeps()}
	func() {
		defer func() {
			if e := recover(); e != nil {
				t.Fatalf("handlePreAccept panicked: %v", e)
			}
		}()
		r.handlePreAccept(pa)
	}()
	if !sameCmds(r.InstanceSpace[1][0].Cmds, pa.Command) {
		t.Fatalf("1.0 at replica 2 has commands %s", cmdsString(r.InstanceSpace[1][0].Cmds))
	}
	if r.InstanceSpace[3][0] != nil {
		t.Fatalf("3.0 at replica 2 was written")
	}
}
