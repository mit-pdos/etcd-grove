package swift

import (
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos/state"
)

func storeGet(r *Replica, k int64) string {
	return string((&state.Command{Op: state.GET, K: state.Key(k)}).Execute(r.State))
}

// S5: the old leader's optimistic execution must not survive a new ballot
// that orders the command differently or drops it (the paper keeps the
// speculative execution apart from the committed state).
//
// Replica 0, the leader of ballot 0, executes put c (k=6, "x") when it
// proposes it. A new leader's MSync of ballot 4 does not have c (it was not
// chosen): replica 0's store must not have c's write.
func TestIssueS5_OptimisticExecutionUndone(t *testing.T) {
	seqDescs(t)
	r := newTestReplica(t, 3, 0, 0, true)
	c := cid(1, 0)
	propose(r, put(c, 6, "x"))
	if storeGet(r, 6) != "x" {
		t.Fatal("the leader did not execute c optimistically")
	}
	r.handleSync(&MSync{Replica: 1, Ballot: 4, Phases: map[CommandId]int{},
		Cmds: map[CommandId]state.Command{}, Deps: map[CommandId]Dep{}})
	if v := storeGet(r, 6); v == "x" {
		t.Fatalf("the store has c's write after an MSync without c")
	}
}

// R5: after an MSync, the replicas order the recovered commands one way, and
// a command proposed in the new ballot comes after the recovered commands of
// its key. handleSync sorted with a comparator that is not a strict weak
// order, and emptied the key dependencies: a new write did not depend on the
// recovered ones (two replicas could execute the two in either order).
func TestIssueR5_NewCommandsAfterRecovered(t *testing.T) {
	seqDescs(t)
	r := newTestReplica(t, 3, 2, 0, false)
	r.status = RECOVERING
	r.ballot = 4
	c, d := cid(1, 0), cid(2, 0)
	r.handleSync(&MSync{Replica: 1, Ballot: 4,
		Phases: map[CommandId]int{c: COMMIT},
		Cmds:   map[CommandId]state.Command{c: {Op: state.PUT, K: 6, V: state.Value("c")}},
		Deps:   map[CommandId]Dep{c: {}}})
	propose(r, put(d, 6, "d"))
	desc := r.getCmdDesc(d, nil, nil)
	if desc == nil || !desc.proposeDep.Equals(Dep{c}) {
		t.Fatalf("d's dependencies %v, want {c}", desc.proposeDep)
	}
}

// S6, C2: after an MSync, no client gets an answer without a result. The new
// leader answered each recovered command it was proposed with an MReply
// without Rep, and every replica each proposal the MSync lacks with an
// MAccept without Rep, which the client takes as the reply (a get "not
// found" after a completed put).
//
// Replica 1 becomes the leader of ballot 4: the MSync has put p (k=6, "v")
// then get g; replica 1 was proposed g, and x, which the MSync lacks.
func TestIssueS6_RepliesWithResults(t *testing.T) {
	seqDescs(t)
	r := newTestReplica(t, 3, 1, 0, true)
	p, g, x := cid(1, 0), cid(2, 0), cid(3, 0)
	propose(r, get(g, 6))
	propose(r, put(x, 7, "x"))
	sent(r)
	r.status = RECOVERING
	r.repchan.stop()
	r.ballot = 4
	r.handleSync(&MSync{Replica: 1, Ballot: 4,
		Phases: map[CommandId]int{p: COMMIT, g: COMMIT},
		Cmds: map[CommandId]state.Command{p: {Op: state.PUT, K: 6, V: state.Value("v")},
			g: {Op: state.GET, K: 6, V: state.NIL()}},
		Deps: map[CommandId]Dep{p: {}, g: {p}}})
	time.Sleep(100 * time.Millisecond)
	gotG := false
	for _, m := range sent(r) {
		switch m := m.(type) {
		case *MReply:
			if m.CmdId == g {
				if string(m.Rep) != "v" {
					t.Errorf("MReply for g with result %q, want \"v\"", m.Rep)
				}
				gotG = true
			}
		case *MAccept:
			t.Errorf("MAccept for %v (result %q)", m.CmdId, m.Rep)
		}
	}
	if !gotG {
		t.Errorf("no MReply for g")
	}
}
