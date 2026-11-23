package swift

import (
	"testing"

	"github.com/imdea-software/swiftpaxos/state"
)

// reaches says whether to is reachable from from through deps.
func reaches(deps map[CommandId]Dep, from, to CommandId) bool {
	seen := map[CommandId]bool{}
	stack := []CommandId{from}
	for len(stack) > 0 {
		x := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		for _, y := range deps[x] {
			if y == to {
				return true
			}
			if !seen[y] {
				seen[y] = true
				stack = append(stack, y)
			}
		}
	}
	return false
}

// S2: every two conflicting commands are ordered by the dependencies (the
// paper's Invariant 2). A write depended only on the key's last command: a
// read received before it but not last was ordered with it neither way.
//
// put p1, get g1, get g2, put p2 of one key: p2 must come after g1 and g2.
func TestIssueS2_WriteAfterEveryRead(t *testing.T) {
	r := newTestReplica(t, 3, 1, 0, false)
	p1, g1, g2, p2 := cid(1, 0), cid(2, 0), cid(3, 0), cid(4, 0)
	deps := map[CommandId]Dep{}
	for _, x := range []struct {
		id CommandId
		op state.Operation
	}{{p1, state.PUT}, {g1, state.GET}, {g2, state.GET}, {p2, state.PUT}} {
		d, _ := r.getDepAndHashes(state.Command{Op: x.op, K: 1, V: state.NIL()}, x.id)
		deps[x.id] = d
	}
	for _, g := range []CommandId{g1, g2} {
		if !reaches(deps, p2, g) && !reaches(deps, g, p2) {
			t.Errorf("put %v and get %v are not ordered: %v", p2, g, deps)
		}
	}
	if !reaches(deps, g1, p1) || !reaches(deps, p2, p1) {
		t.Errorf("p1 must precede: %v", deps)
	}
}
