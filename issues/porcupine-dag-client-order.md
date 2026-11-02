---
upstream: unchecked
---

# porcupine PR #46: a client's operations must be sequential and listed in real-time order

**Status**: a bug in an unmerged pull request (anishathalye/porcupine#46, "Support
system-specific consistency models via DAG-based execution", head `29a6b8e6c` of
`practical-systems-iitd/porcupine`): an unstated precondition on the history, without which
`CheckOperations` both rejects linearizable histories (incomplete) and accepts
non-linearizable ones (unsound). Porcupine v1.3.1 has neither problem, and documents
`Operation.ClientId` as "optional, unless you want a visualization", which the PR keeps.
Recorded here although the PR is unmerged, at the request of the task that verified it
(`notes/porcupine-dag-plan.md`).

**Where** (`third_party/porcupine-dag`, the PR vendored): `makeEntries` (`checker.go`) puts
the operations of one `ClientId` into one chain, in the order the history lists them; the
search (`dag.go`, `client.lift`) linearizes a chain only in that order (`head` moves forward
one operation at a time), and the dependency search (`computeFirstUnk`) assumes that along a
chain both the call and the return times increase (its exponential and binary searches, and
its start from the previous operation's bound).

**What happens**: with a register model (`Init` 0, a write sets the value, a read must
return it), both operations with `ClientId` 0 (the default):

- incomplete: `{read → 1, [0, 10]}, {write 1, [1, 5]}` (the read listed first) is
  linearizable (write, then read) and v1.3.1 returns `true`; the PR returns `false`, because
  the read must be linearized first. With distinct client ids both return `true`.
- unsound: `{read → 0, [2, 3]}, {write 1, [0, 1]}` (the read listed first) is not
  linearizable (the write returns before the read is called, so the read must see 1) and
  v1.3.1 returns `false`; the PR returns `true`, linearizing the read before the write.

```go
package porcupine

import "testing"

type regIn struct {
	w bool
	v int
}

var reg = Model{
	Init: func() interface{} { return 0 },
	Step: func(s, i, o interface{}) (bool, interface{}) {
		in := i.(regIn)
		if in.w {
			return true, in.v
		}
		return o.(int) == s.(int), s
	},
	Equal: func(a, b interface{}) bool { return a == b },
}

func TestSameClientOverlap(t *testing.T) {
	h := []Operation{
		{Input: regIn{false, 0}, Output: 1, Call: 0, Return: 10},
		{Input: regIn{true, 1}, Output: 0, Call: 1, Return: 5},
	}
	if !CheckOperations(reg, h) { // linearizable: write, then read
		t.Error("linearizable history rejected (same ClientId, overlapping)")
	}
}

func TestSameClientOutOfOrder(t *testing.T) {
	h := []Operation{
		{Input: regIn{false, 0}, Output: 0, Call: 2, Return: 3},
		{Input: regIn{true, 1}, Output: 0, Call: 0, Return: 1},
	}
	if CheckOperations(reg, h) { // the read follows the write in real time, must see 1
		t.Error("non-linearizable history accepted (same ClientId, listed out of order)")
	}
}
```

Both tests fail on the PR and pass on v1.3.1 (checked 2026-11-02 with copies of both side
by side; random small register histories agree with v1.3.1 whenever each client's
operations are sequential in the order listed, 200000 of them).

**Expected**: `ClientId` is documented as optional, and nothing says a client's operations
must not overlap or must be listed in time order (v1.3.1 sorts the entries by time itself).
Either the PR documents the precondition (each client's operations are sequential: listed
in order, each returning strictly before the next is called), or it does not depend on it.

**How the proof handles it**: a premise of the PR's specs (`ClientsOk`, in
`PorcupineDag/Proof/github_com/anishathalye/porcupine/Defs.lean`): for operations `i < j`
of the history with the same `ClientId`, `ops[i].Return < ops[j].Call`. The premise is also
what makes the dependency search exact (`notes/porcupine-dag-plan.md`, spec plan, "Premises").

**Possible fixes**: sort each chain by call time and split a client's overlapping operations
into separate chains (virtual clients); or check the precondition and fall back to one chain
per operation.

**Found**: 2026-11-02, while planning the specs of the PR's checker (the incompleteness was
known to the task; the unsoundness found by a random comparison with v1.3.1).
