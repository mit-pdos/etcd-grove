---
upstream: unchecked
---

# porcupine PR #46: a client's listed order is imposed on the linearization

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
chain the return times do not decrease (its exponential and binary searches find the first
operation that does not precede, and take all before it to precede).

What the PR decides, precisely (checked against a brute-force checker on 300000 random register
histories): linearizability by an order that respects real time *and* each client's listed order
(the proof's `LinearizableCO`), provided that along each client's listed order the returns do not
decrease. When a client's operations are sequential (each returns strictly before the next is
called) the two notions agree; otherwise the PR is incomplete (overlapping operations, or a
return at the same time as the next call) or, when a client's returns decrease, unsound.

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

Two more, same model:

- incomplete with a non-strict clock: client 0 lists `{read → 1, [0, 5]}, {write 1, [5, 6]}`
  (the read returns at the time the write is called; porcupine's intervals are closed, so they
  overlap): linearizable (write, then read), v1.3.1 `true`, the PR `false`. A tracer whose clock
  gives `ret_i ≤ call_{i+1}` (not `<`) meets this.
- unsound with decreasing returns: client 1 lists `{write 1, [0, 10]}, {write 2, [1, 2]}`,
  client 0 `{read → 0, [5, 6]}`: not linearizable (the read follows `write 2`), v1.3.1 `false`,
  the PR `true` (`computeFirstUnk` stops at `write 1`, which does not precede the read, and takes
  `write 2` not to precede it either).

The two tests above fail on the PR and pass on v1.3.1 (checked 2026-11-02 with copies of both side
by side; random small register histories agree with v1.3.1 whenever each client's
operations are sequential in the order listed, 200000 of them).

**Expected**: `ClientId` is documented as optional, and nothing says a client's operations
must not overlap or must be listed in time order (v1.3.1 sorts the entries by time itself).
Either the PR documents the precondition (each client's operations are sequential: listed
in order, each returning strictly before the next is called), or it does not depend on it.

**How the proof handles it**: the PR's specs have the premise that along each client's listed
order the returns do not decrease (`ClientsOk`, in
`PorcupineDag/Proof/github_com/anishathalye/porcupine/Defs.lean`), and say that the answer is
`true` exactly when the history is linearizable respecting the client order
(`LinearizableCO`), which implies linearizable. v1.3.1's statement (`true` exactly when
linearizable) is a corollary under the stronger condition that each client is sequential
(`ClientsSeq`: `ops[i].Return < ops[j].Call` for `i < j` of one client;
`notes/porcupine-dag-plan.md`, spec plan, "Premises").

**Possible fixes**: sort each chain by call time and split a client's overlapping operations
into separate chains (virtual clients); or check the precondition and fall back to one chain
per operation.

**Found**: 2026-11-02, while planning the specs of the PR's checker (the incompleteness was
known to the task; the unsoundness found by a random comparison with v1.3.1).
