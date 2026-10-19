---
upstream: unchecked
---

# etcd's robustness model sorts its states in place in `Equal` (and `DescribeState`)

**Status**: a documentation-contract violation in etcd's test code (its robustness tests' porcupine
model), harmless in practice as far as known; the porcupine proof's model premise admits it
(below).

**Where** (etcd, the fork pinned in `etc/goose.py`, `8a24be2a3`; the file is upstream's):

- `tests/robustness/model/non_deterministic.go:73-86`, `nonDeterministicState.Equal`: sorts both
  of its arguments in place (`slices.SortFunc(states, compareStates)`,
  `slices.SortFunc(other, compareStates)`, lines 77-78) before comparing them element by
  element. `NonDeterministicModel`'s `Equal` (line 39) calls it on the two states porcupine
  passes.
- `tests/robustness/model/non_deterministic.go:51-55`, `NonDeterministicModel`'s
  `DescribeState`: sorts the state passed to it in place too.
- porcupine's documentation (`third_party/porcupine/model.go:81-83`, v1.3.1, the version etcd's
  `tests/go.mod` pins): "models in this package are expected to be purely functional. That is,
  the model Step function should not modify the given state (or input or output), but return a
  new state."

**What happens**: porcupine's checker (`checkSingle`) keeps state values in its backtracking
stack (`calls[i].state`) and in its memo cache (`cacheEntry.state`); the same value can be in
both, and be passed again to `StepContext` and `Equal` later. Each `Equal` call
(`cacheContains`) reorders the backing arrays of a cached state and of the new state. A
`nonDeterministicState` denotes a set of possible `EtcdState`s, and `StepContext` (`apply`)
treats it as one (it maps over the states and merges or filters them), so the reordering changes
no verdict as far as we can tell: the behavior is the same, the contract is not met.

It is not a data race, even with partitions (the model defines none, and could not sensibly:
revisions are global): each partition's goroutine starts from its own `Init()` (a fresh slice,
`freshEtcdState(keys)`) and `apply` returns fresh slices, so the slices `Equal` sorts are never
shared between goroutines. It would race only for a model whose `Init` returned a shared value.
(`DescribeState` runs in the visualizer, after the check.)

Reproduction (a test in `tests/robustness/model`, fails at the pin):

```go
package model

import "testing"

// Equal sorts both of its arguments in place, against porcupine's contract that a model does
// not modify the states it is given.
func TestNonDeterministicEqualMutatesArguments(t *testing.T) {
	a := nonDeterministicState{{Revision: 2}, {Revision: 1}}
	b := nonDeterministicState{{Revision: 2}, {Revision: 1}}
	if !a.Equal(b) {
		t.Fatalf("expected equal states")
	}
	if a[0].Revision != 2 || b[0].Revision != 2 {
		t.Errorf("Equal reordered its arguments: a = %v, b = %v", a, b)
	}
}
```

```
--- FAIL: TestNonDeterministicEqualMutatesArguments (0.00s)
    equal_mutates_test.go:14: Equal reordered its arguments: a = [{1 0 [] [] [] []} {2 0 [] [] [] []}], b = [{1 0 [] [] [] []} {2 0 [] [] [] []}]
```

**Expected**: `Equal` (and `DescribeState`) leave their arguments unchanged, as porcupine's
model contract says.

**How the proof handles it** (2026-10-19): the porcupine proof's model premise `isModel`
(`Proof/github_com/anishathalye/porcupine/Defs.lean`) does not ask for a persistent state
representation: `ModelSpec.rep` is any predicate, and each closure spec takes the `rep`s it reads
and gives them back, of the same abstract states; `equalSpec` is
`{{ S.rep v s ∗ S.rep w t }} Equal(v, w) {{ b, S.rep v s ∗ S.rep w t ∗ ⌜b = true → s = t⌝ }}`,
so an `Equal` that writes to its arguments meets it when the write keeps what they denote: for
etcd, `rep v s` would say the slice holds some ordering of the set `s`, which a sort keeps. The
checker, which aliases a state between its stack, its cache and its current state, shares each
state value in a non-atomic invariant and opens it for each call
(`Proof/github_com/anishathalye/porcupine/Shared.lean`). etcd's model itself is not verified
against these premises (`notes/STATUS.md`, "Porcupine").

**Possible fixes**:

- etcd: sort copies (`slices.Clone` first, or `slices.SortedFunc(slices.Values(states),
  compareStates)`) in `Equal` and `DescribeState`; or keep `nonDeterministicState` sorted as an
  invariant (sort once where a state is built, in `apply`) and compare without sorting.
- proof (done, 2026-10-19): owned, non-persistent state representations, shared by the checker
  through non-atomic invariants (above); what is left is a proof of etcd's model against them.

**Found**: 2026-10-14, while matching the porcupine proof's model premises against etcd's
robustness model (`notes/STATUS.md`, "Porcupine").
