---
upstream: unchecked
---

# porcupine PR #46: a negative or huge `ClientId` panics

**Status**: a reachable panic in an unmerged pull request (anishathalye/porcupine#46, head
`29a6b8e6c` of `practical-systems-iitd/porcupine`): an unstated precondition on
`Operation.ClientId`. Porcupine v1.3.1 never indexes by `ClientId` (it is only for the
visualizer) and accepts any value. Recorded here although the PR is unmerged, at the request
of the task that verified it (`notes/porcupine-dag-plan.md`).

**Where** (`third_party/porcupine-dag`): `checkOperations` (`checker.go`) takes
`numClients = maxClientId + 1` over the history; `makeEntries` indexes
`operationHistory[elem.ClientId]`; `newChains` (`dag.go`) allocates
`make([]int, n*numClients)` and slices it at `id*numClients`.

**What happens**:

- a negative `ClientId`: `index out of range [-1]` in `makeEntries`;
- `ClientId = math.MaxInt`: `maxClientId + 1` overflows to a negative length, and `make`
  panics (`len out of range`);
- `(maxClientId + 1) * n` beyond `math.MaxInt` overflows in `newChains`; and short of that, a
  large sparse `ClientId` allocates `n * (maxClientId + 1)` integers (a single operation with
  `ClientId` 2^40 asks for 8 TiB).

```go
func TestNegativeClientId(t *testing.T) {
	h := []Operation{{ClientId: -1, Input: regIn{true, 1}, Output: 0, Call: 0, Return: 1}}
	CheckOperations(reg, h) // panics: index out of range [-1]
}
```

(`reg`, `regIn` as in `issues/porcupine-dag-client-order.md`.)

**Expected**: `ClientId` is documented as optional (any value, as v1.3.1 accepts).

**How the proof handles it**: a premise of the PR's specs (`ClientsOk`, in
`PorcupineDag/Proof/github_com/anishathalye/porcupine/Defs.lean`): every `ClientId` is
non-negative and `(ClientId + 1) * len(history) < 2^63`. (The model has no memory limit, so
the allocation size is not a premise.)

**Possible fixes**: renumber the client ids densely (a map from `ClientId` to `0..k-1`)
before building the chains.

**Found**: 2026-11-02, while planning the specs of the PR's checker.
