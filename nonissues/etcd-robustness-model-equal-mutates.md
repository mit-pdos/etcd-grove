---
upstream: none
checked: 2026-10-26
links:
  - anishathalye/porcupine#11 issue closed: related, not this bug (a user's Step mutated its state; the origin of the documented "purely functional" model contract)
blocks-proof: no
---

# tests/robustness: the porcupine model's `Equal` (and `DescribeState`) sorts its states in place

`nonDeterministicState.Equal` in etcd's robustness tests sorts both of its arguments in place before
comparing them, and the model's `DescribeState` sorts its argument too, while porcupine's
documentation says a model should not modify the states it is given.

**Why not an issue:** test code only, and harmless: a state stands for a set of possible etcd
states, `Step` treats it as one, so the reordering changes no verdict; no state value is shared
between partitions (each starts from a fresh `Init()`), so it is no data race either.

## Proof

no: the porcupine proof's model premise does not need a persistent representation (`equalSpec`
gives back the same abstract states; `Proof/github_com/anishathalye/porcupine/Defs.lean`), so an
`Equal` that sorts meets it.

## Notes

Test: `TestNonDeterministicEqualMutatesArguments` in
[`etcd-robustness-model-equal-mutates/equal_mutates_test.go`](etcd-robustness-model-equal-mutates/equal_mutates_test.go)
(package `model`, `tests/robustness/model`) fails at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-11-01): `Equal reordered its
arguments`. The INDEX-reviewed Plan: if anything, ask porcupine to say whether `Equal`/`Step` may
change a state's representation without changing the state it represents. A drafted question for
anishathalye/porcupine (not filed) asked which is intended: (1) no writes to arguments at all, or
(2) representation changes (normalizing, sorting, caching) allowed as long as the represented
state stays the same and no state value is shared between partitions, since they are checked
concurrently. etcd's side: sort copies (`slices.Clone`), or keep states sorted where `apply`
builds them.
