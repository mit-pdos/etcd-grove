<!-- Issue for anishathalye/porcupine, to file by hand. Drafted 2026-10-23 against porcupine master's model.go. -->

Title: Docs: may Equal (or Step) change a state's representation without changing the state it represents?

`Model`'s documentation says models "are expected to be purely functional. That is, the model Step function should not modify the given state (or input or output), but return a new state", and `Step`'s says "it cannot mutate the given state". `Equal`, `Hash` and `DescribeState` have no such sentence.

etcd's robustness tests have a model that writes to its states in `Equal`: a state there is a slice that stands for a set of possible states, and `Equal` sorts both of its arguments in place before comparing them element by element ([`nonDeterministicState.Equal`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/tests/robustness/model/non_deterministic.go#L73-L86) in `tests/robustness/model/non_deterministic.go`; the model's `DescribeState` sorts its argument too). The sort changes the slice but not the set it stands for, and the model's `Step` treats the slice as a set, so as far as I can tell no check result changes. Read literally, though, the model-level sentence forbids it, and it would race if two partitions' checks shared a state value (etcd's `Init` returns a fresh slice, so they do not).

Could the documentation say which of these is intended?

1. `Step` (and `StepContext`), `Equal`, `Hash` and `DescribeState` must not write to their arguments at all; or
2. they may change a state's representation (normalizing, sorting, caching) as long as the state it represents, as later `Equal`, `Hash` and `Step` calls see it, stays the same, and no state value is shared between partitions, since partitions are checked concurrently.

Either is fine for etcd: if (1), etcd's model can sort copies. Knowing which one is intended tells model authors, and people reasoning about the checker, what porcupine relies on. (#11 is where the "purely functional" sentence came from, for a `Step` that mutated its state.)

Found while formally verifying porcupine's checker and etcd's use of it. Written with the assistance of generative AI; I reviewed it.
