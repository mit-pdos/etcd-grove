---
upstream: none
checked: 2026-11-17
links:
  - kubernetes/kubernetes#141652 issue open: the tracking issue of the model-based correctness tests (watch validation)
blocks-proof: no
---

# k8s correctness.WatchValidator rejects a watch-list the consumer stopped reading before its initial-events-end bookmark

`WatchValidator.ValidateWatch` (`apiserver/pkg/storage/testing/correctness/watch.go`,
`splitInitialEvents`) rejects a `SendInitialEvents=true` watch whose recorded events hold initial
events but no initial-events-end bookmark ("missing initial events end bookmark"). It accepts only
the case with no events at all. `TestCorrectness`'s harness (`runWatch` in
`test/integration/apiserver/storage/traffic.go`) can produce exactly that response from a correct
store: its `timer.C` (the watch's `Duration`) and `MaxEvents` are checked while the initial events
are still being read, and a `watch.Error` ends the read too. So a slow run, or a larger initial
list than the test's four objects, makes the test fail on a correct store.

**Why not an issue:** a test helper's latent flake. With the test's four objects and 500 ms
duration the initial events arrive at once, and no failure is reported upstream. Found by code
reading, at master of 2026-10-21 (`k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038`).
Shown with the validator on hand-made events (`TestValidatorDepartures` in
`notes/k8s-7g-experiment.patch`: "cut before the bookmark" is rejected).

## Proof

no: the driver's own check accepts such a watch if its events are a prefix of the initial events at
some revision (the 7f Scope's departure 2). Stage 7g gives the maintainers' validator that watch
with no events (departure D7g-3, `notes/k8s-7g-scope.md` §1.4).

## Notes

Fix: in `splitInitialEvents`, accept a stream with no bookmark when its events are a prefix of the
initial events at some revision the replay knows (or when the response says the watch was cut).
Alternatively, have the harness read until the bookmark before honouring the timer.
