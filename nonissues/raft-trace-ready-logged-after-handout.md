---
upstream: none
checked: 2026-11-08
links: []
blocks-proof: no
---
# raft: the `with_tla` build logs a `Ready` after handing it out, so a receipt can precede it in the trace

In the `with_tla` build, `traceReady` is the last statement of `RawNode.acceptReady`
(`rawnode.go:437`), which `node.run` calls after the `Ready` has gone over `readyc`
(`node.go:435-436`). An application that sends the `Ready`'s messages at once (as etcd does, before
`Advance`) can have one received, and its receipt logged by the recipient, before the sender's
`Ready` line; `Traceetcdraft.tla` then rejects the trace, since `Ready(i)` is what moves a message
from `pendingMessages` to `messages`, where `Receive` looks for it.

**Why not an issue:** the trace instrumentation's event order, not raft's behavior; no failing test
against upstream's own trace validation (found by the review of Draft S4, witnessed in a scratch
copy of this repository's concurrent harness with a 20ms sleep between the hand-off and
`acceptReady`: `notes/trace-validation-sim.md`, round 1's F1).

## Proof

no: the trace-check harness sends a `Ready`'s messages after `Advance`, which the run loop takes
only after `acceptReady` has logged the `Ready` (`examples/raft/tracecheck/concurrent.go`, `app`).

## Notes

Upstream's trace validation of etcd's robustness tests could hit it (etcd sends before
`Advance`); logging the `Ready` before the hand-off (in `node.run`, or `traceReady` before
`readyc <-`) would remove the window.

The places where upstream's TLA+ specification and trace validation do not fit raft, each with a
test at upstream `main`, are the `issues/raft-tla-*` files (2026-11-08); this one stays here: it
needs a timing window inside `Node`'s run loop that no test can open without changing raft.
