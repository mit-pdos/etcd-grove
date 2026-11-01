---
upstream: none
checked: 2026-10-16
links: []
blocks-proof: no
---

# apply: the apply-duration metric labels an `AuthStatus` request `op="unknown"`

`uberApplier.dispatch` sets `op` to the request's name in every case but `AuthStatus`, so the
apply time of an `AuthStatus` entry is recorded in `etcd_server_apply_duration_seconds` under
`op="unknown"`, the label meant for a request it does not know.

**Why not an issue:** no test, found by code reading (a metric label only).

## Proof

no: a metric; `dispatch`'s spec says the deferred metrics return, with any `op`.

## Notes

A test applying `InternalRaftRequest{AuthStatus: ...}` through `NewUberApplier(...).Apply` and
reading the histogram's labels would promote it to `issues/`; the fix is `op = "AuthStatus"` in the
case. INDEX-reviewed.md's plan: skip for now.
