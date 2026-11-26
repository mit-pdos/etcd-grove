---
upstream: none
checked: 2026-11-25
links: []
blocks-proof: no
---

# etcd-grove `examples/etcd/dist/client`: a `kv` workload calls `ready` twice, though `MainReady`'s doc says once

`MainReady`'s doc: "ready is called once the workload's set-up is done (at once for a workload with
none), or not at all if the workload ends before". For a `kv` workload (no set-up, `hasSetUp(KV)`
false) `MainReady` calls `ready()` before its switch, and `RunKV` calls `ready()` again as its first
statement: two calls.

**Why not an issue:** this repository's own example code, documentation only: `ready` is an
observer (the doc: "nothing the workload does depends on it"), and its only non-trivial caller,
`examples/etcd/dist/run.go`, writes the same ready file each time (idempotent). Either `RunKV` should
not call `ready` (as `RunCompact`, `RunPutGet` do not), or the doc should say "at least once".

## Proof

no: `readySpec` (`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/KvDefs.lean`) is
persistent (a `ready` safe to call any number of times), which both calls use.

## Notes

Found by the N7-kv spec review (2026-11-25, `notes/etcd-dist-n7kv.md`).
