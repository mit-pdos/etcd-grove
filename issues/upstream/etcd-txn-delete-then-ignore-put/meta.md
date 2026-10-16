# etcd-txn-delete-then-ignore-put

- **Finding**: `issues/etcd-txn-delete-then-ignore-put.md`
- **Target**: etcd-io/etcd `main`; affected also `release-3.6`, `release-3.5`, `release-3.4` (same `checkIntervals` and
  `IgnoreValue` code; not run there)
- **Base checked**: upstream `main` ea8b59433d82e8fc3f1365618740395e0028bd03 (2026-10-16)
- **State**: blocked — security triage (step 3); the user decides how to report. No fix branch, no public text.
- **Upstream issue / PR**: root cause already public, see below.

## Upstream status (2026-10-16)

- **#22395** (open PR, youdie006, 2026-09-08, `ok-to-test`, not reviewed, no lgtm): "server/etcdserver: detect txn
  overlap for open-ended delete ranges" — the same `checkIntervals` change as the finding's fix. Says "This is not a
  security fix ... the same effect is reachable with two separate calls": it does not know about the panic.
- **#22445** (issue) / **#22446** (PR), omar-3, 2026-09-18: the same root cause, closed as duplicates of #22395.
- Neither mentions `IgnoreValue`/`IgnoreLease`, a panic, or the restart loop.

## Probes (integration tests, 1-member cluster, `put a v` then the txn)

| Txn | `main` | #22395 (eb347e2b4) |
|---|---|---|
| `del(a, FromKey)`, `put(a, IgnoreValue)` | panic | rejected (duplicate key) |
| `del(a, FromKey)`, `put(a, IgnoreLease)` | panic | rejected |
| `del(0, FromKey)`, `put(a, IgnoreValue)` | panic | rejected |
| `del("", Prefix)` (all keys), `put(a, IgnoreValue)` | panic | rejected |
| `del(a, FromKey)`, `txn(put(a, IgnoreValue))` | panic | rejected |
| `txn(del(a, FromKey))`, `put(a, IgnoreValue)` | panic | rejected |
| `txn(del(a))`, `txn(put(a, IgnoreValue))` | — | rejected |
| `txn(txn(del(a, FromKey)))`, `put(a, IgnoreValue)` | — | rejected |
| `txn(del(0, FromKey))`, `txn(txn(put(a, IgnoreLease)))` | — | rejected |
| `txn(put(a, IgnoreValue))`, `txn(del(a))` | — | accepted, no panic (`etcd-txn-check-intervals-sibling`) |
| `del(a, Range b)`, `put(a, IgnoreValue)` (control) | rejected | rejected |

No variant found that crashes with #22395 applied. Restart loop: from the finding (1- and 3-member clusters, every
member re-panics on restart); not rerun at ea8b59433.

## Options for the user

1. Private report through the GitHub security advisory form (etcd's `security/README.md`), pointing at #22395 as the
   fix and asking for review and backports to 3.4–3.6.
2. Leave it to #22395 (no report).
3. Public comment on #22395 — discloses a one-request permanent outage before a fix is released.
