# Issues found by the verification

Drafts of the issues to file against etcd-io/etcd, one per finding, as the verification found
them (the proofs state what the code does; a finding is a behaviour the specs could not hide).
Each draft names the upstream revision it refers to, how to reproduce it (a test on the fix
branch) and the fix. The fix branches are on the fork `upamanyus/etcd`, one signed-off commit
each off upstream `main` (f061acd09), with the tests; the issues and pull requests are filed by
hand from them. A finding that is not a bug (a documentation request) has no fix branch.

| Draft | Kind | Fork branch | Found in |
|---|---|---|---|
| [cache-ready-after-retry](cache-ready-after-retry.md) | bug | `cache-ready-after-retry` (64313a1f8) | `cache` (STATUS "The whole package") |
| [mutex-lock-recreated](mutex-lock-recreated.md) | bug | `mutex-lock-recreated` (113b0b324) | `concurrency` (Mutex) |
| [election-campaign-key-check](election-campaign-key-check.md) | bug | `election-campaign-key-check` (bb50d33b8) | `concurrency` (Election) |
| [stm-serializable-snapshot](stm-serializable-snapshot.md) | documentation | none (`stm-serializable-snapshot` kept local, not proposed) | `concurrency` (STM) |
| [leasing-evictrange-key](leasing-evictrange-key.md) | bug | `leasing-evictrange-key` (14d1c4bf3) | `leasing` (units 1–2) |
| [leasing-evalcmp-missing-key](leasing-evalcmp-missing-key.md) | bug | `leasing-evalcmp-missing-key` (06541aec6) | `leasing` (units 1–2) |
| [leasing-modify-uncached-once](leasing-modify-uncached-once.md) | bug | `leasing-modify-uncached-once` (7a6077dec) | `leasing` (units 3–4) |
| [leasing-get-failed-acquire-options](leasing-get-failed-acquire-options.md) | bug | `leasing-get-failed-acquire-options` (af95e2ff8) | `leasing` (units 3–4) |

Findings without a draft yet (`notes/STATUS.md`, the leasing sections): the `Update` family
(`WithIgnoreValue` caching the empty value, the lease never updated, out-of-order updates of
concurrent puts: one issue, with Go reproductions, once unit 5 settles the monitors' part);
`waitRescind` returning `nil` without a delete event and an entry carrying an old session's
lease (to be confirmed by unit 5); `gatherOps` appending into the caller's nested `OpTxn`
slice (a race only for callers who reuse the slice; assessed, not filed).
