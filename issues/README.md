# Issues found while verifying

One file per issue found in the verified Go code (raft, etcd, their dependencies) or its
documentation: a bug (a reachable panic or wrong result), a precondition the code needs
but its API does not state, or documentation the code contradicts. Not for bugs in this
repository's own specs and proofs (those go in `notes/`).

Name a file `<project>-<short-slug>.md` and give it:

- **Status**: open / reported (link) / fixed upstream (commit) / not a bug (why).
- **Where**: the Go code (file:line at the pinned revision in `etc/goose.py`) and the
  documentation involved.
- **What happens**: the behavior, with a reproduction (a Go test, inline or by path) when
  one exists.
- **Expected**: what the documentation or API promises instead.
- **How the proof handles it**: the premise, spec or scope choice that keeps it out of the
  verified results (file:line).
- **Possible fixes**.
- **Found**: date and by what (which proof or check).

## Drafts for etcd-io/etcd

The findings of the etcd client-side work (cache, concurrency, leasing, recipes) are written as
drafts of the issues to file against etcd-io/etcd, one per finding (the proofs state what the
code does; a finding is a behaviour the specs could not hide): each names the upstream revision
it refers to, how to reproduce it (a test on the fix branch) and the fix. The fix branches are
on the fork `upamanyus/etcd`, one signed-off commit each off upstream `main` (f061acd09), with
the tests; the issues and pull requests are filed by hand from them. A finding that is not a bug
(a documentation request) has no fix branch. A draft covers the fields above in its own order
(summary, what happens, how to reproduce, expected, the fix); "How the proof handles it" is in
`notes/STATUS.md`'s section for the package.

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
| [leasing-wait-rescind-no-delete](leasing-wait-rescind-no-delete.md) | bug | `leasing-wait-rescind-no-delete` (d3db62afd) | `leasing` (unit 5) |
| [leasing-stale-entry-after-reset](leasing-stale-entry-after-reset.md) | bug | `leasing-stale-entry-after-reset` (3d0769edc) | `leasing` (unit 5) |
| [leasing-update-stale](leasing-update-stale.md) | bug | `leasing-update-stale` (d97e455c2) | `leasing` (units 3–5) |
| [recipes-dequeue-closed-watch](recipes-dequeue-closed-watch.md) | bug | `recipes-closed-watch-channel` (0aa6c6af8) | recipes, 2026-10-11 |
| [recipes-barrier-wait-closed-watch](recipes-barrier-wait-closed-watch.md) | bug | `recipes-closed-watch-channel` (0aa6c6af8) | recipes, 2026-10-11 |
| [raft-zero-max-size-per-msg](raft-zero-max-size-per-msg.md) | bug | none (etcd-io/raft; the format of the list above) | `raft` |

Findings without a draft yet (`notes/STATUS.md`, the leasing sections): `gatherOps` appending
into the caller's nested `OpTxn` slice (a race only for callers who reuse the slice; assessed,
not filed).
