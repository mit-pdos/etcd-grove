---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#22526 issue open: this bug (the reporter's reproduction: 24,537-27,720 warnings in about 3 s)
  - etcd-io/etcd#22527 pr open: the fix, a wait on `applyWait` after the rejection (verified on branch `pr-verify/etcd-22527`)
  - etcd-io/etcd#22516 issue open: related, not this bug (`s.appliedIndex` stale after a snapshot; with it, the PR's wait ends at once)
---

# etcdserver: `publishV3` retries a "too many requests" rejection in a tight loop

- **Status**: a bug (a busy loop that floods the log), known upstream; not a safety bug.
- **Where**: `server/etcdserver/server.go:1793-1843` (`publishV3`) at the pinned revision
  (`09669450f`): on any error of `s.raftRequest`, it logs a warning and retries at once;
  `v3_server.go:1063` (`processInternalRaftRequestOnce`) rejects a proposal at once with
  `ErrTooManyRequests` while the committed index is more than 5000 past `s.appliedIndex`
  (`exceedsRequestLimit`, `util.go:60`).
- **What happens**: a member far behind (a new member installing a leader snapshot, a slow
  apply) retries its publish thousands of times a second until its apply catches up, one warning
  each. Reproduction: `notes/pr-verify/etcd-22527/server_publish_probe_test.go`,
  `TestPublishV3ProbeTimeoutRetries`, which on the upstream base `91703b3d4` logs 5632 rejections
  in 200 ms with a 20 ms publish timeout (`notes/pr-verify/etcd-22527/tests-base.log`).
- **Expected**: after a rejection, wait for the apply to catch up (or the timeout, or the stop).
- **How the proof handles it**: on `lean`, `publishV3` is names-only (an axiom, "returns"); a
  partial-correctness spec cannot state the absence of a busy loop. Branch `pr-verify/etcd-22527`
  translates and proves `publishV3` with the PR's wait.
- **Possible fixes**: etcd-io/etcd#22527 (with #22510 for the snapshot case).
- **Found**: 2026-10-17, while verifying etcd-io/etcd#22527 (`pr-verify/etcd-22527`).
