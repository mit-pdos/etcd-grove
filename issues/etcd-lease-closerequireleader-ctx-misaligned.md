---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#22081 issue open: this issue
  - etcd-io/etcd#22087 pr open: fix (`ka.ctxs[i]` for `ka.ctxs[newIdx]`)
  - etcd-io/etcd#22291 pr open: does not fix it; with it, the second leader loss also deletes the entry, so the plain subscriber's lease stops being renewed
---

# client/v3: closeRequireLeader pairs a kept channel with another subscriber's context

- **Status**: a bug (a subscriber that did not ask for a leader gets its keep-alive channel
  closed, and with etcd-io/etcd#22291 its lease stops being renewed).
- **Where**: `client/v3/lease.go` at 09669450f (`etc/goose.py`'s etcd pin),
  `lessor.closeRequireLeader`, the compaction `newChs[newIdx], newCtxs[newIdx] = ka.chs[i],
  ka.ctxs[newIdx]` (`lease.go:413`): the kept channel `ka.chs[i]` is paired with `ka.ctxs[newIdx]`,
  not its own `ka.ctxs[i]`.
- **What happens**: a keep-alive with a require-leader subscription A and, after it, a plain one
  B (`chs = [A, B]`, `ctxs = [ctxA, ctxB]`): on a leader loss A is closed and the entry becomes
  `chs = [B]`, `ctxs = [ctxA]`. On the next leader loss B is closed, though `ctxB` does not ask
  for a leader; if A's context is canceled first, A's `keepAliveCtxCloser` finds `ctxA` and
  closes B; and canceling B's context does not close B's channel (B's closer looks for `ctxB`,
  which is no longer in `ka.ctxs`). Reproduction: `notes/pr-verify/etcd-22291/lease_requireleader_pairing_internal_test.go`
  on branch `pr-verify/etcd-22291` (`cp` it to `client/v3/`, `go test -run
  TestLessorCloseRequireLeaderKeepsPairing .`): fails on the pin 09669450f, on upstream f744d457f
  and on etcd-io/etcd#22291's head 71d57990b (log: `pairing-fork-pin.log` there); also
  `TestReviewMixedCase` in `notes/pr-verify/etcd-22291/lease_review_internal_test.go` (log
  `review-tests.log`).
- **Expected**: only channels whose own context carries `WithRequireLeader` are closed
  (`closeRequireLeader`'s comment, `WithRequireLeader`'s documentation).
- **How the proof handles it**: on `pr-verify/etcd-22291`, the lessor's lock invariant pairs each
  channel with a resource `R ch ctx` for its own context (`lessor.muInv`,
  `Proof/go_etcd_io/etcd/client/v3/InvLease.lean`), and `closeRequireLeader` may close a channel only
  through `R ch ctx` with `ctx` requiring a leader. Its spec (`Spec/go_etcd_io/etcd/client/v3/lessor__closeRequireLeader.lean`)
  has the premise `□ ∀ ch c c', R ch c -∗ R ch c'` (the pairing does not matter), used only in the
  compaction branch: that premise is this bug. A fix like #22087's lets the proof drop it.
- **Possible fixes**: etcd-io/etcd#22087 (`ka.ctxs[i]`).
- **Found**: 2026-10-17, verifying etcd-io/etcd#22291 (the reviewer comment on the PR points at it).
