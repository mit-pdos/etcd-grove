---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#22081 issue open: same bug (ka.ctxs[newIdx] for ka.ctxs[i] in closeRequireLeader), reported 2026-07-12; no maintainer review yet
  - etcd-io/etcd#22087 pr open: same fix (ctxs[i]) with a regression test, fixes #22081; marked stale 2026-10-12, not approved; upstream main still has ctxs[newIdx]
  - etcd-io/etcd#21872 pr closed: same diagnosis and fix, closed unmerged (2026-06-01)
  - etcd-io/etcd#22094 issue open: related, not this bug (closeRequireLeader leaves a keepAlives entry with no subscribers; fixes proposed in #22253, #22291, open)
blocks-proof: yes
---

# clientv3: after a keep-alive stream loses its leader, canceling one `KeepAlive` closes another caller's channel

When a lease has several `KeepAlive` subscribers, one of them with `WithRequireLeader`, and the
keep-alive stream ends with "no leader", the surviving channels are paired with the wrong
contexts: canceling a caller's context then leaves its channel open (the caller waits for a close
it was promised), and canceling another context closes it instead.

**Reproduction:** `TestCloseRequireLeaderKeepsContextsAligned` in
[`issues/etcd-lease-close-require-leader-ctx-misaligned/lease_close_require_leader_test.go`](etcd-lease-close-require-leader-ctx-misaligned/lease_close_require_leader_test.go),
copied into `client/v3` at etcd-io/etcd@1573d5941 (2026-10-28), go1.27.3 linux/amd64. It builds
the lessor state two `KeepAlive` calls make (A with `WithRequireLeader`, B plain), runs
`closeRequireLeader` (what `recvKeepAliveLoop` does on `ErrNoLeader`), cancels B and runs B's
`keepAliveCtxCloser`:

```
$ go test . -run '^TestCloseRequireLeaderKeepsContextsAligned$' -count=1
--- FAIL: TestCloseRequireLeaderKeepsContextsAligned (0.00s)
    lease_close_require_leader_test.go:54: B's channel not closed after B's context was canceled; ka.ctxs[0] is A's context: true
FAIL
```

The cause is one index in
[`closeRequireLeader`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/lease.go#L413):
`ka.ctxs[newIdx]` where `ka.ctxs[i]` is meant.

## Proof

yes: the verified fork carries the one-token fix (`a7bd9a16e`, `etc/goose.py`); with the upstream
line the proof of `closeRequireLeader` fails on the lessor invariant's channel/context pairing
(`kaReg`, `Proof/go_etcd_io/etcd/client/v3/InvLessor.lean`).

## Notes

- The 2026-10-23 review's plan: wait to see if #22087 gets merged.
- The test sets the lessor's fields by hand rather than through `KeepAlive` and a server that
  answers "no leader"; #22087's test is the upstream one.
