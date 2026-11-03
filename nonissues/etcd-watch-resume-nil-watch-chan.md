---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#7938 pr closed: related, different (2017, unmerged): canceled watchers left in `resuming` across a reconnect; not the nil channel
blocks-proof: yes
---

# clientv3: a watch canceled during a reconnect can be handed a nil WatchChan

If a watch's create is in flight when the stream fails transiently, its context is canceled while the
client reconnects, and the `Watch` caller's goroutine reaches its final `select` only after the client
has torn the watch down, `Watch` can return a nil channel (on which a receive blocks forever) instead
of a closed one: `waitCancelSubstreams` sets the watch's output channel to nil
([L974-L1008](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/watch.go#L974-L1008))
and `closeSubstream` then sends it on the watch's `retc`
([L487-L494](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/watch.go#L487-L494)).

**Why not an issue:** no test through the public API: the last step needs the caller's goroutine
descheduled across a whole reconnect, which the test below plays itself through internals (it sends
the watch request on the stream's `reqc` and reads `retc` directly). The user's 2026-10 review: skip.

**Test:** `TestWatchResumeNilChannelOnRetc` in
[`nonissues/etcd-watch-resume-nil-watch-chan/watch_resume_nil_retc_test.go`](etcd-watch-resume-nil-watch-chan/watch_resume_nil_retc_test.go)
(from the fork's `a8a459955`), copied into `client/v3` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef, go1.27.3 linux/amd64:

```
$ go test . -run '^TestWatchResumeNilChannelOnRetc$' -count=1
--- FAIL: TestWatchResumeNilChannelOnRetc (0.10s)
    watch_resume_nil_retc_test.go:106: retc carries a nil WatchChan: Watch() may return a channel that never closes
FAIL
```

## Proof

yes: the verified fork carries the fix (`c15c7dda8`, from `a8a459955` on branch
`watch-resume-fixes`: `closeSubstream` sends nothing on `retc` for a nil channel); the watch contract
returns a channel that is not nil, which holds across a reconnect only over it (`notes/decisions.md`,
D25).

## Notes

The race is real; a test that only uses `Watch`, `Close` and a fake server would hit it with a tiny
probability. Promote it if one is written.
