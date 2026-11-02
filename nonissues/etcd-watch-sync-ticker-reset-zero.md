---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#22296 issue open: same bug, reported by someone else on windows/amd64 (Go's monotonic clock there advances in ~0.5 ms steps); no maintainer response on the issue
  - etcd-io/etcd#22297 pr open: same bug, fix (`resyncDelay`); a maintainer (serathius) commented "Never seen the issue in production, doesn't seem like a real issue"; Windows is a Tier 3 platform; cherry-picked into the fork as 5615016f6
blocks-proof: yes
---

# mvcc: syncWatchersLoop panics resetting its ticker to zero on a coarse monotonic clock

After a sync pass that made progress but left watchers unsynced, `syncWatchersLoop` resets its ticker
to the pass's duration, `time.Since(st)`
([L240-L247](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/storage/mvcc/watchable_store.go#L240-L247));
where the monotonic clock did not advance during the pass (Windows), that is 0, and `Ticker.Reset(0)`
panics, killing the member.

**Why not an issue:** reachable only on Windows, a Tier 3 platform (etcd ships binaries, without
support or CI); no test here (on Linux `time.Since` is never 0; #22296 reports the panic in the mvcc
unit tests on Windows 11, 5 of 5). Upstream's maintainer judged it not a real issue on #22297.

## Proof

yes: the verified fork carries #22297's fix (`5615016f6`); `Spec/time/Ticker__Reset.lean` requires a
positive duration, and the loop is proved over `resyncDelay`
(`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/resyncDelay.lean`).

## Notes

The user's 2026-10 review: wait for #22297 to merge. Departed from: with the maintainer's comment and
Windows' tier, it does not meet the bar here; it stays tracked through #22296.
