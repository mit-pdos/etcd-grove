---
upstream: none
checked: 2026-10-23
links:
  - etcd-io/bbolt#577 issue closed: the same panic on arm32 (an earlier field layout), fixed then; this is a new regression of it
  - etcd-io/bbolt@4bfc851: the commit that introduced it ("Prevent Bucket from being copied by value", 2026-10-15; on main only, in no release)
---

# On 32-bit platforms every transaction panics: `Tx.stats` is no longer 64-bit aligned

- **Status**: a bug (a regression on upstream `main`, not in any release): on 386 (and, by the same
  layout, every 32-bit platform: arm, mips, ppc), the first statistics update of a transaction panics
  with `unaligned 64-bit atomic operation`. Reproduced with bbolt's own tests under `GOARCH=386` on
  linux/amd64 (go1.26.9): `TestBucket_Put` passes at 4bfc851's parent and panics (then hangs until the
  test timeout) at 4bfc851 and at `main` a4ef197. Not in v1.5.0 (the version the bbolt proof pins).
  Not reachable through etcd on 64-bit platforms.
- **Where**: upstream `main` a4ef197, `tx.go:27-44` (`type Tx struct`): `TxStats` (int64 fields updated with
  `atomic.AddInt64`, `tx.go:698-` and `IncCursorCount` at `tx.go:803-805`) is the field `stats`, after
  `writable`, `managed` (padded to 4 bytes), `db`, `meta`, `root` and `pages` (4 bytes each on 386): offset
  20, not a multiple of 8. 4bfc851 changed `root Bucket` to `root *Bucket`, which moved `stats` from an
  aligned offset. `sync/atomic` requires 64-bit alignment of 64-bit words on 32-bit platforms, guaranteed
  only for the first word of an allocated struct.
- **What happens**: `GOARCH=386 go test -run 'TestBucket_Put$' .` at a4ef197:
  `panic: unaligned 64-bit atomic operation` in `internal/runtime/atomic.Xadd64` ←
  `TxStats.IncCursorCount` (and `TxStats.IncSplit` in `TestNode_split`); the deferred rollback then
  panics or deadlocks, and the test binary hangs until its timeout. bbolt's cross-arch CI
  (`.github/workflows/cross-arch-template.yaml`) only runs `go build ./...`, so the tests do not catch it.
- **Expected**: bbolt works on the 32-bit platforms it builds for (`bolt_386.go`, `bolt_arm.go`, ...), as
  at 4bfc851's parent.
- **How the proof handles it**: not in the verified code (the proof pins v1.5.0, before 4bfc851, and
  models no platform alignment); found while running the `bbolt-large-values-leaf-unreadable`
  candidate's tests under `GOARCH=386`.
- **Possible fixes**: make `stats` the first field of `Tx` (or put it after a field that keeps it aligned),
  or use `atomic.Int64` fields in `TxStats` (aligned automatically; but its exported fields are part of the
  API); and run the tests, not only the build, on a 32-bit platform in CI (386 runs on amd64 runners).
- **Found**: 2026-10-23, by the `GOARCH=386` run above (upstream-report of bbolt-large-values-leaf-unreadable).
