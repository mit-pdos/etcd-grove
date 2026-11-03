---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/bbolt#1300 pr merged: introduced it ("Prevent Bucket from being copied by value", commit 4bfc851, 2026-10-16; on main only, in no release)
  - etcd-io/bbolt#577 issue closed: the same panic on arm32 with an earlier field layout, fixed then; this is a new regression of it
blocks-proof: no
---

# bbolt: on 32-bit platforms every transaction panics with "unaligned 64-bit atomic operation"

On `main`, every transaction on a 32-bit platform (386, arm, mips) panics on its first statistics
update with `unaligned 64-bit atomic operation`; the deferred rollback then panics again or
deadlocks. The smallest program (open, put one key in an `Update`) hits it. A regression from
#1300, on `main` only, in no release.

**Expected:** bbolt should work on the 32-bit platforms it builds for (`bolt_386.go`,
`bolt_arm.go`, ...), as it did before #1300; `sync/atomic` requires the 64-bit words it updates to
be 64-bit aligned on those platforms ([bugs section](https://pkg.go.dev/sync/atomic#pkg-note-BUG)).

**Impact:** every user of bbolt on a 32-bit platform once a release includes #1300 (v1.5.0 is not
affected), etcd on 32-bit platforms included. bbolt's cross-arch CI only builds, so it does not
catch it.

**Reproduction:** `TestTx_Stats_Aligned32Bit` in
[`issues/bbolt-txstats-unaligned-32bit/txstats_386_test.go`](bbolt-txstats-unaligned-32bit/txstats_386_test.go),
copied into the root of etcd-io/bbolt@a4ef19710eb7ddc41fd1155336baf331b5c57ba8 (2026-10-16),
go1.27.3 linux/amd64 running `GOARCH=386` (it passes at 4bfc851's parent, 7f68b29):

```
$ GOARCH=386 go test . -run TestTx_Stats_Aligned32Bit -count=1 -timeout 60s
--- FAIL: TestTx_Stats_Aligned32Bit (0.00s)
panic: unaligned 64-bit atomic operation
internal/runtime/atomic.panicUnaligned()
	/usr/local/go/src/internal/runtime/atomic/unaligned.go:8 +0x2d
internal/runtime/atomic.Load64(0xc8b240c)
	/usr/local/go/src/internal/runtime/atomic/atomic_386.s:235 +0x10
go.etcd.io/bbolt.(*TxStats).GetPageCount(...)
	tx.go:779
go.etcd.io/bbolt.(*TxStats).add(0xc8c6180, 0xc8b240c)
	tx.go:743 +0x75
go.etcd.io/bbolt.(*Tx).close(0xc8b23f8)
	tx.go:366 +0x10c
```

**Cause:** the `int64` fields of [`TxStats`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/tx.go#L27-L44)
are updated with `atomic.AddInt64`, and `stats` is no longer at an 8-byte-aligned offset of `Tx`
on 32-bit platforms: #1300 changed `root Bucket` to `root *Bucket`, which put `stats` at offset 20
(after `writable`, `managed`, `db`, `meta`, `root` and `pages`, 4 bytes each with padding).

## Proof

no: not in the verified code (the bbolt proof, branch `bbolt`, pins v1.5.0, before #1300, and its
model is 64-bit).

## Fix

Make `stats` the first field of `Tx` (or use `atomic.Int64` fields, aligned automatically, though
`TxStats`'s fields are exported), and run the tests, not only the build, under `GOARCH=386` in CI.
