---
upstream: none
checked: 2026-11-15
links:
blocks-proof: no
---
# etcd: a member restarting on a torn WAL tail hangs, instead of failing, when closing the WAL fails before the repair

At boot, when reading the WAL fails with an unexpected EOF (a torn last record), the server closes
the WAL, ignores the error, and repairs it
([`openWALFromSnapshot`](https://github.com/etcd-io/etcd/blob/260e4e0457aa317681e8576339dc9ee1ebcabd66/server/etcdserver/bootstrap.go#L681-L694)).
If the close's fdatasync fails, [`WAL.Close`](https://github.com/etcd-io/etcd/blob/260e4e0457aa317681e8576339dc9ee1ebcabd66/server/storage/wal/wal.go#L962-L966)
returns before releasing its file locks, and `Repair` then takes a blocking lock on the last WAL
file ([`openLast`](https://github.com/etcd-io/etcd/blob/260e4e0457aa317681e8576339dc9ee1ebcabd66/server/storage/wal/repair.go#L109-L116),
`F_OFD_SETLKW` or `flock`, both per open file, so they conflict within the process): the member
waits forever instead of exiting with an error.

**Why not an issue:** no test, found by code reading: it needs an fdatasync error injected at that
one call (etcd's failpoints around the WAL sync, `walBeforeSync`/`walAfterSync`, are `struct{}`
failpoints in `Save` that can only panic or sleep, not return an error), and the outcome is a hang
on a disk that already fails, where a crash was due anyway. Same code at upstream `main`
(etcd-io/etcd@260e4e0) and upamanyus/etcd@3df9b265f (`bootstrap.go:683`). Fix if wanted:
`Fatal` on `Close`'s error before `Repair`.

## Proof

no: a hang is liveness. But the server's restart (C6, `notes/wal-units/specgap.md` row 6 and
§3.2) cannot be proved on this path over the current specs: `WAL.Close.specFailed` loses the
unlocked token when `Close` fails, and `wal.Repair.spec` needs it. Ledger P7 (2026-11-15):
either the lock model (Repair then specified as possibly blocking) or the fork fix above; if the
fork fix is chosen, the proof needs it and this becomes `yes`.

## Notes

Searched upstream `main`'s history of `openWALFromSnapshot` (`git log -L`): no change has checked
the `w.Close()` before `Repair`; the last change to the loop (`bd9f1584d`, 2023) left it as is.
GitHub's issue search was not run.
