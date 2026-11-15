---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---
# etcdserver: `AppliedIndex()` stays behind after a snapshot is installed, until the next entry

`applySnapshot` moves the apply thread's progress (`ep.appliedi`) to the snapshot's index and
`applyAll` then triggers `applyWait` at it, but nothing stores `s.appliedIndex`: the only stores are
per applied entry (`server.go:1944, 1952`). Until the next entry is applied, `AppliedIndex()` reports
the index before the snapshot, while waiters of `applyWait` at indices up to the snapshot's have
already been woken.

**Why not an issue:** found by code reading; no caller relies on the atomic after an `applyWait`
(the read loop serves from the store, which the install moved), and the lag only affects
`exceedsRequestLimit`'s gap check (`v3_server.go:1060-1064`: a request may be refused with
`ErrTooManyRequests` for a little longer) and Maintenance's `RaftAppliedIndex` (a stale number).

## Proof

no: `getAppliedIndex.spec` gives `srvApplied` of the (stale) value it reads, which stays true; the
read path rests on `applyWait`'s `srvApplied` and `srvReadAt` (batch 2d, round 1, provability F6).

## Notes

A one-line fix: `s.setAppliedIndex(ep.appliedi)` (and `setTerm`) at the end of `applySnapshot`.
