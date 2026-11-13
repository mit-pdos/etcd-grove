---
upstream: none
checked: 2026-11-07
links: []
blocks-proof: no
---

# etcdserver: a second server on a data directory in use panics in `bootstrap` instead of returning an error

`bootstrap` decides whether the member restarts or starts fresh (`haveWAL := wal.Exist(cfg.WALDir())`,
`server/etcdserver/bootstrap.go:77` at the pin `673da07c8f`) before it opens the backend
(`bootstrapBackend`, `serverstorage.OpenBackend`, `:78`), and the backend's open is where bbolt takes its
file lock. Two servers started on one data directory therefore both read "no WAL". The second blocks on
bbolt's lock. When the first stops, the second gets the lock and goes on with its stale "no WAL": it
calls `bootstrapNewWAL`, whose `wal.Create` finds the first server's WAL and `Logger.Panic`s with "failed
to create WAL: file already exists" (`:719`). Taking the lock first, or checking `wal.Exist` again after
it, would turn this into a restart from the WAL, or an error.

**Why not an issue:** two servers on one data directory is a misuse that etcd does not support. The
lock is there to stop it, and here it does stop it, only with a panic rather than an error. The failing
test (`TestRace` in `examples/axiomcx/waldiralias`, branch `axiom/waldiralias`) starts both servers in
one process, on two strings that name the directory (`/proc/self/cwd/...`). That is the axiom review's
setting (`notes/axiom-review/wal-tokens.md`, the racy variant, 19 of 20 runs), not a way etcd or a
documented user starts a server. Two processes would plausibly hit it too, but that was not run.

## Proof

no: the proof's start rights hand out each WAL directory once (`walDirFresh`, `goose_adequacy_start`),
and `walCreateOk` excludes another process creating the WAL. The in-process case, through two names
of one directory, is the per-string flaw of `goose_adequacy_start`'s `Ds` part, refuted in
`notes/axiom-review/wal-tokens.md`. It is to be repaired in sweep repairs 1 by a premise that the
strings of `Ds` name pairwise distinct directories, after which this path is excluded.

## Notes

Found by the axiom sweep, B3-1 (2026-11-07, etcd-grove-56).
