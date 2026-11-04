---
upstream: none
checked: 2026-11-04
links: []
blocks-proof: no
---

# etcdserver: NewServer's error paths after bootstrap leave the WAL open and three goroutines running; a retried server can hang

When `NewServer` fails after `bootstrap` (`server/etcdserver/server.go`, at the fork
`upamanyus/etcd`@323320bb89: an unknown `--auth-token` type at `auth.NewTokenProvider`, `:355`, or
`rafthttp.Transport.Start` failing to re-read the peer TLS files, `:429`), its deferred `b.Close()`
(`bootstrap.go:159-182`) closes only the backend. The WAL (`b.storage.wal.w`) stays open with its
file lock, and three goroutines `NewServer` started before failing keep running: raft's `node.run`
(`b.raft.newRaftNode`, `server.go:324`), the lessor's `runLoop` (`lease.NewLessor`, `:348`;
`lessor.go:245`) and the WAL's file pipeline (`wal/file_pipeline.go:55`). The leaked WAL is
unreachable, so its file's descriptor, and the lock on it, is released only when the GC finalizes
the `*os.File`: a second `NewServer` on the same data directory in the same process gets past
`bootstrap` once that has happened, and otherwise exits at `bootstrap.go:677` (`lg.Fatal("failed to
open WAL")`). The goroutines are never stopped, and the WAL's file pipeline keeps its
preallocated `0.tmp` locked for good (its goroutine holds the file, so no GC closes it): a later
`NewServer` on the directory that succeeds gets a WAL whose own pipeline (`wal.go:402`) blocks in
`fileutil.LockFile` on that `0.tmp`, so its first segment cut (`wal.go:840`, `w.fp.Open()`, reached
from `Save` once the segment exceeds 64 MB) waits forever, blocking its raft loop (inferred, not
driven).

**Why not an issue:** behavior etcd does not exercise: the `etcd` binary exits when `NewServer`
fails (`embed.StartEtcd` returns the error, `etcdmain` exits), which releases the WAL and the
goroutines. Only an embedder that retries `embed.StartEtcd` in the same process meets it, and
`StartEtcd`'s deferred `e.Close()` (`server/embed/etcd.go:117-127`) does not help, since `e.Server`
is nil on this path (`NewServer` returns `nil, err`, `:262`; `Etcd.Close` checks `e.Server != nil`,
`:438`). For such an embedder it is a robustness defect: a goroutine leak, a retry that may `Fatal`
depending on the GC, and a retry that succeeds but hangs at its first WAL segment cut (inferred, not
driven). An embedder test through `embed.StartEtcd` (an unknown `--auth-token`, then a valid one,
then 64 MB of puts; `embed` does not validate `AuthToken` before `NewServer`, `config.go:352, 730`)
would move it to `issues/`.

## Proof

no: the proof models `NewServer`'s error return and `b.Close()`'s closing of the backend
(`bootstrappedServer.Close.spec`, R-D1, 2026-11-04); the WAL, the raft node and the lessor are left to the
process, which no result continues after an error from `NewServer`.

## Notes

Test: `TestSpecBootstrapNewServerErrorLeak` (`etc/spec-test/bootstrap/spec_test.go`, run by its
`run.sh`; go1.27.3, at 323320bb89, 2026-11-04), path 1 (the unknown token type): 3 more goroutines
after `NewServer`'s error (2 before, 5 after, run alone; 8 and 11 beside the file's other tests), the WAL locked (`fileutil.TryLockFile` fails) right
after it, released after an explicit `runtime.GC()`, and a second `NewServer` then failing again only
at the token provider (`auth: invalid auth options`); the same with `GOGC=off`, since the test
collects explicitly. Without a collection between the two calls (`GOGC=off` and no `runtime.GC()`),
the second `NewServer` exits at `bootstrap.go:677`; and after path 1 and a collection, a second
`NewServer` with a valid token succeeds with its pipeline blocked in `syscall.FcntlFlock` ←
`fileutil.ofdLockFile` ← `LockFile` ← `createNewWALFile` ← `(*filePipeline).alloc` while the first
pipeline holds `0.tmp`: the R-D reviews' manual experiments (rounds 2 and 3, 2026-11-04), which also
identified the three goroutines from stack dumps, for path 2 too. The hang at the segment cut is
inferred from `wal.go:822-840`, not driven (no 64 MB written).
`TestSpecBootstrapNewServerErrorPaths` (same file) shows path 2 reachable (a peer CA file that a zap
hook rewrites to a malformed PEM block on "bootstrap successfully": `bootstrap`'s round tripper
accepts it, `Start`'s rejects it, `x509: malformed certificate`). A fix would close the WAL and stop the raft node and the lessor in `NewServer`'s
deferred cleanup (or have `bootstrappedServer.Close` close the WAL too: `WAL.Close` closes the
pipeline, whose `run` removes and unlocks the tmp file, `file_pipeline.go:98-101`). Upstream not
searched (no GitHub access in the session that wrote this).
