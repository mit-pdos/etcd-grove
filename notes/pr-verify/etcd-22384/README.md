# Files of the verification of etcd-io/etcd#22384 (`ResumeMutex`)

Report: `notes/pr-verify/etcd-22384.md`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `pr-tests.log` | The PR's own `TestResumeMutex` and the existing `TestResumeElection`, `TestMutexLockSessionExpired`, `TestMutexUnlock` pass. | PR head `7ee0cfdf3` (upstream checkout) | `cd tests && go test ./integration/clientv3/concurrency/ -run 'TestResumeMutex\|TestResumeElection\|TestMutex' -v` |
| `resume_mutex_probe_test.go` | Three probes (all pass, i.e. the behavior described holds): `TestProbeMutexHeaderRevisionIsNotMyRev` — after a contended `Lock`, `Header().Revision` (7) is not the key's create revision (3), and resuming with it gives a non-owner handle: the caller needs an extra `Get` to learn `myRev`, since `Mutex` has no `Rev()`; `TestProbeLockAlreadyResumes` — a restarted process on the surviving lease (`WithLease`) gets the lock back with `NewMutex` + `Lock`, without waiting, while another session is queued; `TestProbeResumeMutexSlashedPrefix` — passing the prefix with its trailing `/` gives a handle whose `Unlock` refuses the key. | PR head `7ee0cfdf3` | `cp resume_mutex_probe_test.go <etcd at PR head>/tests/integration/clientv3/concurrency/ && cd <etcd>/tests && go test ./integration/clientv3/concurrency/ -run TestProbe -v` |
| `resume_mutex_review_probe_test.go` | The reviewer's four probes (all pass): `TestProbeResumeViaLock` — `WithLease` + `NewMutex` + `TryLock` gets the lock back (create rev 2, header 3 on the reused-key branch); `TestProbeHeaderRevAfterWait` — after waiting, header 7 vs create rev 6; `TestProbeResumedStaleUnlockDeletesRecreated` — a resumed handle with a stale revision fails `IsOwner` but its `Unlock` deletes the re-created key; `TestProbeResumedForeignKeyUnlock` — a handle resumed in session B with session A's key deletes A's lock key on `Unlock`; `Header()` is nil. | PR head `7ee0cfdf3` | as above, `-run TestProbe` |
| `review-probe.log` | The output of the reviewer's probes. | PR head `7ee0cfdf3` | (above) |
| `probe.log` | The output of the probe run. | PR head `7ee0cfdf3` | (above) |

The verified code is `mit-pdos/etcd-grove` branch `pr-etcd-22384-goose-lean` (commit `83587195a`):
the fork's `goose-lean` at `09669450f` plus the PR's `mutex.go` change, applied cleanly.
Go toolchain: `GOTOOLCHAIN=go1.27.1`.
