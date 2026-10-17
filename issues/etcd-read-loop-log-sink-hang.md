---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#22214 issue open: the report (a stalled log sink parks the read loop in trace.LogAllStepsIfLong; every linearizable read hangs while the member reports healthy)
  - etcd-io/etcd#22242 pr open: moves the loop's trace logging to a goroutine; does not cover requestCurrentIndex's and sendReadIndex's inline logging (notes/pr-verify/etcd-22242.md)
---

# The linearizable read loop logs on its own goroutine: a stalled log sink hangs every linearizable read

- **Status**: bug (availability; no wrong result): the read loop is the only goroutine that serves
  read indexes, and it writes log entries itself. With a log sink that blocks in `write(2)` (a
  saturated disk, a blocked pipe reader, a stuck syslog), zap's locked write syncer parks the loop,
  and every later `LinearizableReadNotify` (every linearizable `Range`, `Txn`, `MemberList`) waits
  forever. Nothing reports it: reads do not fail, `read_indexes_failed_total` stays 0.
- **Where** (`upamanyus/etcd` `goose-lean` `09669450f`, the same code as upstream `main`
  `a279d15ac`), `server/etcdserver/read/read.go`, all on the loop's goroutine:
  - `LinearizableReadLoop`: `trace.LogAllStepsIfLong(100 * time.Millisecond)` (144), an `Info` for
    every iteration slower than 100 ms;
  - `requestCurrentIndex` (148), called by the loop: `lg.Warn` for an out-of-date read state (182),
    `lg.Info` on the first commit in the term (196), `lg.Warn` every `readIndexRetryTime` (500 ms)
    while the ReadIndex response is late (206), `lg.Warn` at the request timeout (220);
  - `sendReadIndex` (232): `lg.Warn` when `ReadIndex` fails (243).
  A slow disk makes iterations slow and read indexes late, so the slower the sink, the more surely
  the loop logs. Indirectly too: the loop waits on `ApplyWait(confirmedIndex)`, and the apply
  goroutine logs "apply request took too long" inline for every apply over 100 ms
  (`server/etcdserver/apply/uber_applier.go:99`, `txn.WarnOfExpensiveRequest`,
  `server/etcdserver/txn/util.go:94`); parked there, it never reaches the index the loop waits for
  (code reading, not reproduced).
- **What happens**: `notes/pr-verify/etcd-22242/read_logsink_test.go` (copy into
  `server/etcdserver/read/`, `go test -run StalledSink -v .`): a logger whose sink blocks in
  `Write`. At upstream `a279d15ac` both tests fail: `TestReadLoopStalledSink_SlowIteration` (an
  iteration slower than 100 ms logs its trace; the next read's ReadIndex is never sent) and
  `TestReadLoopStalledSink_ReadIndexRetry` (a ReadIndex response later than `readIndexRetryTime`:
  the retry warning parks the loop, the read never completes). With PR #22242 (head `3d53e5a41`)
  the first passes and the second still fails.
- **Expected**: diagnostics should not be able to stop the read path (#22214): log from another
  goroutine, or with a sink that drops on back-pressure.
- **How the proof handles it**: outside what is verified. The read loop's spec
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/read/Read__LinearizableReadLoop.lean`) is a safety
  property (a notifier is closed with `nil` only after a read index the applied index reached);
  Perennial's Hoare triples are partial correctness, so a loop parked forever meets it. The loggers
  are trust-boundary axioms that return (`zap.Logger.Warn`/`Info`,
  `traceutil.Trace.LogWithStepThreshold`), with no statement about how long they take.
- **Possible fixes**: PR #22242's for the trace (a logger goroutine fed by a one-slot channel with a
  nonblocking send); the same for `requestCurrentIndex`'s and `sendReadIndex`'s messages, or rate-
  limited logging, or a zap core that drops entries when its sink is not keeping up.
- **Found**: 2026-10-17, verifying PR #22242 (`notes/pr-verify/etcd-22242.md`); the report is
  upstream's (#22214).
