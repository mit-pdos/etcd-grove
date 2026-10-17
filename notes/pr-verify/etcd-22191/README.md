# Files of the verification of etcd-io/etcd#22191

Revisions: the PR head `34aa7c606c3307ec17af8ae7c05b4e7629871b43` (fetched as `pr-etcd-22191`), its
upstream base `3e3b4c181c69eaaee169d33cbdb9a94a369207bf` (the merge base with `upstream/main`), and
the fork branch `mit-pdos/etcd-grove` branch `pr-etcd-22191-goose-lean` (`2a532d962`, the PR onto
the pin `09669450f`). Every test is a test of package `clientv3`: copy it into `client/v3/` of a
checkout at the named revision and run, from `client/v3/`, the command given
(`GOTOOLCHAIN=go1.27.1`).

| File | What it shows | Revision | Command |
|---|---|---|---|
| `watch_cancel_reconnect_test.go` | The finding `issues/etcd-watch-canceled-substream-stale-id.md`: after a server cancel of watch A and a retryable stream error, watch B, resumed with A's old id on the new stream, is deleted by `closeSubstream(A)`; B loses its events and `Close()` hangs | PR head (fails), PR head + `suggested-fix.diff` (passes), base (panics: the older `etcd-watch-resume-closing-substream`) | `go test -count=1 -timeout 300s -run TestWatchServerCancelThenReconnectKeepsOtherWatch .` |
| `watch_stale_id_etcdlike_test.go` | the same finding with an etcd-like fake server (per-stream ids from 0, `Canceled` only answering a cancel request for a live id) and the realistic trigger (the user cancels A with an event in flight; concurrent `RequestProgress`), then `Unavailable`; written by the reviewer; needs `watch_cancel_reconnect_test.go` beside it (its `reconnRecv`) | PR head (fails), PR head + `suggested-fix.diff` (passes) | `go test -count=1 -timeout 900s -run TestWatchStaleIDEtcdLike -v .` |
| `etcdlike-at-pr-head.log` | its output at the PR head: of 300 trials, 6 lost B's event and hung `Close()`, 2 closed B's channel silently | PR head | as above |
| `etcdlike-with-suggested-fix.log` | its output with the fix: 300 of 300 fine | PR head + `suggested-fix.diff` | as above |
| `reconnect-at-pr-head.log` | its output at the PR head: 23 of 200 trials lost B's event and hung `Close()` | PR head | as above |
| `reconnect-with-suggested-fix.log` | the test, the fork's regression test and the PR's test all pass with the suggested fix | PR head + `suggested-fix.diff` (with `watch_progress_cancel_test.go` copied in too) | `go test -count=1 -run 'TestWatchServerCancelThenReconnectKeepsOtherWatch\|TestWatchProgressBroadcastAfterServerCancel\|TestBroadcastResponseSkipsRemovedSubstream' -v .` |
| `reconnect-at-base.log` | the same scenario at the base: `panic: send on closed channel` (watch.go:761, `unicastResponse`), the resume bug the PR's change also removes; the "lost" counts there are an artefact (the fake server answers only one re-create, which goes to A) | base | three runs of the first command |
| `suggested-fix.diff` | `ws.id = InvalidWatchID` after the PR's `delete` | applies to the PR head | `git apply` |
| `watch_progress_cancel_test.go` | the fork's regression test of the PR's bug (`TestWatchProgressBroadcastAfterServerCancel`, from `goose-lean` `107edf7e4`): a server cancel then a progress broadcast | base (panics), PR head (passes) | `go test -count=3 -run TestWatchProgressBroadcastAfterServerCancel .` |
| `progress-cancel-at-base.log` | its output at the base: `panic: send on closed channel` at watch.go:747 (`broadcastResponse`) | base | as above |
| `pr-test-at-base.log` | the PR's own test `TestBroadcastResponseSkipsRemovedSubstream` passes at the base, without the fix: it does not exercise `run` | base + the PR's `watch_test.go` | `go test -count=1 -run TestBroadcastResponseSkipsRemovedSubstream -v .` |
