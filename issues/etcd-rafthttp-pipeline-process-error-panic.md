---
upstream: none
checked: 2026-11-10
links:
  - etcd-io/etcd#10569 issue closed: related, not this bug (asks to add `Error()` to `writerToResponse`; nobody noticed that no error implements it)
  - etcd-io/etcd#17078 pr merged: added the second `403` that hits this (a message to a mismatched member)
  - etcd-io/etcd#3579 pr merged: introduced it (2015: `HTTPError.WriteTo` started returning an error, and so stopped matching rafthttp's `writerToResponse`)
blocks-proof: yes
---

# rafthttp: a raft message the member rejects makes the peer handler panic and answer 500 instead of 403

When a member rejects a raft message posted to its peer `/raft` endpoint, because the sender was
removed from the cluster or because the message is addressed to another member, the handler
answers `500 Internal Server Error` and then panics, cutting the response short; net/http recovers
the panic and drops the connection. The `403 Forbidden` the server means to send is never
written, so a removed member that posts to its old peers is never told it was removed by this
path.

**Expected:** the handler should answer the status the server's
[`Process`](https://github.com/etcd-io/etcd/blob/fc81ffd2d5d79d4c685e476cedb7c5296ee019c4/server/etcdserver/server.go#L699-L721) returns (`403`, which the sender's
[`checkPostResponse`](https://github.com/etcd-io/etcd/blob/fc81ffd2d5d79d4c685e476cedb7c5296ee019c4/server/etcdserver/api/rafthttp/util.go#L110-L111) reads as "this member
was removed" and stops on), as the [`writerToResponse`
branch](https://github.com/etcd-io/etcd/blob/fc81ffd2d5d79d4c685e476cedb7c5296ee019c4/server/etcdserver/api/rafthttp/http.go#L148-L163) of the handler is written to do,
without panicking.

**Impact:** every release since 2015 (checked: v3.4.45, v3.5.35, v3.6.16, v3.7.3, `main`), any
configuration. Reached whenever a member posts a raft message to a peer that rejects it: a removed
member that is still running (it was down when it was removed, or has not applied its own removal
yet), or a member whose peer URL for another member is now served by a different member (a member
removed and a new one added on the same peer URL, while a peer lags behind both changes). Each
such message costs a recovered handler panic and a closed connection; the panic is silent with
etcd's own peer server (`embed` discards net/http's error log) and logged with a stack trace by a
server that keeps net/http's default log. The removed member still stops, through its stream
connections (`410 Gone`), so this is not a liveness failure; but the `403` path for removed
members is dead code, and the snapshot handler has the same dead branch (it answers `500`
without panicking). Found by a test that repeatedly removes members and adds new ones on the
freed peer URLs: about half of its rounds hit the panic.

**Reproduction:** `TestRaftPipelineRejectsMisaddressedMessage` and
`TestRaftPipelineRejectsRemovedMember` in
[`issues/etcd-rafthttp-pipeline-process-error-panic/rafthttp_reject_test.go`](etcd-rafthttp-pipeline-process-error-panic/rafthttp_reject_test.go),
copied into `tests/integration` at etcd-io/etcd@fc81ffd2d5d79d4c685e476cedb7c5296ee019c4 (2026-11-10), go1.27.3 linux/amd64. A
3-member cluster; the test posts, to member 0's `/raft` endpoint, the request a peer's pipeline
sends (rafthttp's `createPostRequest` headers, a protobuf `raftpb.Message`): a heartbeat from
member 1 to member 2 (what member 1 sends when the URL it holds for member 2 is member 0's), and,
after member 2 is removed, a heartbeat response from member 2. Each asserts that the response is a
complete `4xx` (`403` for the removed sender):

```
$ (cd tests && go test ./integration -run 'TestRaftPipelineRejects' -count=1)
--- FAIL: TestRaftPipelineRejectsMisaddressedMessage (0.27s)
    rafthttp_reject_test.go:86:
        	Error:      	Received unexpected error:
        	            	unexpected EOF
        	Messages:   	response body cut short (status 500): the handler panicked
--- FAIL: TestRaftPipelineRejectsRemovedMember (0.28s)
    rafthttp_reject_test.go:114:
        	Error:      	Received unexpected error:
        	            	unexpected EOF
        	Messages:   	response body cut short (status 500): the handler panicked
FAIL
```

The member's log shows `rejected Raft message to mismatch member` (resp. `from removed member`)
followed by `failed to process Raft message`, the warning of the handler's panicking branch.
The same tests fail the same way at the pinned fork commit (upamanyus/etcd@a4d2bb17, based on
etcd-io/etcd@f061acd0).

**Cause:** `Process` rejects these messages with `*httptypes.HTTPError`, whose
[`WriteTo(w) error`](https://github.com/etcd-io/etcd/blob/fc81ffd2d5d79d4c685e476cedb7c5296ee019c4/server/etcdserver/api/etcdhttp/types/errors.go#L33) returns an error,
while the handler's [`writerToResponse`](https://github.com/etcd-io/etcd/blob/fc81ffd2d5d79d4c685e476cedb7c5296ee019c4/server/etcdserver/api/rafthttp/http.go#L72-L74)
interface declares `WriteTo(w)` with no result. No error type in etcd has that method set, so
`errors.As(err, &writerErr)` never matches and every `Process` error takes the `default` branch,
which writes `500`, flushes and
[`panic(err)`](https://github.com/etcd-io/etcd/blob/fc81ffd2d5d79d4c685e476cedb7c5296ee019c4/server/etcdserver/api/rafthttp/http.go#L159-L162). rafthttp's unit test of
that branch uses its own error type with the old signature (`resWriterToError`, `http_test.go`),
so it passes.

## Proof

yes: the panic is a handler panic of the verified server, which the network model treats as a
program panic (the proof needs the fork fix below; recovering it in the net/http model is the
alternative, `notes/specs-only/net-extensions-design.md`); the crashreconf adequacy test reaches it
with a reused peer URL (`notes/specs-only/crashreconf-test.md`, "Findings" 2).

## Fix

[`fix.patch`](etcd-rafthttp-pipeline-process-error-panic/fix.patch) (against etcd-io/etcd@fc81ffd2d5d79d4c685e476cedb7c5296ee019c4;
both tests and `server/etcdserver/api/rafthttp`'s pass with it): `writerToResponse` declares
`WriteTo(w http.ResponseWriter) error`, so `HTTPError` matches (and the unit test's error type
follows); and `Process` answers a message to a mismatched member with `412 Precondition Failed`
instead of `403`. The second change is needed with the first: once the `403` reaches the sender,
`checkPostResponse` would read a misaddressed message's `403` as "the sender was removed" and
stop a healthy member (`nonissues/etcd-rafthttp-misaddressed-403-member-removed.md`); `412` is
what the stream handler already answers a mismatched `X-Raft-To`, and the sender treats it as a
transient error. Alternatives: check for `*httptypes.HTTPError` by type in rafthttp, or
`panic(http.ErrAbortHandler)` in the `default` branch (stops the panic noise only).

## Notes

The crashreconf test's other peer-API finding, that a member must serve etcd's whole peer handler
(`etcdhttp.NewPeerHandler`: `/members`, `/members/promote/<id>`, ...) or learners cannot join
and a promote through a follower fails, is not a bug: `embed` serves the whole handler
([`etcd.go`](https://github.com/etcd-io/etcd/blob/fc81ffd2d5d79d4c685e476cedb7c5296ee019c4/server/embed/etcd.go#L594)), and nothing documents `EtcdServer.RaftHandler`
alone as sufficient; the repository's own starters served only `RaftHandler`.
