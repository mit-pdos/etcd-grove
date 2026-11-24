---
upstream: known
checked: 2026-11-21
links:
  - grpc/grpc-go#9443 issue open: the same cause, its unary form (Invoke returns a bare io.EOF instead of the status)
  - grpc/grpc-go#9447 pr open: the proposed fix in retryLocked (return the attempt's status when shouldRetry passes a bare io.EOF through), which covers this case too
blocks-proof: no
---
# grpc-go: a server-streaming call can end cleanly (io.EOF) with no message after a transparent retry

In grpc-go v1.84.0, when a stream's first attempt is refused (REFUSED_STREAM, or above a GOAWAY's
last stream id) and transparently retried, and the replayed request's write fails on the new
attempt (its stream already ended, or its connection failed), `csAttempt.sendMsg` returns `io.EOF`
and `clientStream.retryLocked` returns it unchanged (`shouldRetry` passes a non-retryable error
through), without `recvMsg`'s status check. For a server-streaming RPC, the client's first `Recv`
then returns `io.EOF`, the clean end: a successful call with no message, whose handler may never
have run. (For a unary call, `Invoke` returns the bare `io.EOF`: grpc/grpc-go#9443.)

**Why not an issue:** found by the grpc model's randomized differential test
(`models/internal/grpcdifftest`, `TestAtMostOnce` with `GRPC_MODEL_CHOOSE=random`: about one run
in 50) and confirmed by reading v1.84.0's `stream.go` (`retryLocked`, `shouldRetry`,
`csAttempt.sendMsg`), which the model keeps verbatim; no test against real grpc-go (the write
failure must fall between the retry's HEADERS and its replayed DATA), and the cause is already
reported upstream.

## Proof

no: nothing proved relies on a server stream's clean end implying a handler run; the model keeps
the behavior (its trusted claim is to include grpc-go's), so a spec of a server-streaming call over
the model must allow a clean end with no message, and `TestAtMostOnce` allows exactly that.

## Notes

etcd's server-streaming RPC is `Maintenance.Snapshot` (a clean end with no data would look like an
empty snapshot to `clientv3`); not assessed. Bidirectional streams (watch, lease keep-alive) go
through the same `retryLocked` path.
