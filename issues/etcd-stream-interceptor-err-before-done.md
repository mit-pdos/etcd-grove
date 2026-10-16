---
upstream: unchecked
checked:
links:
---

# The stream interceptor's cancellable context reports an error before it is done

- **Status**: open (not reported).
- **Where**: `server/etcdserver/api/v3rpc/interceptor.go` at the pinned revision (`upamanyus/etcd`
  `bc8b52a50`, the same code as upstream `main`): `cancellableContext.Cancel` (lines 288–293:
  `c.lock.Lock(); c.cancelReason = reason; c.lock.Unlock(); c.cancel()`) and
  `cancellableContext.Err` (297–304: the stored reason if non-nil, else the embedded context's
  `Err()`). Its users: `newStreamInterceptor` (the require-leader branch wraps the stream in a
  `serverStreamWithCtx` whose `Context()` is the `cancellableContext`; the deferred
  `ctx.Cancel(nil)`, line 256) and `monitorLeader` (`ssWithCtx.ctx.Cancel(rpctypes.ErrGRPCNoLeader)`,
  line 342, then `<-ss.Context().Done()`). The contract: `context.Context`'s documentation, "If
  Done is not yet closed, Err returns nil. If Done is closed, Err returns a non-nil error".
- **What happens**: between `Cancel`'s unlock (line 291) and its `c.cancel()` (line 292), a
  concurrent `Err()` returns the stored reason (`ErrGRPCNoLeader`) while `Done()` is still open: a
  non-nil `Err()` on a context that is not done. Who can observe it: any code holding the stream's
  context, i.e. the handler (`ss.Context()` is the wrapper), while the leader monitor cancels the
  stream. etcd's own handler (`watch.go`) reads `stream.Context().Err()` after `Done()` is closed
  (line 227: no window) and, in `isClientCtxErr(stream.Context().Err(), err)` (lines 201, 494, 520,
  544), after a stream error: there the window can only change how the error is classified (a
  debug log instead of a warning and a `streamFailures` count, or the reverse), a wrong reason at
  most. A handler polling `Err() != nil` as "done" (a common idiom) would stop before the
  context's `Done()` is closed; nothing in etcd does.

  Reproduction (deterministic: a test of the package that observes the state at the moment
  `Cancel` reaches `c.cancel()`, by wrapping the `cancel` field `newCancellableContext` set; run
  without touching the tree with `go test -overlay overlay.json -run
  TestCancellableContextErrBeforeDone -v ./etcdserver/api/v3rpc/` from `server/`, the overlay
  mapping `etcdserver/api/v3rpc/zz_err_before_done_test.go` to this file; it passes, logging
  `Done() open, Err() = no leader`):

  ```go
package v3rpc

import (
	"context"
	"errors"
	"testing"
)

// cancellableContext.Cancel stores the reason, unlocks, then calls the underlying cancel: in
// between, Err() returns the reason while Done() is still open, against context.Context's
// contract ("If Done is not yet closed, Err returns nil"). The test observes that state from
// inside the cancel call (the moment Cancel reaches c.cancel()), deterministically.
func TestCancellableContextErrBeforeDone(t *testing.T) {
	c := newCancellableContext(context.Background())
	reason := errors.New("no leader")
	realCancel := c.cancel
	observed := false
	c.cancel = func() {
		observed = true
		select {
		case <-c.Done():
			t.Fatal("Done() already closed before the underlying cancel")
		default:
		}
		if err := c.Err(); err == nil {
			t.Fatal("expected a non-nil Err() in the window")
		} else {
			t.Logf("Done() open, Err() = %v", err)
		}
		realCancel()
	}
	c.Cancel(reason)
	if !observed {
		t.Fatal("cancel not called")
	}
	<-c.Done()
	if !errors.Is(c.Err(), reason) {
		t.Fatalf("Err() = %v after Cancel", c.Err())
	}
}
  ```

  A test racing a goroutine's `Err()` against `Cancel` would hit the window only sometimes; the
  wrapper above shows the state the window exposes.
- **How it happens**: `Cancel` publishes the reason under the lock, releases the lock, and only
  then closes `Done()`. `Err()` reads the reason under the lock, without looking at `Done()`.

  1. A client opens a watch stream with require-leader metadata. The interceptor wraps the
     stream's context in a `cancellableContext`.
  2. The member loses its leader. `monitorLeader` calls `Cancel(rpctypes.ErrGRPCNoLeader)`,
     which stores the reason and unlocks.
  3. Before `Cancel` reaches `c.cancel()`, the handler calls `ss.Context().Err()`. It returns
     `ErrGRPCNoLeader`, while `ss.Context().Done()` is still open.

  ```go
  // server/etcdserver/api/v3rpc/interceptor.go:288-304 (etcd main f061acd09)
  func (c *cancellableContext) Cancel(reason error) {
  	c.lock.Lock()
  	c.cancelReason = reason // <- visible to Err() after the unlock
  	c.lock.Unlock()
  	c.cancel()              // <- Done() closes only here
  }

  // Err will return the preserved cancel reason error if present, and will
  // otherwise return the underlying error from the parent context.
  func (c *cancellableContext) Err() error {
  	c.lock.RLock()
  	defer c.lock.RUnlock()
  	if c.cancelReason != nil {
  		return c.cancelReason
  	}
  	return c.Context.Err()
  }
  ```
- **Expected**: `Err()` is `nil` until `Done()` is closed (the `context.Context` contract the
  wrapper implements by embedding).
- **How the proof handles it**: the require-leader branch, the only place a `cancellableContext`
  is made, is excluded by the premise `v3rpc.runsNoRequireLeader`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvStreamInterceptor.lean`: no client asks
  for a leader on a stream); with the window, the wrapper cannot meet Perennial's `isContext` (its
  `Err` clause), so the branch could not be proved even with a `context.WithCancel` spec over any
  parent context (`notes/STATUS.md`, "W-W, the stream interceptor"; `notes/decisions.md`, "The
  stream interceptor's require-leader premise").
- **Possible fixes**: call `c.cancel()` before publishing the reason is not enough (a reader
  could then see `Done()` closed and `Err()` the parent's `context.Canceled`, the reason lost,
  which is what the wrapper exists to avoid); instead make `Err` consult `Done` first:
  `select { case <-c.Context.Done(): default: return nil }` before reading the reason, so that the
  reason is reported only once the context is done (the reason is stored before the cancel, so it
  is visible by then). Or use Go 1.20's `context.WithCancelCause(parent)` and
  `context.Cause(ctx)`, which store the cause and close `Done` atomically, and drop the wrapper's
  lock.
- **Found**: 2026-10-15, the watch slice's unit W-W (the stream interceptor), while specifying
  the require-leader branch against Perennial's `context.isContext`.
