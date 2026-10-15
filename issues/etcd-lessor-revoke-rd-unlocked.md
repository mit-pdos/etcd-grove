# lease: `SetRangeDeleter`/`Recover` must not run concurrently with `Revoke` (undocumented)

- **Status**: open, documentation (an unstated precondition, not a bug: unreachable in etcd's
  server, where `SetRangeDeleter` runs at the store's construction and `Recover` and `Revoke` both
  run on the apply goroutine).
- **Where**: `server/lease/lessor.go` at the pinned revision (`etc/goose.py`, bc8b52a50319):
  `lessor.Revoke` (`lessor.go:326`) unlocks `le.mu` after its map lookup and then reads `le.rd`
  (`if le.rd == nil`, `lessor.go:339`; `txn := le.rd()`, `lessor.go:343`) without the lock;
  `SetRangeDeleter` (`lessor.go:267-272`) and `Recover` (`lessor.go:600-605`) write `le.rd` under
  `le.mu`. The `Lessor` interface (`lessor.go:83-140`) is a concurrent object (every method locks
  `le.mu` itself) and says nothing about `SetRangeDeleter`/`Recover` not running concurrently with
  `Revoke`.
- **What happens**: a `Revoke` concurrent with `SetRangeDeleter` (or `Recover`) is a data race on
  `le.rd`. Reproduction (`go test -race`, in `server/lease`):

  ```go
  func TestRevokeSetRangeDeleterRace(t *testing.T) {
  	lg := zap.NewNop()
  	dir, be := NewTestBackend(t)
  	defer os.RemoveAll(dir)
  	defer be.Close()
  	le := newLessor(lg, be, clusterLatest(), LessorConfig{MinLeaseTTL: minLeaseTTL})
  	defer le.Stop()
  	le.SetRangeDeleter(func() TxnDelete { return newFakeDeleter(be) })
  	for i := 1; i <= 100; i++ {
  		if _, err := le.Grant(LeaseID(i), 10); err != nil {
  			t.Fatal(err)
  		}
  	}
  	var wg sync.WaitGroup
  	wg.Add(2)
  	go func() {
  		defer wg.Done()
  		for i := 1; i <= 100; i++ {
  			le.SetRangeDeleter(func() TxnDelete { return newFakeDeleter(be) })
  		}
  	}()
  	go func() {
  		defer wg.Done()
  		for i := 1; i <= 100; i++ {
  			if err := le.Revoke(LeaseID(i)); err != nil {
  				t.Error(err)
  			}
  		}
  	}()
  	wg.Wait()
  }
  ```

  reports `WARNING: DATA RACE` between the write at `lessor.go:271` (`SetRangeDeleter`) and the
  read at `lessor.go:339` (`Revoke`) (run 2026-10-13 with go1.27.1).
- **Expected**: the `Lessor` interface documents that `SetRangeDeleter` and `Recover` are not
  called concurrently with `Revoke` (in etcd: at construction, or on the goroutine that revokes).
- **How the proof handles it**: `Revoke` is not proved (out of scope for now: the verification
  targets a client doing Puts and Gets without leases, for which no lease is granted and `Revoke`
  never runs); the apply package's `Revoke` clause stays a premise
  (`apply.isApplyLessor_of_lessorInv`). A proof would take the precondition above as a right to
  `le.rd` shared by the specs of `SetRangeDeleter`, `Recover` and `Revoke`, held by the one
  goroutine that sets the range deleter and revokes (the apply thread), so no Go change.
- **Possible fixes**: document the precondition. Changing the implementation (reading
  `rd := le.rd` before `le.mu.Unlock()` in `Revoke`) is needed only for a spec that allows
  concurrent `SetRangeDeleter`/`Recover`.
- **Found**: 2026-10-13, the backend's unit 9 (the lessor's apply-side methods), while writing
  `lessor.Revoke`'s spec; the race confirmed with the test above.
