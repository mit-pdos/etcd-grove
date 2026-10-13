# lease: `Revoke` reads the range deleter outside the lessor's lock

- **Status**: open (an unstated precondition; not reachable in etcd's server, where
  `SetRangeDeleter` runs at the store's construction and `Recover` and `Revoke` both run on the
  apply goroutine).
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
- **Expected**: either `Revoke` reads `le.rd` under `le.mu` (with the lease lookup, before
  unlocking), or the interface documents that `SetRangeDeleter` and `Recover` must not run
  concurrently with `Revoke`.
- **How the proof handles it**: `Revoke` is not proved (`notes/STATUS.md`, the backend's unit 9):
  its read of `le.rd` outside the lock needs a share of the field outside `le.mu`'s invariant
  (`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`, `lessorMu`), which `SetRangeDeleter`'s
  spec (unit 8: any caller, under the lock alone) does not give; the apply package's `Revoke`
  clause stays a premise (`apply.isApplyLessor_of_lessorInv`).
- **Possible fixes**: read `rd := le.rd` before `le.mu.Unlock()` in `Revoke` and use `rd`
  afterwards.
- **Found**: 2026-10-13, the backend's unit 9 (the lessor's apply-side methods), while writing
  `lessor.Revoke`'s spec; the race confirmed with the test above.
