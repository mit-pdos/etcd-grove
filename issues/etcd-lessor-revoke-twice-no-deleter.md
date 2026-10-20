---
upstream: none
checked: 2026-10-20
links:
  - etcd-io/etcd#10710 pr merged: related, not this bug (the lease benchmark's Revoke left leases in leaseMap until the PR set a fake range deleter; a reviewer noted it, the lessor was not changed)
---

# server/lease: without a range deleter, `Revoke` keeps the lease and a second `Revoke` panics

- **Status**: documentation the code contradicts (the `Lessor` interface says `Revoke` removes
  the lease), with a panic; not reachable through etcd's server, whose `mvcc.New` sets the range
  deleter before any revocation.
- **Where**: the fork `upamanyus/etcd` at `107edf7e4` (`etc/goose.py`'s etcd pin).
  `lessor.Revoke` (`server/lease/lessor.go:326-363`) defers `close(l.revokec)` (line 335) and
  returns `nil` when `le.rd == nil` (lines 339-341), before deleting the lease from `leaseMap`
  and the backend. The interface's documentation (`lessor.go:93-96`): "Revoke revokes a lease
  with given ID. The item attached to the given lease will be removed. If the ID does not exist,
  an error will be returned."
- **What happens**: the lease stays (`Lookup` finds it) after a successful `Revoke`, and a second
  `Revoke` of it closes `revokec` again: `panic: close of closed channel`. Reproduction (a test
  in `server/lease`, `go test -run TestLessorRevokeTwiceWithoutRangeDeleter .`; it passes, i.e.
  confirms the behaviour, at the pin):

  ```go
  func TestLessorRevokeTwiceWithoutRangeDeleter(t *testing.T) {
  	dir, be := NewTestBackend(t)
  	defer os.RemoveAll(dir)
  	defer be.Close()
  	le := newLessor(zap.NewNop(), be, clusterLatest(), LessorConfig{MinLeaseTTL: minLeaseTTL})
  	defer le.Stop()
  	if _, err := le.Grant(1, 100); err != nil {
  		t.Fatal(err)
  	}
  	if err := le.Revoke(1); err != nil {
  		t.Fatal(err)
  	}
  	if le.Lookup(1) != nil {
  		t.Logf("after Revoke(1) returned nil, the lease is still there")
  	}
  	defer func() {
  		r := recover()
  		if r == nil {
  			t.Fatal("expected a panic")
  		}
  		t.Logf("second Revoke(1) panicked: %v", r)
  	}()
  	le.Revoke(1)
  }
  ```
- **Expected**: `Revoke` removes the lease (from the map and the backend) whether or not a range
  deleter is set, or its documentation states that it needs one.
- **How the proof handles it**: `Revoke` is unproved; the apply package's lessor contract
  (`apply.isApplyLessor`, `etcdserver/apply/Contracts.lean`) is about the server's lessor, whose
  range deleter `mvcc.New` sets.
- **Possible fixes**: in the `le.rd == nil` case, still delete the lease from `leaseMap` and the
  backend (without the key deletions).
- **Found**: 2026-10-17, auditing the contract of `lease.NewLessor` for `NewServer`'s proof
  (unit N1 of the server-construction unit).
