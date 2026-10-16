---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#21128 issue closed: this bug (closed by the stale bot, not fixed)
  - etcd-io/etcd#21165 pr open: proposed fix (Resign on every waitDeletes error)
  - etcd-io/etcd#22123 issue open: related, not this bug (Resign clears the leadership state when its own transaction fails; same "key left, Election forgot it" outcome)
  - etcd-io/etcd#22124 pr open: fix of #22123
---

# concurrency: a failed `Election.Campaign` leaves its key in etcd, and `Resign` cannot remove it

- **Status**: bug (present at the pin). The election stalls behind an orphaned candidate key
  until the session ends.
- **Where**: `client/v3/concurrency/election.go` at the etcd pin `107edf7e4` (`etc/goose.py`):
  `Election.Campaign` (lines 69-107), its `waitDeletes` error branch (lines 93-103), and
  `Election.Resign` (lines 132-145).
- **What happens**: `Campaign` puts `pfx/<lease>`, then waits in `waitDeletes`. If the wait fails
  while `ctx` is live (a `Get` error, or a watch error such as `ErrCompacted`), the `default:`
  branch sets `e.leaderSession = nil` and returns the error. The key stays in etcd on the
  session's lease, and `e.Key()` still names it. `Resign` returns `nil` at once when
  `leaderSession == nil`, so the caller cannot delete the key through the `Election`. Until the
  session ends, the key is a candidate. Once the older keys are gone, `Leader()` reports it, while
  no process acts as leader, and later candidates queue behind it. Reproduction (a unit test with
  fakes, in `client/v3/concurrency`, at the pin,
  `issues/etcd-election-campaign-error-orphan-key/campaign_error_key_test.go`). Its test function
  (the fake `Lease`, `KV` and `Txn` are in the file):

  ```go
  func TestCampaignErrorLeavesKeyResignNoop(t *testing.T) {
  	kv := &fakeKV{keys: map[string]bool{}}
  	cli := clientv3.NewCtxClient(context.Background())
  	cli.KV, cli.Lease = kv, fakeLease{}
  	s, err := concurrency.NewSession(cli, concurrency.WithLease(0x10))
  	if err != nil {
  		t.Fatal(err)
  	}
  	defer func() { s.Orphan(); <-s.Done() }()
  	e := concurrency.NewElection(s, "/el")
  	if err := e.Campaign(context.Background(), "v"); err == nil {
  		t.Fatal("expected an error")
  	}
  	n := kv.txns
  	if err := e.Resign(context.Background()); err != nil {
  		t.Fatal(err)
  	}
  	if len(kv.keys) != 0 {
  		t.Errorf("key %v left in etcd; Resign issued %d txns; Key()=%q", kv.keys, kv.txns-n, e.Key())
  	}
  }
  ```

  At the pin this fails: `key map[/el/10:true] left in etcd; Resign issued 0 txns; Key()="/el/10"`.
  Against a real cluster, the reporter of #21128 triggers the same branch by compacting often, so
  that `waitDelete`'s watch ends with `ErrCompacted`.
- **Expected**: `Campaign`'s doc comment says a non-recoverable error ends the campaign, and the
  only clean-up it documents is for a canceled context. After a failed `Campaign`, the caller
  expects either that the key is gone or that `Resign` removes it, as #21128 asks. Closing the
  session is the only workaround, and it also removes every other key on the session.
- **How the proof handles it**: the proof admits it. `Election.Campaign.spec`'s error outcome is
  `∃ st', electionState e s st'`
  (`Spec/go_etcd_io/etcd/client/v3/concurrency/Election__Campaign.lean:53`), which says nothing
  about the key in etcd. `Election.Resign.spec`'s first case
  (`Spec/go_etcd_io/etcd/client/v3/concurrency/Election__Resign.lean:40`) is the no-op with no
  leader session. The stronger statement that would exclude it (`election-key-accountable`) is in
  `notes/bug-triage/etcd-21128.md`.
- **Possible fixes**: call `e.Resign(client.Ctx())` on every `waitDeletes` error (PR #21165), or
  keep `leaderSession` set so that the caller can `Resign`. Either way `Resign` must keep its state
  when its own transaction fails (#22124), or the key can be forgotten one step later.
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#21128 against the `concurrency` specs.
