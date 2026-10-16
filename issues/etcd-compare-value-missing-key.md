---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#10566 issue open: same behavior (`Compare(Value(k), "!=", v)` false on a missing key), reported as a bug in 2019, reopened 2026; no fix
  - etcd-io/etcd#10571 issue closed: related, not this bug (a request for AND/OR/NOT in a txn's comparisons, to combine existence and value)
---

# etcdserver: a value comparison on a missing key is false for every operator, undocumented

- **Status**: documentation. The behavior is deliberate (a code comment says so) but no API
  documentation states it, and the website's API page suggests the opposite.
- **Where**: `server/etcdserver/txn/txn.go:268-292` (`applyCompare`, at the pinned `107edf7e4`);
  `api/etcdserverpb/rpc.proto:606-650` (`message Compare`); the website's
  `content/en/docs/v3.6/learning/api.md`, section "Transaction".
- **What happens**: when a comparison's range selects no key, `applyCompare` compares the zero
  `KeyValue` (revisions, version, lease `0`) for the `VERSION`, `CREATE`, `MOD` and `LEASE`
  targets, but returns `false` for `VALUE` whatever the operator:

  ```go
  // server/etcdserver/txn/txn.go:278-285 (etcd 107edf7e4)
  	if len(rr.KVs) == 0 {
  		if c.Target == pb.Compare_VALUE {
  			// Always fail if comparing a value on a key/keys that doesn't exist;
  			// nil == empty string in grpc; no way to represent missing value
  			return false
  		}
  		return compareKV(c, &mvccpb.KeyValue{})
  	}
  ```

  So `If(Compare(Value(k), "!=", v)).Then(OpPut(k, v))` on a missing `k` takes the `Else`
  branch, and `Compare(Value(k), "=", v)` is false as well. Reproduction: the issue's program
  (etcd#10566), unchanged in behavior at the pin.
- **Expected**: the API documentation states the rule. `rpc.proto`'s `Compare` says nothing
  about missing keys, and the API page says a comparison "may check for the absence or presence
  of a value", which a value comparison cannot do.
- **How the proof handles it**: the spec states the rule. `txn.applyCompare.spec`
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/applyCompare.lean:30-35`) returns
  `cmpHolds (stateAfter log) c`, and `cmpHolds`
  (`Proof/go_etcd_io/etcd/cache/v3/InvEtcdTxn.lean:124-127`) is `(c.target != .value) && …`
  when the range selects no key. Every verified client is proved against this rule.
- **Possible fixes**: document the rule in `rpc.proto` (`Compare.value`, or the message comment)
  and on the API page, with the existence idiom (`ModRevision(k) = 0` / `> 0`). Changing the
  rule would change the outcome of existing transactions, so it would be an API change.
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#10566 (`notes/bug-triage/etcd-10566.md`).
