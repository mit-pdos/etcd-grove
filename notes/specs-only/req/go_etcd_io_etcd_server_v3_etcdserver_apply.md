# Requirements on `go.etcd.io/etcd/server/v3/etcdserver/apply` (3a)


## from 2c

What the request path (2c) needs of the apply layer (3a):

1. **The result** (`ApiReq.lean`'s `applyResult γ x ir res`, transparent over `*apply.Result`'s
   fields): `Err` `nil` and `Resp` the reply of the request's kind (`irrReply`: a `*pb.<Kind>Response`,
   W0's reply predicates) for a success; `Err` a server error with `srvErrOf err e` for an error
   answer `e`; `Physc` `nil` or, for a compaction, a channel closed once mvcc's compaction is done;
   `Trace` a trace (`traceAt`). An alarm activation's `Resp` an `*AlarmResponse`.
   ```go
   if result.Err != nil { return nil, result.Err }   // v3_server.go:1019
   return resp.(*pb.PutResponse), nil
   ```
2. **The answer is `Step`'s at the entry's state** (W0's): the uber-applier's answer for a committed
   request at the state `histAt N k σ` is one `Step who rq σ σ' res` allows (with `σ'` the next
   history point), `who` the header's `Username`; a stale header `AuthRevision` is
   `ErrAuthOldRevision`, changing nothing (2d keeps the update unfired). If the answer is a fixed
   function of the state (the code is deterministic), exposing it lets 2d's commit-time firing use
   it (`answered`) and 2c's read registry fire once per point.
3. **`CheckTxnAuth(as, ai, lessor, r)`** (a read-only `Txn`'s check, `v3_server.go:355`): `nil` only
   if `σ.permits who (RequestOp.txn ...).perms (...).leases` at the auth store's state (a reached
   one), else `permErr`-class errors or `ErrAuthOldRevision`.

## from 2d

What the apply thread (2d: `applyEntryNormal`, `applySnapshot`, `NewUberApplier`) needs of the apply
layer (3a). 2d's `ApiApply.lean` declares, provisionally for 3a, `MemberCfg` and `applyStep mc σ e σ'
res` (the apply's model of a committed entry, with `applyStep_fun`): replace them by 3a's names.

1. **`apply.Apply(lg, e, uberApply, w, shouldApplyV3)`** (as the old `apply-uber-contract`
   example: one spec parametric in the uber-applier's method contract, which the constructor
   `NewUberApplier` establishes, for every uber-applier the server's field may hold): with
   `shouldApplyV3`, at a state machine at `histAt γ (k-1) σ` (the member's mvcc/lessor/auth/
   membership/alarms: 3a's state-machine predicate over theirs), for the committed normal entry `e`
   at index `k`: the state machine moves to `histAt γ k σ'` with `applyStep mc σ e σ' res`, the
   result `ar` holds `res` (2c's `applyResult`), every write transaction's post-lock hook sets the
   consistent index to the applying index `k` (`Cindex`); the request id is the entry's. Without
   `shouldApplyV3` (the replay below the consistent index): nothing changes but the in-memory
   membership's v2 view, no result (or one nobody waits for).
   ```go
   ar, id := apply.Apply(s.lg, e, s.uberApply, s.w, shouldApplyV3)        // server.go:1994
   ```
2. **`applyStep` is a function** (`applyStep_fun`) of the state, the entry and the member's
   configuration (the lease minimum TTL), refining W0's `Step` for client requests and `EnvStep`
   for the internal ones (`irrStep`, 2c's): the cluster fires the proposer's update with it at the
   commit, so the proposer's apply must compute the same answer.
3. **`NewUberApplier()`** (`server.go:1181`): its contract at the server's current stores (after a
   snapshot install too: `applySnapshot` rebuilds it).
4. **The `SnapshotServer` contract**: the applier calls `ForceSnapshot()` with `forceSnapW s` lent
   by the apply thread (`EtcdServer.ForceSnapshot.spec`).
Used by: `applyEntryNormal.spec`, `applySnapshot.spec`.
