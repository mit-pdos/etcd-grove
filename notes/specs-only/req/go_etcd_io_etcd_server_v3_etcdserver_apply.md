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

## from 2d (round 1)

1. `applyStep mc σ e σ' res` is at the cluster's **shared** configuration `mc` (`Names.mc`, fixed at
   allocation; the coordinator's decision): a function of the entry and the shared configuration
   (`applyStep_fun`), and a step of the model (`applyStep_reach : applyStep … σ σ' … → Reach σ σ'`).
   The per-member alternative (each member's own minimum TTL) is recorded as open in
   `batch-2d.md`.
2. A conf-change entry's step: the membership's validation and change at `σ.members` (2e's), its
   answer a success iff accepted.

## from 3c

The lessor's API: `Spec/go_etcd_io/etcd/server/v3/lease/Api.lean` (namespace `Lease`). The applier
is its writer, holding `Lease.lessorState γl n ls` (and, inside an apply, 4a's `Lease.beApplyTok
ls.be`). What 3c's specs give and need there:

1. **`LeaseGrant`** (`apply/backend.go:84`): `lessor.Grant.spec`: errors `ErrLeaseNotFound` (id `0`),
   `ErrLeaseTTLTooLarge`, `ErrLeaseExists` (live), the state unchanged; else the state
   `ls.grant id l (grantTTL c ttl)` at `n + 1`, `grantTTL c ttl = max ttl c.minTTL` (`c.minTTL` the
   member's `MinLeaseTTL`: 2d's `MemberCfg`'s lease minimum, the per-member TTL of
   `nonissues/etcd-lease-ttl-differs-across-members.md`). `l.ID`, `l.TTL()`: `lessorAt_obj`,
   `leaseObj_id`, `Lease.TTL.spec`. The errors are distinct non-nil values (`Lease.init.spec`).
2. **`LeaseRevoke`** (`apply/backend.go:95`): `lessor.Revoke.spec` takes `ls.rd ≠ func.nil` (mvcc's
   `NewStore` sets it) and the deleter's contract `Lease.rdOk γl ls.rd n ls P D Q` (mvcc's, 3e:
   `req/..._storage_mvcc.md`, "from 3c"); its post: `ErrLeaseNotFound` (not live), or the keys `ks`
   of the lease's object (sorted, `keyLt`), mvcc's `Q ks n' ls'`, the state `ls'.remove id` at
   `n' + 1`. With the attachment invariant (mvcc's item 2: the object's keys are the keys whose
   record names the lease), `ks` are W0's `State.attachedKVs σ id`'s keys and the step is
   `State.revoke`.
3. **`LeaseCheckpoint`** (`apply/backend.go:101`): `lessor.Checkpoint.spec`: `nil`, the state
   unchanged (the remaining TTL is not modelled): a no-op of the model.
4. **The auth applier's `checkLeasePuts`** (`apply/auth.go:199`) and txn's `checkLease`
   (`txn/put.go:83`, 3b): `lessor.Lookup.spec` and `Lease.Keys.spec` at the writer's own
   `lessorAt γl n ls` answer from `ls` exactly (`lessorState_le`, `lessorAt_agree`).
5. **The apply's model** (`applyStep`, provisional, yours): a grant, revoke or checkpoint entry moves
   the lessor's state as above; 2d's invariant records which lessor history index each entry ends
   at (`req/..._etcdserver.md`, "from 3c").
