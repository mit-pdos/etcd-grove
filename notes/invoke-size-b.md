# The encoded-size bound: leasing, recipes, k8s (branch `invoke-size-b`, 2026-10-30)

Plan items 2-4 of `notes/invoke-size.md` (leasing, recipes, k8s), done beside `invoke-size`'s
concurrency work (another branch). The design is `notes/decisions.md`, "The encoded-size bound at
grpc's send side"; this file records only this branch's state and departures.

## State

| Package | State |
|---|---|
| recipes | done but for the four functions that send a key read from a response (below); `584186e94e` |
| leasing | not started: needs a statement beyond the draft (below) |
| k8s | not started: blocked by the example `linkvtxn/Calls.lean`, which this branch may not touch (below) |

### recipes

**The bounds.**
- The constructors take a prefix of at most `2 ^ 27` bytes:
  - `NewBarrier`, `NewQueue`, `NewPriorityQueue`, `NewDoubleBarrier` take `key.length ≤ 2 ^ 27`;
  - `NewRWMutex` takes `pfx.length ≤ 2 ^ 27`.
- Each object keeps the bound in its predicate:
  - `isBarrier`, `isQueue`, `isPriorityQueue`, `isDoubleBarrier`;
  - `isRWMutex` keeps `pfx ++ "/"` at most `2 ^ 27 + 1`.
- `Queue.Enqueue` and `PriorityQueue.Enqueue` take `val.length ≤ 2 ^ 28`.

**The internal helpers** take bounds on their arguments:
- `putNewKV`, `newKV`, `newEphemeralKV`: key and value at most `2 ^ 28`. `newKey`: the key.
- `newUniqueKV`, `newUniqueEphemeralKV(Key)`, `newSequentialKV`: a prefix of at most
  `2 ^ 27 + 2 ^ 10` and a value of at most `2 ^ 28`. The key they make (the prefix, `/`, at most
  20 digits) is then at most `2 ^ 28`.
- `deleteRevKey`, `WaitEvents`: the key at most `2 ^ 28`. `WaitPrefixEvents`: the prefix.
  `claimFirstKey`: every key.
- `RWMutex.waitOnLastRev`: `bp`.
- `RemoteKV.Put`: the value.

`ownRemoteKV` keeps its key's bound (`2 ^ 28`), so `RemoteKV.Delete`, `RUnlock`, `Unlock` and the
double barrier's key need nothing more. The laws are in `InvRecipesClient`:
- `newKeyTxn_size`, `deleteRevTxn_size`;
- `getOp_size`, `topOp_size`, `deleteOp_size`, `putOp_size`;
- `keyWatchOp_size`, `prefixWatchOp_size`;
- `decimal_sint_length_le`, `uniqueKey_length_le`.

`InvRecipesSeq` adds `lastKeyOp_size`, `seqKey_length_le` and `seqTxn_size`. `InvDoubleBarrier`
adds `waitersOp_size` and `leaveOp_size`.

**Results.** `queue_vertical` takes `hkpl : kp.length ≤ 2 ^ 27`, and its `Enqueue` triple takes
`⌜val.length ≤ 2 ^ 28⌝`. The specs in `Results.lean` change with their specs.

**Builds.** Every recipes module builds, except these four proofs and the modules that import them
(`Link`, `Results`, `Vertical`):
- `Queue.Dequeue`: lines 111 and 222, `claimFirstKey`'s and `deleteRevKey`'s key bound;
- `PriorityQueue.Dequeue`: lines 115 and 226, the same;
- `RWMutex.waitOnLastRev`: line 192, `WaitEvents`' key;
- `DoubleBarrier.Leave`: lines 389 and the `leave_not_lowest` macro's two uses (375, 418),
  `WaitEvents`' key.

`Vertical` is edited but unchecked.

**Concurrency.** The recipes use only `concurrency`'s session (`isSession`, `Session.Client`,
`Session.Lease`) and pure lemmas of `InvMutexLemmas`/`InvSTMAtomic`. If the concurrency branch
changes `isSession`, the merge must revisit them.

## Statement question 1: keys read from etcd (recipes, leasing)

Each remaining failure sends a request on a key that came from a response:
- `Dequeue` claims the first key `Get(kp, WithFirstRev())` returned (`claimFirstKey` →
  `deleteRevKey`), or the key of a watch event (`deleteRevKey`);
- `waitOnLastRev` and `Leave` watch a key `Get` returned (`WaitEvents`).

Nothing bounds such a key:
- the etcd model has no length bound on its keys;
- the client's receive limit (`MaxCallRecvMsgSize`, `math.MaxInt32` by default) gives at most
  `2 ^ 31`, which the draft's `2 ^ 30` cannot use;
- `deleteRevKey` sends the key twice.

leasing has the same problem: `revokeLeaseKvs` revokes the keys a `Get` of the lease keys returned.

The draft's table assumes that the recipes' strings are "the prefix + bounded suffixes", but these
keys are under the prefix with any suffix. Options:
- (a) a trusted fact that every key in etcd's state is shorter than the server's request limit:
  the receive-size fact, carried into the model as an invariant of `etcdState`;
- (b) the four specs take a premise bounding every key under the prefix: a protocol invariant
  over the prefix, which the specs cannot state today;
- (c) the client's `Get` and watch contracts return keys of at most a bound, a new
  trust-boundary statement about the client.

## Statement question 2: leasing's own transactions

The draft gives "each KV operation of the leasing KV gains the client's predicate on its
arguments". That premise cannot discharge leasing's own requests, because each one carries the
user's operation and the prefixed key several times:
- `acquire(key, op)`: comparisons on `pfx+key` and on the lease value, and `op`, `Put(pfx+key)` in
  `Then`, `op`, `Get(pfx+key)` in `Else`. That is twice the user's operation plus three times
  `pfx+key`: up to 5 · 2^30 under `opSizeOk`.
- `serverTxn`:
  - the user's transaction nested (`OpTxn`);
  - a guard for each write operation (`pfx+key`; for a range, the key and range end, prefixed
    and not);
  - a fallback get for each write operation (`pfx+key`, `pfx+end`).

  With `txnSizeOk` of the user's transaction, the server's transaction can be about three times
  `2 ^ 30` plus the number of operations times `|pfx|`.
- `deleteRangeRPC`, `revoke`, `rescind`, `tryModifyOp`: the prefixed key and the operation.

A proposal, which would need approval:
- `NewKV` takes `pfx.length ≤ 2 ^ 26`, kept in `isLeasingKV`.
- `Get`, `Put`, `Delete` and `Do` take `OpShape (2 ^ 27) (2 ^ 27) (2 ^ 28)` of their operation
  (the existing vocabulary in `InvOp`) instead of `opSizeOk`.
- `txnLeasing.Commit` takes a leasing predicate: the user's transaction's `txnWireLen` at most
  `2 ^ 27`, and its node count (L-s4's `TxnModel.nodes`, not yet written) times `2 ^ 26 + 2 ^ 10`
  at most `2 ^ 28`.
- The lease cache's keys keep the operation's key bound (`monitorLease`, `rescind`, `revoke`).
- `revokeLeaseKvs` needs question 1's answer.

## k8s: blocked by an example

`Proof/go_etcd_io/etcd/client/v3/kubernetes/Defs.lean` imports
`Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Calls`, for the generic half: `srvStart`,
`kvRegs_*`, `rangeReply_state'`. That module no longer builds since pass 1:
- `client_List_st` (`Calls.lean:265`) needs `opSizeOk (opGetModel listFrom [withRangeM listTo])`;
- `txn_Commit_st` (`:344`, `:392`) needs `txnSizeOk (txnWireOf b.model)`.

This branch may not touch the examples, so neither the kubernetes client nor the etcd3 store
can be checked. Two ways to unblock it:
- give those two theorems the size hypotheses, which pass 5 needs anyway, with linkvtxn's
  `GenIn` discharging them;
- move the generic half out of the example.

Once unblocked, the plan, as the draft's section 7 says:
- `Client.Get` gains `opSizeOk (opGetModel key [])`, passed to `client_range_any`'s `hsz`.
- `Client.OptimisticPut`/`OptimisticDelete` gain `txnSizeOk` of their transaction (`optPutTxn`,
  `optDelTxn`, on the wire), passed to `client_txn_any`.
- The etcd3 store's specs take the key's bound (`c.pathPrefix ++ k`) and the encoded objects'
  bound. The encoded objects are `c.S.encode o` for `Create` and every object
  `GuaranteedUpdate`'s update returns. The specs affected: `Create`, `Get`, `Delete`,
  `GuaranteedUpdate`, `GetCurrentResourceVersion`, `getCurrentState`, `updateOnce`.
- The cacher passes the bounds on.
- `k8setcd3`'s closed theorem is pass 4 and is left alone. It will need:
  - `GenIn`'s keys (`a`, `b`, `c`) and the value bound from `workloadVals`;
  - `encodeV0(name, val)`'s length computed;
  - the path prefix's length.

## Departures

- Internal specs take the bounds in a simple per-argument form (`key.length ≤ 2 ^ 28`), not the
  exact `txnSizeOk` of their request. The laws above turn these bounds into the request's
  predicate.
- `ownRemoteKV` carries a pure conjunct (the key's bound). The other choice was a premise on
  `RemoteKV.Delete`/`Put` plus the bound in `rwMyKey`/`dbMyKey`.
- `isRWMutex` keeps `2 ^ 27 + 1`, the stored prefix ends in `/`. The constructor's premise is on
  the user's prefix.
