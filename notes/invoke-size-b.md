# The encoded-size bound: leasing, recipes, k8s (branch `invoke-size-b`, 2026-10-30)

Plan items 2-4 of `notes/invoke-size.md` (leasing, recipes, k8s), done beside `invoke-size`'s
concurrency work (another branch). The design is `notes/decisions.md`, "The encoded-size bound at
grpc's send side"; this file records only this branch's state and departures.

## State

| Package | State |
|---|---|
| recipes | done but for four proofs blocked on the key-length bound on etcd's state (below); `584186e94e` |
| leasing | done but for `revokeLeaseKvs`, blocked on the same bound (below); `b56be48c57` |
| k8s | kubernetes client and etcd3 store done, the cacher unchanged and building; `eb00a8b15f`, `3e05cb4f0d`. `k8setcd3`'s closed theorem is pass 4 (below) |

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

## Keys read from etcd: blocked on the key-length bound

Some requests carry a key that came from a response. Nothing bounded such a key (the etcd model had
no length bound on its keys; the client's receive limit, `math.MaxInt32` by default, gives only
`2 ^ 31`). The user chose (2026-10-30) a key-length bound on etcd's state: every key at most
`2 ^ 27` (`etcdKeyMax`), designed separately as a law of the clients' model (likely
`etcdState_keys` in `EtcdModel`). The proofs that need it are left failing, each at the goal it
needs:

| Proof | Where | The goal |
|---|---|---|
| `Queue.Dequeue` | `Queue__Dequeue.lean:111` | `claimFirstKey`'s premise for the keys `Get(kp, WithFirstRev())` returned: `v.key.length ≤ 2 ^ 28` for `v` in the response |
| | `:222` | `deleteRevKey`'s `e.key.length ≤ 2 ^ 28` for a watch event's key `e.key` |
| `PriorityQueue.Dequeue` | `PriorityQueue__Dequeue.lean:115`, `:226` | the same two |
| `RWMutex.waitOnLastRev` | `RWMutex__waitOnLastRev.lean:192` | `WaitEvents`' `w.key.length ≤ 2 ^ 28` for the key `w` a `Get` returned |
| `DoubleBarrier.Leave` | `DoubleBarrier__Leave.lean:389` | `WaitEvents`' `wh.key.length ≤ 2 ^ 28` (the highest waiter's key, from a `Get`) |
| | `:375`, `:418` (the `leave_not_lowest` macro) | `WaitEvents`' `wl.key.length ≤ 2 ^ 28` (the lowest waiter's key) |
| `leasingKV.revokeLeaseKvs` | `leasingKV__revokeLeaseKvs.lean:111` | `v.key.length ≤ 2 ^ 27` for a key `v` of the lease keys a `Get` returned (the `have Hk`; the rest of the call is proved from it) |

With the bound (`2 ^ 27 ≤ 2 ^ 28`) each goal is one application of the law to the key's
membership in etcd's state. The modules that import these proofs do not build until then: recipes'
`Link`, `Results`, `Vertical`; leasing's `Link`, `Results`. With the leasing goal admitted
locally (not committed), leasing's `Link` and `Results` build.

## leasing (approved 2026-10-30; `notes/decisions.md`, "Leasing's sizes")

- `NewKV` takes `pfx.length ≤ 2 ^ 26`, kept in `isLeasingKV` (`isLeasingKV_kv` returns it).
- `Get`, `Put`, `Delete` and `Do` (get, put, delete) take `OpShape (2 ^ 27) (2 ^ 27) (2 ^ 28)` of
  their operation; `get`, `put`, `delete`, `deleteRange`, `tryModifyOp` the same.
- `Commit`, `serverTxn` and `Do`'s transaction (`doTxnPre pfx`) take `LTxnBuild.sizeOk pfx b`
  (`InvLeasingKV`): every comparison's and operation's string at most `N` bytes, and
  `(5 * n + 1) * (3 * (|pfx| + N) + 256) ≤ 2 ^ 30`, `n` the comparisons and operations.
  `serverTxn_sizeOk` (`InvLeasingCommitLemmas`) bounds the server transaction with L-s4.
- L-s4 is in `cache/v3/InvEtcdTxn.lean`: `CmpModel.bytesLe`, `TxnOp.bytesLe`, `TxnModel.bytesLe`,
  `TxnOp.nodes`, `TxnModel.nodes`, `txnSizeOk_of_bounds`, `TxnModel.bytesLe_empty`/`nodes_empty`,
  `bytesLe_append`/`nodes_append` (the builder's steps). Also there: `txnOpOf_wireLen_le` and
  `keyWatch_size`.
- `guardKeys`, `guardRanges`, `guard` and `fallback` return `guardOf` of each string (the
  operation's key and range end, prefixed or not, no value) and their counts (one, two, three, one
  per operation); `guardRanges` and `guard` take the operations' keys and range ends at most
  `2 ^ 27` (from `sizeOk`: `LTxnBuild.sizeOk_ops`).
- `rescind`, `waitRescind`, `monitorLease`, `revoke` take the key at most `2 ^ 27`; `revoke` also
  `OpShape` of its operation; `acquire` `OpShape (2 ^ 27) 0 0` (Go's `OpGet(key)`);
  `deleteRangeRPC`, `revokeRange` the key and range end at most `2 ^ 27`.
- The lease cache keeps no bound: every request on a cached key gets the key from the user's
  operation. The proposal had the cache keep it; nothing needs it.

## k8s

- `linkvtxn/Calls.lean` (the example, now allowed): `client_List_st` takes
  `hsz : opSizeOk (opGetModel listFrom [withRangeM listTo])` and `txn_Commit_st`
  `hsz : txnSizeOk (txnWireOf b.model)`. Their callers in `linkvtxn` are not updated (pass 4).
- `kubernetes.Client`: `Get` takes `key.length ≤ 2 ^ 27` (for `opts.Revision' = 0`, the path
  that reads etcd); `OptimisticPut` `key.length ≤ 2 ^ 27` and `val.length ≤ 2 ^ 28` (for
  `opts.LeaseID' = 0`); `OptimisticDelete` `key.length ≤ 2 ^ 27`. `clientTxn_size`
  (`kubernetes/Defs.lean`) bounds their transactions.
- etcd3 store: `Get`, `GetCurrentResourceVersion`, `Create`, `Delete`, `GuaranteedUpdate` take
  `(c.pathPrefix ++ k).length ≤ 2 ^ 27`; `getCurrentState`, `deleteOnce`, `conditionalDelete`,
  `updateOnce` `key.length ≤ 2 ^ 27`. `Create` takes `c.S.storedSizeOk o` and `GuaranteedUpdate`
  `storedSizeOk` of every object its update returns (`ObjCodec.storedSizeOk`, `Contract.lean`:
  every encoding of the object is at most `2 ^ 28` bytes); `updateOnce` the same of its `o'`.
- The cacher builds unchanged.
- `k8setcd3`'s closed theorem (pass 4, untouched) will need: the callers of `client_List_st` and
  `txn_Commit_st` in `linkvtxn` to discharge `hsz` (`GenIn`'s keys and values); in `k8setcd3`'s
  `call.lean`, `(pathPrefix ++ k).length ≤ 2 ^ 27` for its keys, and `storedSizeOk` of the
  objects it creates and updates (`encodeV0(name, val)`'s length, with `GenIn`'s value bound).

## Departures

- Internal specs take the bounds in a simple per-argument form (`key.length ≤ 2 ^ 28`), not the
  exact `txnSizeOk` of their request. The laws above turn these bounds into the request's
  predicate.
- `ownRemoteKV` carries a pure conjunct (the key's bound). The other choice was a premise on
  `RemoteKV.Delete`/`Put` plus the bound in `rwMyKey`/`dbMyKey`.
- `isRWMutex` keeps `2 ^ 27 + 1`, the stored prefix ends in `/`. The constructor's premise is on
  the user's prefix.
- The leasing premise is on `OpFull`s (`OpShape N N N` of each operation, `CmpModel.bytesLe N` of
  each comparison) and counts the operations, not on the user's `TxnModel`: the guards read the
  operations' range ends, which a put's `TxnOp` drops. The count is the user transaction's
  `TxnModel.nodes` (the operations are plain). `5 * n + 1` over-counts the guards (at most two per
  operation; three is what the per-function counts give without splitting by kind).
- The internal guard and fallback specs gained posts (`guardOf`, counts) and `guardRanges`/`guard`
  a premise: not in the draft, needed by the approved `Commit` bound.
