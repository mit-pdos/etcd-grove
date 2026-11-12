# Batch 1f (client recipes): report

Author's report. Everything builds (`etc/specs-build.sh --dir
SpecPlan/Spec/go_etcd_io/etcd/client/v3/experimental/recipes`: 39 modules, after W0's round-1 repairs); the
snippets vet (`cd examples && go vet ./specreq/recipes/`, gofmt-clean).

## Files

| path | what |
|---|---|
| `SpecPlan/Spec/go_etcd_io/etcd/client/v3/experimental/recipes/Api.lean` (`Recipes`, new namespace) | the vocabulary, the laws, the slots for 1b and 1d |
| `SpecPlan/Spec/go_etcd_io/etcd/client/v3/experimental/recipes/*.lean` | 38 specs: every function with an old spec |
| `examples/specreq/recipes/{barrier,queue,pqueue,rwmutex,doublebarrier,watch}.go` | 11 requirement snippets |
| `nonissues/recipes-dbarrier-leave-without-key.md` (+ `nonissues/INDEX.md` regenerated) | a new finding (below) |
| `notes/specs-only/req/go_etcd_io_etcd_client_v3.md` (`## from 1f`), `req/go_etcd_io_etcd_client_v3_concurrency.md` (new), `req/go_etcd_io_etcd_api_v3.md` (new) | needs of 1b, 1d, W0 |

Specs: `deleteRevKey`, `claimFirstKey`; `putNewKV`, `newKV`, `newKey`, `newUniqueKV`,
`newSequentialKV`, `newEphemeralKV`, `newUniqueEphemeralKV`, `newUniqueEphemeralKey`,
`RemoteKV.{Key,Revision,Value,Delete,Put}`; `waitEvents`, `WaitEvents`, `WaitPrefixEvents`;
`NewBarrier`, `Barrier.{Hold,Release,Wait}`; `NewQueue`, `Queue.{Enqueue,Dequeue}`;
`NewPriorityQueue`, `PriorityQueue.{Enqueue,Dequeue}`; `NewRWMutex`,
`RWMutex.{Lock,RLock,Unlock,RUnlock,waitOnLastRev}`; `NewDoubleBarrier`,
`DoubleBarrier.{Enter,Leave,enteredClients}`. Left out: none (no other function in the package).

Users: only etcd's integration tests (`tests/integration/clientv3/experimental/recipes`: barrier,
double barrier, queue, priority queue, RWMutex, closed-watch tests); nothing in the pinned
etcd/raft, Kubernetes or `examples/` imports the package.

## Exported vocabulary (`Recipes`)

Pure: `decStr`, `padDec` (Go's `%v`, `%0wd`), `uniqueKeyIn p k` (`p/<UnixNano>`), `seqKey`, `seqBase`,
`pqPrefix`, `pfxRange`, `waitersPfx`, `readyKey`; the requests `putReq0`, `delReq`, `putNewReq`
(create if absent), `deleteRevReq` (delete at a mod revision), `seqPutReq` (`newSequentialKV`'s
guarded put); `txnSucceeded`, `txnCmpFailed`; the guarantees `frontByRev` (queue front: least mod
revision), `frontByKey rng s r0` (priority front: every key before it written after `r0`),
`goneAt h k r` (absent, or deleted, at `r`), `rwHeld rng R s` (no key of `rng` below `R`: the mutex
acquired), `createdAt`, `readyPutAt`, `storeCount`; the watch's `WatchEv`, `watchHist h rg rev`
(every event of `rg` from `rev`, in order), `WatchEv.typ`, `.kvM`, `matchCount`; `RecipeErr`,
`RKSt`; `okOrErr`, `putNewRet`, `deleteRevRet` (what a call returns for its request's answer);
`dbWrite key count id leave σ rq` (the double barrier's writes, guarded).

Resources: `etcdPeek γ` (def, persistent: a no-op atomic update; reads are made of it);
`recipeErr e` (the sentinels' values); `rkOwn rk γ who st` (exclusive), `ekOwn` (def);
`barrierAt`, `queueAt`, `pqueueAt` (persistent handles); `dbOwn`, `rwmOwn` (exclusive: `myKey`);
`dbPerm γ who key count id leave` (def, persistent permission for `Enter`'s or `Leave`'s writes).
**Slots**: `sessionAt s γ who id` (1d: = `Concurrency.isSession`, same signature), `watchChanAt wc
γ rg rev seen`, `watchEvOwn p e` (1b / 3h).

Laws: `handles_persistent`, `recipeErr_ne`, `recipeErr_fresh` (no `callErr` value is a sentinel),
`errorsIs_recipeErr`, `init.spec` (the five sentinels), slots `watchChanAt_recv` (a receive:
closed, an error response, or events extending a prefix of `watchHist` with `etcdLb`),
`watchEvOwn_unfold`.

## The design

* **Operations with a linearization point take the caller's atomic update (TaDa)**, in W0's KV
  shape: `Hold`, `Release`, `RemoteKV.Put/Delete`, `putNewKV`, `deleteRevKey`, `newKV`... (the
  request's `Step`, every definite answer linearized, `indefCall` otherwise); loops with no-op
  attempts (`newUniqueKV`, `Queue.Enqueue`, the lock key's creation, `newSequentialKV`) take one
  update that the code aborts on a failed comparison and fires once; `Queue.Dequeue` /
  `PriorityQueue.Dequeue` fire it **at the claim**, with the claimed key the queue's front there.
* **Reads** are made of `etcdPeek γ` (every caller can give it), and give `etcdLb` facts.
* **Waits** return history facts anchored at a state `σ0` the caller passes (`etcdLb γ σ0`):
  `Barrier.Wait` (`goneAt` after `σ0`), `RWMutex.Lock/RLock` (`rwHeld` at a state after its key's
  creation: revision fencing), `DoubleBarrier.Enter/Leave`.
* **`DoubleBarrier`'s writes go through a guarded permission** (`dbPerm`), not one update per call:
  each call makes up to three writes, none a linearization point.

## Main changes from the old specs

* The recipes' client invariant (`isEtcdRecipesClient`, `isRecipesKV`: keys under a prefix only the
  recipes write) is gone: every spec holds whoever else writes. Prefix, length (`recipesStrMax`,
  `recipesPfxMax`), `kp ≠ []` and revision-bound premises dropped; any lease.
* Answers linearized (`ErrKeyExists`, etcd's errors), as W0's.
* **Queue is FIFO at the claim** (`frontByRev`), on both paths, whoever else writes the prefix:
  the old spec gave the order at the read. This answers the open point of
  `nonissues/recipes-pqueue-dequeue-order.md` ("whether it breaks FIFO for `Queue` was not
  checked"): it does not (the first put after the read is the least mod revision at the claim).
* **PriorityQueue**: one condition for both paths (`frontByKey ... σ0.kv.rev`): first in priority
  order among the items present when the call started; a later lower-priority arrival may be
  returned (the known non-linearizability).
* Watches may close (the fork's fix for `issues/recipes-dequeue-closed-watch.md`,
  `recipes-barrier-wait-closed-watch.md`): the specs allow it.
* `Barrier.Wait`'s fact is `goneAt` (absent, or deleted at a revision), not absence: a revision may
  delete and re-put a key (sibling nested transactions, `issues/etcd-txn-check-intervals-sibling.md`),
  and `Wait` then returns `nil` though the key was never absent.

## Premises kept (the code needs them)

`ts ≠ []` (`waitEvents`, `WaitEvents`: an empty slice is indexed), `0 < rev` (`WaitEvents`: a scope
restriction, every caller passes a revision it read), `st.live` for `RemoteKV.Put` (nil interface),
`myKey` set for `Unlock`/`RUnlock`/`Leave`/`waitOnLastRev` (nil dereference).

## Finding

`nonissues/recipes-dbarrier-leave-without-key.md` (blocks-proof: no): `DoubleBarrier.Leave` panics
on a nil `myKey` when others wait and this process's `Enter` did not create a key; also notes
`WaitEvents`' empty-slice panic. Found by code reading; no caller does it.

## Decisions for the user

1. **TaDa for the queues, barrier and lock key; a permission for the double barrier.** 1d chose a
   permission (`Concurrency.etcdPerm γ T`) for all of `concurrency`. The recipes' TaDa updates are
   stronger (a caller can linearize a queue at the claim); the permission is simpler for calls with
   several writes. Choose whether the two batches should align (one shape).
2. **Time exclusion is not provable**: the tests' "no one acquires while I hold" (RWMutex), "the
   11th entrant gets `ErrTooManyClients`" (double barrier) need leases to outlive the test; the
   model lets them expire at any time. The specs give revision fencing; the snippets check that.
3. **`dbPerm`'s guards** (`ready` put after `count` waiters at some revision, its delete after
   exactly one) constrain a one-round use of a barrier key only; a stronger guard would need a round
   notion the code does not have.

## Open questions

* W0: `σ.kv.rev + 1 < 2^63` and a well-formedness / reachable-from-init law
  (`req/go_etcd_io_etcd_api_v3.md`): the queues' front argument and `createdAt` rest on it.
* W0/1d: one shared permission (`etcdPerm`) in `State.lean` would replace `etcdPeek` and `dbPerm`.
* Perennial specs assumed in sketches: `fmt.Sprintf` (`%s/%v`, `%s/%016d`, `%s%05d`), `fmt.Sscanf
  ("%d")`, `strings.Split`, `time.Now().UnixNano()`, `errors.Is`.
* Margins: `Dequeue` errors drop the caller's update (it could be given back except after an
  indefinite claim); `RemoteKV.Delete` on a deleted object drops it.

## `req/` sections written

* `go_etcd_io_etcd_client_v3.md`, `## from 1f`: 1b's `Watcher.Watch` (→ `watchChanAt`), receives
  (history-prefix events with `etcdLb`), `WatchResponse.Err` (never a recipes sentinel), the
  event's fields; W0: one shared permission.
* `go_etcd_io_etcd_client_v3_concurrency.md` (new), `## from 1f`: `isSession`, `Session.Client`,
  `Session.Lease`.
* `go_etcd_io_etcd_api_v3.md` (new), `## from 1f`: revision bound with one to spare; states'
  well-formedness.

## Round 1 repairs (2026-11-09)

Reviews: `reviews/1f-provability-1.md` (F1–F4, S1–S8), `reviews/1f-completeness-1.md` (C-1–C-9).
Built against W0's round 2 (`etcdPerm`/`etcdPeek`, `putOnce`, `etcdLb_init`, `etcdLb_revFits`,
`callErr_errorsNew`) and 1b's `ApiWatch.lean`: `etc/specs-build.sh --dir
SpecPlan/Spec/go_etcd_io/etcd/client/v3/experimental/recipes SpecPlan/Spec/fmt` (41 modules OK); snippets vet and are
gofmt-clean.

* **F1** (`WaitEvents` on `""`): the watch specs are stated over 1b's `watchEvents w` with `w` the
  request as the member reads it (`(opWatchM key [withRevM rev]).watchReq`: an empty key is
  `"\x00"`).
* **F2** (the dequeued value on the watch path): the sketches cite W0's `kvStep`'s `putOnce evs`
  (`req/go_etcd_io_etcd_api_v3.md` item 3, done by W0).
* **F3, C-3, C-7** (errors' shape): new `recipeErrOk err` (etcd's `errVal`, any `callErr`, a
  sentinel, `Fmt.scanErr`), given by every error arm of `waitEvents`, `WaitEvents`,
  `WaitPrefixEvents`, `Barrier.Wait`, both `Dequeue`s, `PriorityQueue.Enqueue`, `newSequentialKV`,
  `enteredClients`, `Enter`, `Leave`, `Lock`/`RLock`, `waitOnLastRev`; `errorsIs_recipeErr` takes
  it; `Enter`'s "not `ErrTooManyClients`" from `recipeErr_ne`, `recipeErr_fresh` (now also W0's
  `callErr_errorsNew`).
* **F4** (`Sscanf`): new trust-boundary spec `SpecPlan/Spec/fmt/Sscanf.lean` (`Fmt.Sscanf_d.spec`, the `%d`
  form into an `*int`: digits below `2^63` give `nil` and the value; otherwise some value or
  `Fmt.scanErr`), vocabulary `SpecPlan/Spec/fmt/Api.lean` (`decValue`, `scanErr`); 1f owns `SpecPlan/Spec/fmt/`.
* **C-1** (double barrier): `Enter` takes one-shot updates for creating its waiter key (`Qc`) and
  for deleting that key (`∀ k`, `Qd k`), `Leave` one for deleting its key; `dbPerm` (now W0's
  `etcdPerm`) covers only the `ready` key: its put after `count` waiters (`Enter`'s, `own = none`),
  its delete after a revision whose only waiter is this process's key (`Leave`'s, `own = some k`;
  provability S3). `Enter`'s post says which path ran: nothing created (`ErrTooManyClients` with the
  fact, both updates back), the creation's error, or created (`nil`; `ErrTooManyClients` with the
  key deleted by `Qd`; another error).
* **C-2** (sequence numbers): `newSequentialKV`'s and `PriorityQueue.Enqueue`'s update binds the
  read's revision `R` and `seqNext (σ.kv.storeAt R) prefix n` (one past the last key's number, by
  `Sscanf`), the guard `R + 1`.
* **C-4** (time-free exclusion): `Lock`/`RLock` and `Enter`/`Leave` docstrings and the Api header say
  that with W0's `EnvCfg.leaseExpiry = false` the facts are the tests' exclusion; snippets
  `ReqNoTwoHolders` (rwmutex.go), `ReqEnterCount` (doublebarrier.go). Decision 2 above is
  superseded.
* **C-5, C-6**: snippets `ReqDequeueWaitThenFed` (queue.go), `ReqSamePriority`,
  `ReqPQEveryItemOnce` (pqueue.go).
* **S1**: `waitEvents` restated over 1b's `watchChAt`, `watchChAt_recv`, `watchRespAt`, `eventOwn`
  and `WatchResponse.Err.spec` (any position with `done = some (rev - 1)`: `Watch`'s `init` or
  `closed`); the slots `watchChanAt`, `watchEvOwn`, `WatchEv`, `watchHist` removed; `evTyp`,
  `matchCount` over 1b's `WEv`.
* **S4**: `etcdPeek` is W0's; `dbPerm` is `etcdPerm` of the `ready` writes.
* **S7, C-8**: `RWMutex.Unlock`/`RUnlock` with a nil `myKey` added to the nonissue (retitled).
* **S8**: `waitOnLastRev` takes `0 < rev`.
* Not done: S6 (updates given back on a deleted `RemoteKV`, a `Dequeue`'s definite error: margins);
  S5 is 2a's (`callErr`'s `.other` and `errors.Is`, noted in `errorsIs_recipeErr`'s docstring);
  `sessionAt` stays a slot for 1d's `isSession` (same signature), to keep this batch's build off
  1d's draft.
