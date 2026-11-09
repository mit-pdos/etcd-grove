# Batch 1f (client recipes): provability review, round 1

Reviewer: provability. Targets: `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/` (`Api.lean` and
38 specs), `examples/specreq/recipes/*.go` (11 snippets), `nonissues/recipes-dbarrier-leave-without-key.md`,
the `## from 1f` sections of `notes/specs-only/req/*.md`. Checked against the Go code
(`.lake/src/client/experimental/recipes/*.go`), the server's watch handler, W0 (`api/v3/{Model,State}.lean`,
`client/v3/Api.lean`), 1b (`client/v3/ApiWatch.lean`, `WatchResponse__Err.lean`) and 1d
(`concurrency/Api.lean`, `Session__{Client,Lease}.lean`). The snippets vet and are gofmt-clean (`go
vet ./specreq/recipes/`). I did not rebuild the Lean files. The batch report (`batch-1f.md`) was read
only after the findings below were written.

Go line numbers are the file's own lines in `.lake/src/client/experimental/recipes/`.

## Verdict

The design is sound and mostly provable. Queue FIFO at the claim holds on both paths. The
priority queue's "first among the items present at `σ0`" holds on both paths, strictly. RWMutex's
`rwHeld` fencing and `Barrier.Wait`'s `goneAt` after `σ0` are true of the code. `dbPerm`'s guards
are what the code knows when it writes. Nine of the eleven snippets are provable, given W0's
outstanding well-formedness law. **Four first-tier findings.**

1. `WaitEvents.spec` is false for an empty key.
2. The queues' `Dequeue` value is not provable on the watch path under W0's model.
3. The recipes' errors carry no shape, so `DoubleBarrier.Enter`'s "not `ErrTooManyClients`" case
   and the snippet `ReqEnterThenLeave` cannot be proved.
4. A sketch rests on a `fmt.Sscanf` spec that does not exist on this branch.

The rest are second-tier.

## First tier

### F1. `WaitEvents.spec` is unsound at `key = ""` (hard rule: sound)

`WaitEvents.lean:57` states the result over the range `{ key := key, rangeEnd := [] }`. The server
watches the key `"\x00"` when the create request's key is empty: `if len(creq.Key) == 0 {
creq.Key = []byte{0} }` (`server/v3/etcdserver/api/v3rpc/watch.go:268-270`; 1b models the same
thing, `ApiWatch.lean:128`, `OpM.watchReq`). So `WaitEvents(c, "", r, [PUT])` after a `Put("\x00", ...)`
returns that put. The spec says the event is in `watchHist σ.kv {key := []} r`, and that history is
empty: `PutReq.invalid` refuses an empty key. `WaitEvents` is exported, and its pre admits `key = []`.
No caller in the package passes `""` (`Barrier.Wait`'s `Get("")` fails first), so the snippets are
unaffected.

**Fix**: state the range as 1b does, `(opWatchM key [withRevM rev]).watchReq.range`, or take
`⌜key ≠ []⌝`. The first needs no premise. It also spares `waitOnLastRev` and `Leave`, which pass keys
read from the store, a well-formedness fact to prove the key is non-empty. `WaitPrefixEvents` is
fine: `withPrefixM` already maps `""` to `"\x00"` in both `pfxRange` and the watch.

### F2. `Queue.Dequeue` / `PriorityQueue.Dequeue`: on the watch path, `v = kr.value` does not follow from W0's model (sketch implausible)

On the watch path the code claims the first put event `e` it was told about and returns
`ev.Kv.Value` (`queue.go:73,79`, `priority_queue.go:76,82`). The posts say
`v = kr.value`, where `kr` is the record the claimed key has in the store at the claim
(`Queue__Dequeue.lean:71`, `PriorityQueue__Dequeue.lean:59`). `frontByRev`/`frontByKey` force
`σ.kv.store k = some kr`. W0's `kvStep` (`Model.lean:854ff`, `TxnRun.put` at `:700`) lets one
successful transaction put the same key twice at one revision `m`; the gRPC duplicate-key refusal is
only one optional disjunct. 1b relies on the same thing deliberately ("no `noDupKeys` server
premise"). In that run:

* the watch delivers `put k v1` first;
* the store holds `v2` with mod revision `m`;
* `deleteRevKey(k, m)` succeeds, and `Dequeue` returns `v1`;
* the update must commit with `kr.value = v2`.

etcd itself refuses two puts of one key in one transaction, siblings included
(`v3rpc/key.go:280-287`, `checkIntervals`). Only a put followed by a delete gets through
(`issues/etcd-txn-check-intervals-sibling.md`), and that run is harmless here: the key is absent,
so the claim's comparison fails. So the code is fine and the model is weaker than etcd. Still, the
proof must use the model. The W0 request (`req/go_etcd_io_etcd_api_v3.md`, item 2) asks that "its
mod revision is the revision of the event that wrote its record", which does not exclude two puts at
one revision. The Get path is fine: the value is read from the store.

**Fix**: either (a) extend the W0 request: a successful transaction puts each key at most once per
revision, except a put followed by a delete, as `checkIntervals` gives (as a law of `etcdLb`'s
states, or as `kvStep` refusing it); or (b) weaken the posts on that path to the value of a put of
`k` at revision `kr.modRev` (`∃ kr', Event.put k kr' ∈ σ.kv.eventsAt kr.modRev ∧ v = kr'.value`).
That makes `ReqFIFO` harder to prove (two candidate values at one revision), so (a) is better.

### F3. The recipes' errors have no shape, so `DoubleBarrier.Enter`'s post and `ReqEnterThenLeave` cannot be proved (sketch gap; snippet unprovable; user not served)

* `DoubleBarrier.Enter.spec`'s last disjunct claims `err ≠ recipeErr .tooManyClients`
  (`DoubleBarrier__Enter.lean:73`). On the wait path (`double_barrier.go:91`) the error is
  `WaitEvents`'. The posts of `WaitEvents`, `WaitPrefixEvents` and `waitEvents` say only
  `err ≠ GoInterface.nil ∧ ev = null` (`WaitEvents.lean:59`, `WaitPrefixEvents.lean:52`,
  `waitEvents.lean:58`). Nothing rules out `err = ErrTooManyClients`. The code's errors on that path
  are:
  * `wresp.Err()`, which is `callErr err ck` of any kind, or `errVal .compacted`/`.futureRev`
    (1b's `WatchResponse.Err.spec`);
  * `ErrWatchClosed`;
  * `ErrNoWatcher`.

  None of them is `ErrTooManyClients`, but the specs do not carry it.
* The snippet `ReqEnterThenLeave` (`doublebarrier.go:55`) calls
  `errors.Is(err, recipe.ErrTooManyClients)` on `Enter`'s error. That is the user pattern of
  `T/v3_double_barrier_test.go:150`. Perennial's `errors.Is` (`wp_Is_tree`) and the batch's
  `errorsIs_recipeErr` both need to know the error's shape: `errVal`, `recipeErr` or `indefCall`.
  `Enter`'s error disjunct gives none. The call can run an arbitrary `Is` method, so this is not
  only a missing fact: as stated, the snippet's call is not provably panic-free.
* `errorsIs_recipeErr` itself (`Api.lean:433`) takes `indefCall err` but not a `callErr err k` of a
  definite kind, which is what `WatchResponse.Err` returns for a `closeErr` of kind `.etcd e`. So the
  errors from watches would still not qualify.

**Fix**: one persistent predicate, for example `recipeErrOk err := ⌜∃ e, err = errVal e⌝ ∨ (∃ k,
callErr err k) ∨ ⌜∃ e, err = recipeErr e⌝`.

* Every error post of the package gives it: `waitEvents`, `WaitEvents`, `WaitPrefixEvents`,
  `Barrier.Wait`, `Queue.Dequeue`, `PriorityQueue.Dequeue`, `Enter`, `Leave`, `Lock`, `RLock`,
  `newSequentialKV`, `PriorityQueue.Enqueue`.
* `waitEvents` gives `callErr`/`errVal` of `wresp.Err()`, or `recipeErr .watchClosed`.
* `errorsIs_recipeErr` takes it.
* `recipeErr_fresh` and `recipeErr_ne` then give `Enter`'s `≠ ErrTooManyClients`.

### F4. `newSequentialKV`'s sketch rests on a `fmt.Sscanf` spec that does not exist (resource without a source)

`key.go:88` calls `fmt.Sscanf(fields[len(fields)-1], "%d", &newSeqNum)`. The sketch and the batch
report cite "Perennial's `fmt.Sscanf`". Perennial has only the name (`Perennial/Code/fmt.lean:269`):
there is no spec under `Perennial/Spec/fmt/` (`Sprintf`, `Printf`, `Errorf` only). The old tree had
it as an etcd-grove trust-boundary axiom (`Spec/fmt/Sscanf.lean`, `notes/decisions.md:2928`), and
this branch deleted the old `Spec/`. Without it `newSequentialKV`, and so `PriorityQueue.Enqueue`,
has no proof.

**Fix**: restate the old trust-boundary spec in this branch (`Spec/fmt/Sscanf.lean`, with its
reason). The weak form is enough here: it writes some `int` through the pointer, and returns `nil`
or an error. Say which batch owns it (W0 owns the ambient boundaries). `strings.Split`, `Sprintf` and
`Time.UnixNano` do exist in Perennial.

## Second tier

S1. **1f's watch slot is not derivable from 1b as stated.** `watchChanAt_recv` (`Api.lean:407-415`)
splits responses on the Go fields (`v.closeErr' = nil ∧ CompactRevision' = 0 ∧ ¬Canceled'`). 1b's
`watchRespAt_fields` gives only `closeErrOk v.closeErr' m.closeErr`, and `closeErrOk` is opaque
(`ApiWatch.lean:375`). Its one law is the introduction `closeErrOk_nil` (`:505`), so "a non-error
response has `closeErr' = nil`" cannot be derived. The rest of the slot can be derived from
`watchChAt_recv` (`:463`), with this realization of `watchChanAt`: `∃ who w p, watchChAt …`, `w` the
`OpWatch` range with no filter and no `prevKV`, and `seen` the events up to `p.done`. The pieces:

* the first disjunct, because 1b's error case always has `canceled = true`;
* the events from `lo = c + 1 = rev`;
* `watchEvOwn` from `eventOwn` discarded.

The req says the slot is to be replaced at integration by "rename, same content"; that does not
hold. Since 1b exists now, restate `waitEvents` over `watchChAt`/`watchStep` and decide errors with
`WatchResponse.Err.spec` (which is what the code calls). With F3's error shape this also gives the
`callErr` facts.

S2. **W0 dependencies still open.** `State.lean` has neither the well-formedness law (req item 2)
nor `rev + 1 < 2^63` (item 1); 1d's sketches cite an `etcdLb_init` that does not exist either. Every
fact below uses well-formedness:

* `frontByRev` and `frontByKey` on both paths ("a key present later with a mod revision `≤ H` was
  present at `σg` with the same record"; a claimed key's mod revision is nonzero, else
  `deleteRevReq k 0` succeeds on an absent key);
* `createdAt` (`Version = 0` means absent);
* `0 < ModRevision` in `Leave`'s `WaitEvents` calls;
* `ReqHoldTwice` (a present key has version `≥ 1`; its header does not list the law).

Not 1f's to fix; the batch cannot close without them.

S3. **`dbPerm` is weaker than the code allows the caller to know.** `dbWrite`'s
(`Api.lean:373`) delete case admits **any** waiter key, though the docstring says "its own". The
`Leave` guard on deleting `ready`, "exactly one waiter at some revision `r ≤ σ.kv.rev`", already
holds once the first entrant has created its key, so in a one-round use it constrains nothing
during the leaving phase. The code knows more at each write: the key it deletes is the one it
created with lease `id`, and the single waiter it read is that key (`isLowest`). Guards like
`∃ R, createdAt σ.kv k [] id R` for the delete, and "the only waiter at `r` was created with lease
`id`" for the `ready` delete, are provable by the code and give a caller's invariant real content.
The realization of `dbOwn` must then carry `uniqueKeyIn (waitersPfx key) st.key` (and the
creation) for `my = some st`. `Leave` needs that even as things stand, for the delete permission;
the header says only "myKey's `ekOwn`".

S4. **The atomic-update and permission vocabularies are duplicated across batches.** `etcdPeek` is
`Concurrency.etcdPerm γ (fun σ σ' => σ' = σ)` with a weaker `COMM`, and `dbPerm` is an `etcdPerm`
over `dbWrite`. 1d's `etcdPerm` also gives `etcdLb` of both states at the commit, which every
recipe sketch rebuilds by hand. The req (item 5) proposes moving one `etcdPerm` to W0; I agree.
`dbPerm`'s `COMM True` is strictly weaker than `etcdPerm`'s for no reason. The TaDa-vs-permission
split itself is consistent and sound: one update for operations with a single linearizing write,
which a failed comparison aborts (`σ' = σ` on `txnCmpFailed`, checked against `kvStep`); a
permission for `DoubleBarrier`'s up-to-three non-linearizing writes.

S5. **`errorsIs_recipeErr`'s soundness depends on 2a.** It claims `errors.Is(err, sentinel)` is
false for every `callErr` value. `.other` is "any other error", which could wrap something with an
`Is` or `Unwrap` method. The law is provable only if 2a's realization of `callErr` pins the shapes
down (status errors, context errors, transport errors). W0's `errorsIs_errVal` has the same
dependency. Uncertain; worth a line in 2a's req.

S6. **Updates dropped without need.** `RemoteKV.Delete`, `Unlock` and `RUnlock` on a deleted object
drop the caller's update (`else ⌜err = nil⌝`). The Dequeues drop it on a definite error. Both are
noted as margins; giving it back costs nothing and lets a caller retry.

S7. **Nonissue coverage.** `RWMutex.Unlock`/`RUnlock` with a `nil` `myKey` (`rwmutex.go:88-89`:
`Unlock` without `Lock`, or after a `Lock` whose key creation failed) panic the same way `Leave`
does. The specs take `some st`; the nonissue mentions only `Leave` and `WaitEvents`. Add it to the
nonissue's notes.

S8. **Minor.** `waitOnLastRev`'s premise `2 ≤ st.rev` could be `0 < st.rev`: at `rev = 1` the
filter `maxModRev = 0` is off, but an empty answer still gives `rwHeld` at `1`. Harmless, internal.

## Per target

**Api.lean.**
* Good:
  * the guarantees are stated as history facts anchored at `σ0` (`goneAt`, `rwHeld`, `frontByRev`,
    `frontByKey`, `readyPutAt`, `createdAt`); they combine with a caller's invariant through
    `etcdLb_reach`;
  * `goneAt`'s delete-event case is exactly what the sibling delete-then-put run needs;
  * the requests are spelled out (`putNewReq`, `deleteRevReq`, `seqPutReq`) and checked against
    the `Op`s the code builds; `putReq0` is what `KV.Put` sends with no option;
  * `matchCount` matches `waitEvents`' greedy loop.
* Findings: F1 (it hosts the range shape `WaitEvents` uses), F3 (`errorsIs_recipeErr`'s pre), S1,
  S3, S4, S5.

**Barrier (`NewBarrier`, `Hold`, `Release`, `Wait`).** Sound. `Wait`:
* the key absent at `σg` gives `r = σg.kv.rev ≥ σ0.kv.rev`;
* otherwise the first `DELETE` from `H + 1` has `e.typ = evDelete`, from `matchCount`, and is the
  key's delete event at `e.rev > σ0.kv.rev`;
* `Get` with an `etcdPeek`-made update and `etcdState_lb` inside the commit gives `etcdLb γ σg`.

Needs W0 item 1, for `H + 1` in `int64`. Error posts: F3.

**Queue (`NewQueue`, `Enqueue`, `Dequeue`).**
* Get path: FIFO holds at the claim, any state `σ` reached from `σg`. Keys written after `σg` have
  mod revision `> H ≥ m0`; a key unchanged since `σg` has mod revision `≥ m0` (the sort ascends,
  ties in any order).
* Watch path, also checked for the case "one key read, its claim lost, `more = false`": the
  claimed put's revision `m` is `≥ H`, and every key under the prefix at the claim has mod revision
  `≥ m`. The only key at `σg` was changed by the failed claim, and puts in `[H, m)` would precede
  `e` in `es`, against `matchCount [PUT] es = 0`.
* The update also stays correct if an indefinite claim fires it later.

Findings: F2 (the value), S2.

**PriorityQueue (`NewPriorityQueue`, `Enqueue`, `Dequeue`).**
* `frontByKey … σ0.kv.rev` holds on both paths, strictly. Get path: a key before `k` at the claim
  was not at `σg`. Watch path: `m > H`, since a put at `H` with its key still at mod revision `H`
  at the claim would have been in `σg`'s store.
* `WithFirstKey()`'s sort normalizes to `SortNone`, so the default-order pushdown applies; checked.
* `pqPrefix`'s `padDec 5` gives key order = priority order.

Findings: F2, F4 (through `newSequentialKV`).

**RWMutex (`NewRWMutex`, `Lock`, `RLock`, `waitOnLastRev`, `Unlock`, `RUnlock`).** Sound.
* `waitOnLastRev`'s answer at `σg`, with `maxModRev = R - 1 ≥ 1` (`hasRevFilters`, pushdown `0`),
  is empty exactly when `rwHeld (pfxRange pfx) R`.
* `Lock`/`RLock` turn it into `rwHeld … σ'.kv.rev` via `sint.Z (W64 σ'.kv.rev) = σ'.kv.rev`. That
  needs `etcdState_revFits` at the creation's commit, so the recipe's update must snapshot it.
  Worth a sentence in the sketch.
* The post's `myKey`-set-on-error matches the code.

Findings: S7, S8.

**DoubleBarrier (`NewDoubleBarrier`, `Enter`, `Leave`, `enteredClients`).**
* The `ready` put's guard is discharged at any later firing state by the history-prefix lemma; a
  late firing after an indefinite error is fine.
* `resp2.Kvs[b.count-1]` is in bounds, because `count ≤ 0` returns at the first check.
* `Leave`'s "only this key at `r`" holds on the `len = 1 ∧ isLowest` path.

Findings: F3, S3; `createdAt` needs S2.

**Key helpers (`putNewKV`, `newKV`, `newKey`, `newUniqueKV`, `newEphemeralKV`, `newUniqueEphemeralKV`,
`newUniqueEphemeralKey`, `newSequentialKV`, `RemoteKV.*`, `deleteRevKey`, `claimFirstKey`).**
* Sound. The abort-on-`txnCmpFailed` construction is valid: `kvStep`'s failure branch is
  `TxnRun.nil`, so `σ' = σ`.
* `claimFirstKey` gives the update back on a definite error and loses it on an indefinite one, as
  stated.
* `newSequentialKV`'s `bound ≤ σ.kv.rev + 1` holds even if `H + 1` wraps.

Findings: F4.

**Watch helpers (`waitEvents`, `WaitEvents`, `WaitPrefixEvents`).**
* `ts ≠ []` is needed (`evs[i]`); the index stays in bounds.
* `0 < rev` is a fair scope restriction; every caller meets it, given S2 for `Leave`.

Findings: F1, F3, S1.

## Snippets

| snippet | provable? | how / what blocks |
|---|---|---|
| `ReqHoldTwice` | yes, given S2 | second `Hold`: `nil` only by a successful `Version = 0` comparison, but the key is owned, lease-free, present since the first `Hold`, and has version `≥ 1` (well-formedness). `errors.Is`: `Hold`'s errors are `errVal`, `recipeErr .keyExists` or `indefCall`. |
| `ReqWaitAfterRelease` | yes | invariant: `released = false →` the key has been present with no delete event since `Hold`'s revision `≤ σ0.kv.rev`; `released.Store(true)` precedes `Release`'s firing; `Wait`'s `goneAt` after `σ0` gives the flag. |
| `ReqWaitAbsent` | yes | calls only. |
| `ReqFIFO` | given F2 and S2 | the store under `kp` is `{ka ↦ (Ra,"a"), kb ↦ (Rb,"b")}` with `Ra < Rb`; `frontByRev` picks `ka`. On the watch path the value needs F2's fix. |
| `ReqEveryItemOnce` | yes | each firing deletes a present key (`frontByRev` includes presence); per-key exclusive tokens in `Q`. |
| `ReqDequeueClosed` | yes | the program's update can never commit (no key under `kp`), so `nil` is impossible. |
| `ReqPriorityOrder` | given F4 (and F2, S2) | `σ0` after the `Enqueue`s; no key under `key/` is written afterwards, so `frontByKey` means first present. |
| `ReqWritersExclude` | yes, given S2 | `rwHeld` at `R2 > r1`; owned keys only created by `putNewReq` or deleted, so `k1` with `createRev r1` present later ⇒ present at `σh` with mod revision `r1 < R2`. |
| `ReqReaderAfterWriter` | yes, given S2 | as above over `pfx/write`; `Unlock` and `RUnlock` from `Lock`/`RLock`'s `rwmOwn … (some _)`. |
| `ReqEnterReady` | yes, given S2 | two `dbPerm … false` (ids `id1`, `id2`) never delete `ready` (lease `0`, outside `key/waiters`); `readyPutAt` ⇒ present at the later `Get`. |
| `ReqEnterThenLeave` | **no** (F3) | `errors.Is(err, ErrTooManyClients)` on an error of unknown shape. The rest is provable: the third `Enter`'s first read saw `0` waiters at a revision after the `Get` that saw `k1`. |
| `ReqWaitFirstDelete` | yes | owned `k`: the events from `Rp` are the put, then `Delete`'s delete at `Rd`; `WatchEv.kvM`'s delete has `modRevision = W64 Rd`. |

## Ranking (most in need of revision first)

1. `waitEvents` / `WaitEvents` / `WaitPrefixEvents`: F1, F3, S1.
2. `DoubleBarrier.Enter` (and the snippet `ReqEnterThenLeave`): F3; `Leave`/`dbPerm`: S3.
3. `Queue.Dequeue`, `PriorityQueue.Dequeue`: F2 (a W0 request, or a weaker post).
4. `newSequentialKV` → `PriorityQueue.Enqueue`: F4.
5. `Api.lean` (`errorsIs_recipeErr`, `dbWrite`, shared permission): S3–S5.
6. RWMutex, Barrier, the key helpers: sound; minor items only (S6–S8).

No bug in the Go code found beyond the recorded nonissue; S7 extends it.
