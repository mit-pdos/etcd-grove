# Batch 1f (client recipes): completeness review, round 1

Reviewer: completeness. Read-only, except this file. I formed these findings before reading
`notes/specs-only/batch-1f.md`, then checked them against it: its decision 2 is answered below
(C-1, C-4).

## Users

Every importer of `go.etcd.io/etcd/client/v3/experimental/recipes`, found by searching the module
cache, `examples/` and `.lake/src`. It has no importer in the pinned etcd, raft, Kubernetes or
`examples/` outside `examples/specreq/` (and `specreq/clientv3watch/history.go`, which only names it).
The four cached `tests/v3` revisions have byte-identical recipe tests. I cite
`T = tests/v3@v3.0.0-20261103162249-673da07c8fab/integration/clientv3/experimental/recipes/`.

| pattern | call site | what the caller relies on | snippet |
|---|---|---|---|
| B1 Hold, then a second Hold errs | `T/v3_barrier_test.go:44-45` | the first creates the key; a held key is refused | `ReqHoldTwice` |
| B2 Wait does not return before Release | `T/v3_barrier_test.go:56-75`, `T/v3_closed_watch_test.go:173-204` | `nil` only after the key is deleted; Wait writes nothing (`:202-203`: the key is still held) | `ReqWaitAfterRelease` |
| B3 Wait on an absent key (another key has the name as prefix) | `T/v3_barrier_test.go:93-123` | reads the single key, not a prefix; returns promptly (time-based) | `ReqWaitAbsent` (calls only) |
| Q1 FIFO, one writer and one reader running concurrently | `T/v3_queue_test.go:45-64` | values in enqueue order, also when a Dequeue waits on an empty queue | `ReqFIFO` (**sequential only**, see C-5) |
| Q2 many readers and writers (Queue, and PriorityQueue via `flatPriorityQueue`) | `T/v3_queue_test.go:167-215, 119-127, 222-231` | every item dequeued once; reads equal writes (a lost item hangs a reader) | `ReqEveryItemOnce` (Queue only) |
| Q3 Dequeue errs when its watch closes or is compacted | `T/v3_closed_watch_test.go:63-98, 121-167` | an error, no value, no panic | `ReqDequeueClosed` |
| P1 priority order, items enqueued first, **with colliding priorities** ("[0, 2] priority for priority collision to test seq keys") | `T/v3_queue_test.go:99-116` | key order is priority order; equal priorities get distinct, increasing sequence keys | `ReqPriorityOrder` (**distinct priorities only**, see C-2) |
| R1 readers and writers exclude each other while held; the handle is passed to another goroutine, which unlocks | `T/v3_lock_test.go:314-360` | no reader or writer acquires while a writer holds | `ReqWritersExclude`, `ReqReaderAfterWriter` (revision fencing only, see C-4) |
| D1 no Enter returns before the `count`-th entrant arrives; no Leave returns before the last Leave | `T/v3_double_barrier_test.go:46-100` | entrants are counted; the waiter keys are deleted only by their own Leave | `ReqEnterReady` (checks that the ready key exists, not the count; see C-1) |
| D2 with `count` waiters entered, Enter gives `errors.Is(err, ErrTooManyClients)` and creates no key | `T/v3_double_barrier_test.go:116-162` (the 11 barriers share one session) | the waiters' keys stay during the call; the call leaves no key | `ReqEnterThenLeave` (the converse only; see C-1, C-3) |
| D3 failover: a lease revoked by `Session.Close` unblocks Leave | `T/v3_double_barrier_test.go:165-220` | liveness only | none needed |
| D4 Enter errs when the client closes | `T/v3_closed_watch_test.go:205-231` | not `nil` with 1 of 2 entrants | `ReqEnterReady` (via ready) |
| W1 WaitPrefixEvents from a compacted revision errs | `T/v3_closed_watch_test.go:100-119` | `nil` would need an event of the prefix | `ReqWaitFirstDelete` (WaitEvents), `ReqDequeueClosed` |
| internal | `Barrier.Wait`, `DoubleBarrier.Enter`/`Leave`, `RWMutex.waitOnLastRev` → `WaitEvents`; `Queue`/`PriorityQueue.Dequeue` → `WaitPrefixEvents`, `claimFirstKey`, `deleteRevKey`; `newUniqueKV`/`newUniqueEphemeralKV` → `putNewKV` + `errors.Is(ErrKeyExists)` | — | `ReqWaitFirstDelete` |

**Time-based assertions** (outside a model without time; no snippet needed): `v3_barrier_test.go:77-84`
and `:116-123` (waiters return within `waiters*100ms`); `v3_double_barrier_test.go:76-83, 93-100,
204-220` (Enter or Leave within a time limit; failover); `v3_lock_test.go:337-341` (each lock within
`waiters` seconds); `v3_closed_watch_test.go:49-56, 140-144, 196-200, 223-227` (returns within 10 s).
The probes `time.Sleep(…)` followed by a non-blocking `select` (`v3_double_barrier_test.go:67-72,
85-90`, `v3_closed_watch_test.go:82-87, 187-192, 212-217`) and the non-blocking checks in
`v3_lock_test.go:345-356` are **safety** facts sampled at a moment: "no Enter, Leave or acquisition has
returned yet". A spec can state them (C-1, C-4). Every `require.NoError` on a call's error is an
environment-failure assumption, not a spec obligation.

## First tier

### C-1. `dbPerm` cannot count entrants or protect a waiter's key: the double barrier's guarantee (D1, D2) is unprovable

*Principle*: Complete (sufficient for every caller); Faithful to concurrency (a once-only use needs a
token). *Files*: `Api.lean` `dbWrite`/`dbPerm`; `DoubleBarrier__Enter.lean`, `DoubleBarrier__Leave.lean`.

`dbPerm γ who key count id false` is a **persistent** atomic update. Its `dbWrite` admits:
- **any number** of creations of `key/waiters/<n>` (the `uniqueKeyIn` case), and
- the delete of **any** waiter key (`∃ k, (pfxRange (waitersPfx key)).mem k ∧ rq = .deleteRange (delReq k)`),
  in both the Enter (`leave = false`) and the Leave (`leave = true`) permission.

The code creates exactly one key per `Enter` (`double_barrier.go:58`). It deletes only its own key
(`b.myKey.Delete()`, `:72`, `:139`, `:162`). A caller's invariant must be stable under every write the
permission admits, so it cannot:
- **count entrants** (D1, `v3_double_barrier_test.go:67-72`). One Enter could, as far as the spec
  says, create the 10 keys that let the ready guard (`count ≤ n` at some revision) hold before the
  10th process arrives. The guard then says nothing about how many processes entered. `ReqEnterReady`
  checks only that the ready key exists after `nil`, so its header's "never before the `count`-th
  entrant arrived" is not what the snippet relies on.
- **keep another waiter's key present** (D1's leave-wait, `:85-90`: no non-main Leave returns before
  main's Leave). Main's key may, per the spec, be deleted by any other Leave or Enter, so
  `Leave.spec`'s "at some revision after σ0 no waiter key but this one's" does not imply that main
  left.
- **show the 11th Enter gets `ErrTooManyClients`** (D2, `:150`): during that call, its own `dbPerm`
  may delete one of the 10 keys, so the "`nil` only with fewer than `count` at the first read" arm is
  not refuted. Nor can it show **the call created no key** (`:158-159`, `assert.Len(t, resp.Kvs,
  waiters)`): the post's `ErrTooManyClients` arm says nothing about `my'`. The creation went through
  a persistent permission the invariant cannot attribute.

The batch's decision 3 concerns rounds; this concerns one round. Sessions do not help: D2's 11
barriers share one session, so `lease = id` cannot tell their keys apart.

*Fix*: put the per-call writes back under per-call resources, as `RWMutex.Lock` does.
1. `Enter` takes a one-shot `AU` for the waiter key's creation (`putNewReq k [] id`, `uniqueKeyIn`,
   with `Q` given `k`), so the caller's invariant counts entrants.
2. The own-key delete in `Enter` (the too-many path) and in `Leave` is a one-shot update over
   `delReq k` for **the key this barrier created** (`st.key` in `Leave`; in `Enter`, the `k` the
   creation's `Q` recorded).
3. `dbPerm` keeps only the two guarded writes of `ready`.
4. `Enter`'s `ErrTooManyClients` arm states which path ran: either `my' = my` and nothing was
   created (first read: `count` waiters at `r ≥ σ0`), or `my' = some st` with the creation's `Q` and
   the delete's `Q` (or its error).

Then D1 and D2 become provable under `EnvCfg.leaseExpiry = false` (C-4). Add snippets for them:
"no Enter returns `nil` before `count` entrants have created keys", and "with `count` keys held and
no Leave, Enter returns `ErrTooManyClients` and the prefix still has `count` keys".

### C-2. `newSequentialKV` / `PriorityQueue.Enqueue`: the sequence number is unconstrained, so equal priorities can neither be kept apart nor ordered (P1, Q2 for PriorityQueue)

*Principle*: Complete; No vacuous guarantee. *Files*: `newSequentialKV.lean`,
`PriorityQueue__Enqueue.lean`.

The update's binders are `n bound : Int` with only `bound ≤ σ.kv.rev + 1`. The successful
comparison `ModRevision(__pfx) < bound` then holds of every state: every mod revision is at most
`σ.kv.rev`. So the caller learns nothing about `n`. As far as the spec says, two Enqueues at one
priority may get the same `n` (the second put overwrites the first, and an item is lost) or a
decreasing `n` (not FIFO among equal priorities). The code rules both out for a prefix whose writers
all bump `__pfx` (`key.go:82-108`): `n` is one more than the last key's number at the `Get`'s
revision `R`, and `bound = R + 1`, so `__pfx` was not written after `R`.

The test collides priorities on purpose (`v3_queue_test.go:102`, `[0, 2] priority for priority
collision to test seq keys`), and Q2 runs `flatPriorityQueue` with priorities 0 and 1 (`:224-227`),
where every item must survive or a reader hangs. `ReqPriorityOrder` uses three distinct priorities,
so it misses this, and its header's "FIFO among equal priorities" is unproved. The old spec had this
fact (`seqKeyPutAt … g r` with `seqKeyPutAt_order`, `seqKeyPutAt_created`, specs-ref
`newSequentialKV.lean:33-49`). The new spec's Margin admits dropping it.

*Fix*: expose the read inside the update's condition:
`bound ≥ 1 ∧ bound - 1 ≤ σ.kv.rev ∧ seqNext (σ.kv.storeAt (bound-1).toNat) pre n`. Here `seqNext s p n`
holds when `n = 0` and no key of `pfxRange p` is in `s`, or the greatest such key (in key order) ends
in `/d` with `fmt.Sscanf`'s parse `m` and `n = m + 1`. A caller whose prefix holds only
`seqKey`s (16 digits, non-negative) then gets "`seqKey pre n` is greater than every key present at
`bound - 1`, and none was added since (`__pre` unchanged)". Add a snippet with two Enqueues at one
priority, dequeued in order (`panic` on a lost or reordered item).

### C-3. `Enter`'s errors have no shape: `errors.Is(err, ErrTooManyClients)` cannot be proved panic-free (D2; snippet `ReqEnterThenLeave`)

*Principle*: Complete; The postcondition says what the caller inspects. *Files*:
`DoubleBarrier__Enter.lean` (third disjunct `err ≠ nil ∧ err ≠ recipeErr .tooManyClients`);
`Api.lean` `errorsIs_recipeErr` (pre: `errVal`, `recipeErr` or `indefCall`).

The test (`v3_double_barrier_test.go:150`) and the snippet (`doublebarrier.go`, `ReqEnterThenLeave`)
both call `errors.Is(err, recipe.ErrTooManyClients)` on `Enter`'s error. The only `errors.Is`
contract the batch offers needs the error to be one of the shapes above, and `Enter`'s post does not
give one: an arbitrary interface value could have an `Is` or `Unwrap` method that panics. The code's
errors are known: `Get`/`Txn` errors (`errVal`/`indefCall`), the watch's `Err()` (1b: `errVal` or a
gRPC status, which the batch's own `req/` asked 1b for), `ErrWatchClosed`, `ErrNoWatcher`. The same
holds of `Barrier.Wait`, `Leave`, `Queue`/`PriorityQueue.Dequeue`, `WaitEvents`, `waitEvents` and
`PriorityQueue.Enqueue`'s second disjunct (`err ≠ nil` only). No current user applies `errors.Is` to
those, but tests format them (`%v`).

*Fix*: define `recipeCallErr err := (∃ e, err = recipeErr e) ∨ ∃ k, callErr err k`, persistent. Return
it on every error arm. Widen `errorsIs_recipeErr`'s pre to it (`recipeErr_fresh` already rules out a
`callErr` being a sentinel).

## Second tier

### C-4. Decision 2 ("time exclusion is not provable") is superseded by W0's `EnvCfg.leaseExpiry`; the tests' exclusion (R1) and barrier counts (D1, D2) are safety under it, and the snippets do not check them

W0's round-1 repairs (C-F6, `notes/specs-only/batch-W0.md:189`; `Model.lean:1124-1143`) added
`EnvCfg.leaseExpiry`. With it `false` (a deployment premise: every lease outlives the run), the
program's `envUpd` has no `leaseExpire` step, so a lock's or waiter's key stays until its owner deletes
it. Under that premise, **mutual exclusion of R1 follows from the specs as they are**: two holders
with keys created at `R₁ < R₂`, neither unlocked. The later one's `rwHeld` (over `pfx`, or over
`pfx/write` when the later one is a reader and the earlier a writer; a reader-reader pair does not
conflict) at a state `≥ R₂` requires the earlier key (mod revision `R₁ < R₂`) to be gone, and the
invariant says only its owner's Unlock deletes it. So `Lock.spec`/`RLock.spec` suffice, and their
docstrings' "Time-based exclusion … is not a consequence", the snippets' header "Time is not
modelled … no snippet relies on one staying" and the batch's decision 2 are stale.

*Fix*: one snippet per property, assuming `leaseExpiry = false`:
- R1: a writer and a reader on separate sessions, the handle unlocked by the other goroutine as in
  the test; `panic` if both report holding at once;
- D1 and D2: after C-1.

Keep the fencing snippets: they are the `leaseExpiry = true` instance. Correct the docstrings'
"What it guarantees": exclusion under `leaseExpiry = false`, fencing always.

### C-5. Q1's concurrent shape (a Dequeue waiting on an empty queue, then fed) has no snippet

`ReqFIFO` enqueues both items before dequeuing, so only the `Get`-and-claim path is exercised. The
test's reader runs concurrently with the writer (`v3_queue_test.go:45-64`) and usually reaches the
watch path (`queue.go:46-63`): its value comes from `ev.Kv.Value` (`watchEvOwn_unfold`), and FIFO
there rests on the sketch's "the first put after the read is the least mod revision at the claim".
`Queue.Dequeue.spec` states it (`frontByRev` at the claim on every path), so the spec serves Q1. Add a
snippet anyway: a goroutine dequeues from an empty owned queue, then the main goroutine enqueues
`"a"` and `"b"`, and the dequeued value must be `"a"`.

### C-6. Q2 for the priority queue has no snippet

`ReqEveryItemOnce` covers `Queue` only. `PriorityQueue.Dequeue` has the same claim shape, so
once-only follows, but "every enqueued item is there to be dequeued" needs C-2. Extend the snippet to
`PriorityQueue` with two items at one priority after C-2.

### C-7. `errorsIs_recipeErr`'s pre admits only `errVal`, a sentinel or an indefinite `callErr`

A `callErr err k` of a definite non-etcd kind (`.other`, e.g. a context error a W0 law maps there,
`callErr_ctxErr`) is excluded, though Perennial's `errors.Is` on such a value is as safe. Use
`∃ k, callErr err k` (with C-3).

### C-8. Premises the test code violates only after a reported failure (no fix; record)

`v3_lock_test.go:325-335` sends `rwm` to the unlocking goroutine even when `RLock`/`Lock` failed, so
`RUnlock`/`Unlock` may run with `myKey == nil`. That is a nil dereference in the promoted
`Delete` (`rwmutex.go:93-94`), which the `some st` premise excludes. `v3_double_barrier_test.go:56-60,
135-140` call `Leave` after a failed `Enter`
(`nonissues/recipes-dbarrier-leave-without-key.md`). Both are test paths after `t.Errorf`.
`Unlock`/`RUnlock` on an unset `myKey` is the same precondition as that nonissue's `Leave` case and
could be added to it. Not a recipes bug that etcd reaches; no new `issues/` entry.

### C-9. Establishability, sampled (one per pattern): fine except as above

- `Barrier.Hold`/`Wait` (`T/v3_barrier_test.go:43-59`): `isClient` from the cluster's client,
  `etcdPeek` and `etcdLb γ σ0` from the program's invariant (`etcdState_lb`).
- `Queue.Dequeue` (`T/v3_queue_test.go:59-61`): the caller's update, built at the claim from the
  invariant's item list.
- `RWMutex.Lock` (`T/v3_lock_test.go:322-331`): `sessionAt` (1d's `isSession`, same signature,
  given by `NewSession.spec`); `rwmOwn` moves through the channel.
- `WaitEvents` (internal): `sl ↦*□ ts` from a fresh slice literal, `0 < rev` at every call
  (header + 1, a key's revision, `resp.Header.Revision ≥ 1`; the compaction test passes `rev - 2 ≥ 4`).
- `DoubleBarrier.Enter`: `dbPerm` is establishable, but only by an invariant too weak for D1 and D2
  (C-1).

## Locality and abstraction (brief)

- `ekOwn` is a transparent `def` over the field projection `ek.[EphemeralKV, "RemoteKV"]`, which is
  implementation vocabulary in the API. No client outside the package needs it, so it could be opaque
  with an internal law.
- `dbWrite` mixes per-call writes (the creation, the own delete) with guarded shared ones (`ready`).
  C-1 splits them.
- `sessionAt` duplicates 1d's `Concurrency.isSession`, which exists now with the same signature. The
  integration step can replace it.

## What is good

- **The TaDa updates at the right points.** The queues fire at the claim (`frontByRev` on both paths,
  which also settles the open `Queue` half of `nonissues/recipes-pqueue-dequeue-order.md`), the
  barrier at its transaction, the lock key at its creation. Every definite answer is linearized,
  including `ErrKeyExists`.
- **History facts anchored at the caller's `σ0`** (`goneAt`, `rwHeld`, `readyPutAt`). They combine
  with an invariant through `etcdLb_reach`, and `goneAt`'s second case answers sibling delete-and-put
  revisions correctly.
- **The snippets that check history facts** (`ReqWritersExclude`, `ReqEnterThenLeave`'s second part,
  `ReqWaitFirstDelete`) are provable without counting, by the create-revision argument.
- **The closed and compacted-watch cases** (the fork's fixes) are served: every `nil` needs an event
  or a deletion, so the tests' "never `nil` or panic" assertions follow from ownership.
- **The old specs' scope restrictions are gone**: the prefix-ownership invariant, the length bounds
  and `kp ≠ []` are no longer premises.

## Ranking by need of revision

1. `DoubleBarrier.Enter`, `Leave`, `Api.lean`'s `dbWrite`/`dbPerm` (C-1, C-3).
2. `newSequentialKV`, `PriorityQueue.Enqueue` (C-2).
3. Error arms of `Barrier.Wait`, `Queue.Dequeue`, `PriorityQueue.Dequeue`/`Enqueue`, `WaitEvents`,
   `WaitPrefixEvents`, `waitEvents`; `errorsIs_recipeErr` (C-3, C-7).
4. `RWMutex.Lock`/`RLock` docstrings and `examples/specreq/recipes/` (C-4, C-5, C-6): the specs serve
   the users, but the snippets and the notes on what they guarantee are incomplete or stale.
5. The rest (Barrier, Queue, RemoteKV, the key helpers, the handles): no change needed.

## Verdict

Not done. Three first-tier findings:
- C-1: the double barrier's persistent permission makes its core guarantee unprovable.
- C-2: the sequence number is unconstrained, so the priority queue can lose an item at an equal
  priority, as far as the spec says.
- C-3: the error arms have no shape, so `errors.Is` on `Enter`'s error is unprovable, in the test and
  in a snippet.

The other specs serve their users. Decision 2 should be revisited under `EnvCfg.leaseExpiry = false`
(C-4).
