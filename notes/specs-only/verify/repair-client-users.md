# Repair after the verification round: group `client-users` (2026-11-09)

Files owned: `SpecPlan/Spec/go_etcd_io/etcd/client/v3/{concurrency,experimental/recipes,leasing}/`,
`SpecPlan/Spec/go_etcd_io/etcd/cache/v3/`, `SpecPlan/Spec/k8s_io/utils/third_party/forked/golang/btree/`,
`examples/specreq/{concurrency,recipes,leasing,cache,btree}/`. Reports: `A3-client-users-provability.md` (P),
`A3-client-users-completeness.md` (C).

## Findings

### P-F1 (1d) `Mutex.Unlock`'s catch-all error: fixed

`Mutex__Unlock.lean`: the "other error" disjunct now has the premise
`¬ (st.key = [] ∨ sint.Z st.rev ≤ 0 ∨ st.key = [W8 0])`, because the code returns `ErrLockReleased`
first (`mutex.go:134`). I also gave the same premise to the `nil` disjunct, which had the same
gap: on a released mutex it admitted `nil`, so `ReqTryLock`/`ReqLockUnlock` did not close through
it either. `lockerMutex__Unlock.lean` likewise: it returns `#()` only on a held mutex (otherwise
`Unlock` panics with `ErrLockReleased`).

### P-F2 (1d) `Campaign` -> `Resign` with an empty key: fixed as suggested

- `Election__Resign.lean`'s premise is now `effIn (delEff (fun k => k = st.leaderKey ∧ k ≠ [])) T`.
  After `Proclaim`'s `ErrElectionNotLeader`, the leader key is `""`, so that relation is the
  identity and lies within any `T`. etcd refuses an empty key, so the real step changes nothing.
- `Election__Proclaim.lean` gets the same sharpening on its `putEff` (`k = st.leaderKey ∧ k ≠ []`),
  which helps v3election's resumed `Proclaim`.
- Both changes only weaken premises, so 2e's current premises still imply them.
- `Campaign`'s proof sketch now spells out both cleanup cases.

### P-F3 (1f) Queue snippets lack the compaction condition: fixed (cheap fix)

- Each of the six Dequeue snippets now carries an `Assumes (compaction): exactFrom …` line in its
  header: `ReqFIFO`, `ReqEveryItemOnce`, `ReqDequeueWaitThenFed` (`queue.go`), and
  `ReqPriorityOrder`, `ReqSamePriority`, `ReqPQEveryItemOnce` (`pqueue.go`).
- The package comment (`barrier.go`) now says every Dequeue assumes it, because a caller cannot
  tell the read path from the watch path.
- The specs are unchanged; `Queue__Dequeue.lean` and `PriorityQueue__Dequeue.lean` say so in a
  `Changes (verify-round)` line.
- I did not take the stronger fix. The read path's facts could be unconditional only if the post
  told the caller which path ran, or if 1b gave an unconditional fact that a watch event's key is
  in range and that its key-value is the record its revision wrote. `ApiWatch.watchStep` has no
  such fact: every event fact sits under `exactFrom`. So it is a request to client-watch, below.

### P-F4 (1d, 1f) Sentinel errors as Lean constants: fixed with the cache's encoding

**concurrency (`Api.lean`)**

- Removed `opaque concErrVal`, `concErrVal_ok.spec` and `concErrVal_notCanceled.spec`.
- Added:
  - `concErrsOk ev cv` (pure): the values are non-nil, pairwise distinct and not `errVal`, and each
    is a `*errorString` distinct from `context.Canceled`'s value `cv`.
  - `concErrs ev` (def): `□ ∀ e, globalAddr e.global ↦□ ev e`.
  - `notConcErr err` (def): `∃ ev, concErrs ev ∗ ⌜∀ e, err ≠ ev e⌝`.
- `init.spec` is now `isPkgInit … ⊢ ∃ ev cv, concErrs ev ∗ globalAddr context.Canceled ↦□ cv ∗ ⌜concErrsOk ev cv⌝`.
  It can be proved at initialization: the fresh allocations are still owned, and `context` is
  initialized first.
- A post that returns a sentinel now says `globalAddr …ErrX ↦□ err`; "none of the package's"
  becomes `notConcErr err`. Files changed:
  - `Mutex__TryLock.lean`: `ErrLocked`, and `notConcErr` on the other errors.
  - `Mutex__Lock.lean`: `ErrSessionExpired`.
  - `Mutex__Unlock.lean`: `ErrLockReleased`.
  - `Election__Proclaim.lean`: `ErrElectionNotLeader`, and `notConcErr` on the other errors.
  - `Election__Leader.lean`: `ErrElectionNoLeader`.
- `notConcErr` for a client call's error comes from `init.spec` together with W0's `callErr_errorsNew`.

**recipes (`Api.lean`)**

- Removed `opaque recipeErr`, `recipeErr_ne.spec` and `recipeErr_fresh.spec`. The last one is
  derived from `init.spec` and `callErr_errorsNew`, which also gives it the missing
  `context.Canceled` source.
- Added `RecipeErr.global`, `recipeErrsOk`, `recipeErrs`, and `notRecipeErr e err`
  (`∃ v, globalAddr e.global ↦□ v ∗ ⌜err ≠ v⌝`).
- `putNewRet` now takes `ErrKeyExists`'s value `ke` as an argument. The new def `putNewRetAt res rev err`
  reads that value from the global. It replaces `⌜putNewRet res rev err⌝` in 9 specs: `putNewKV`,
  `newKV`, `newEphemeralKV`, `newKey`, `newUniqueKV`, `newUniqueEphemeralKV`,
  `newUniqueEphemeralKey`, `Queue.Enqueue`, `Barrier.Hold`.
- `recipeErrOk`'s sentinel case is now `∃ e, globalAddr e.global ↦□ err`.
- `errorsIs_recipeErr` now takes the global's value `v`, with `globalAddr e.global ↦□ v` and the
  package's `isPkgInit` in its precondition.
- `DoubleBarrier__Enter.lean`: `ErrTooManyClients` is `globalAddr … ↦□ err`, and the other errors
  carry `notRecipeErr .tooManyClients err`.
- `init.spec` has the same existential shape as concurrency's.

The snippets' Go code needed no change, since it compares against the globals. Their header
references were updated (`mutex.go`, `barrier.go`).

### C-F2 (1d) No-two-holders unprovable (`mutexEff`/`campaignEff` too wide): fixed

**Effects**

- New pure def `sessKey pfx lease := pfx ++ Perennial.fmt.hexadecimal lease`. This is what
  `Sprintf("%s%x", pfx, lease)` produces under Perennial's `SprintfOut`, which formats `%s` and
  `%x` exactly. It needs the import `Perennial.Proof.fmt.Base`.
- `mutexEff pfx lease` and `campaignEff pfx val lease` now allow only a put or delete of
  `sessKey pfx lease`.

**Posts**

- They now name the key:
  - `tryAcquire`: `k = sessKey pfx (sint.Z id)`, on the error path too.
  - `TryLock` (`nil`).
  - `Lock`: `nil`, and `ErrSessionExpired`'s `st'.key`.
  - `lockerMutex.Lock`.
  - `Campaign`.
- `Mutex.Lock` and `lockerMutex.Lock` also give
  `σ0.kv.rev < cr ∨ ∃ r, σ0.kv.store k = some r ∧ r.createRev = cr`, because the snippet needs the
  later locker's `cr` to be above the earlier holder's.
  - This is true of the code: `tryAcquire`'s transaction state comes after `σ0` and has `cr` as
    `k`'s create revision. A create revision `≤ σ0`'s revision kept until then means the record
    was there at `σ0`.
  - `lockedSince` alone gives only `cr ≤` the key's create revision, which does not exclude
    `cr ≤ c1`.

**Snippet and header**

- New snippet `ReqMutexNoTwoHolders` (`concurrency/mutex.go`): two sessions, `m1.Lock`, then
  `m2.Lock` in a goroutine, and a panic if `m2` returns before `m1`'s release flag is set. It
  assumes no lease expiry and an owned, initially empty `pfx/`; its header gives the proof idea.
- The Api header's Mutex paragraph now states time exclusion under `leaseExpiry = false`.
- `open-questions.md` 1.13's text, which claimed this for `Mutex`, is now true. I did not edit it;
  the coordinator should note it.

### C-F1, C-F1b, C-F3, C-F7 (2e's specs): not mine, sent as requests (below)

- **C-F1, v3lock:** already repaired by server-boot. `lockServer__Lock.lean` uses
  `name ++ "/"` and `sessKey`.
- **C-F1, v3election:** `electionServer__Campaign.lean` still uses `campaignEff name value l` and
  `waitedFor name`.

### C-F4 (btree) No Kubernetes snippet: fixed

New snippet `ReqTreeOfSnapshots` (`btree/btree.go`): a tree of frozen clones keyed by resource
version. It covers `DescendLessOrEqual` stopped at the first item, a snapshot reading as it was
when cloned, `Min`, `DeleteMin`, `Clear(false)` and `Len`. The btree `Api.lean` header now lists
the Kubernetes users and the snippet.

### C-F5 (cache) No progress notification without `WithProgressNotify`: not fixed

This is second tier, and the fix is not local. `cacheWatchAt`'s state does not record the watch's
options, so the clause needs a new index on the watch predicate and on `Cache.Watch.spec`'s post.
It is left for a later round.

### C-F6 (leasing) The proxy's `Put`/`DeleteRange` through `Do`: fixed

New snippet `ReqDoPutDelete` (`leasing/txn.go`): `Do(OpPut(…, WithPrevKV()))` must give `Put() != nil`,
and `Do(OpDelete(…, WithPrevKV()))` must give `Del() != nil`. Both come from `leasingKV.Do.spec`'s
`doReplyL`. No spec changed.

## Requests to server-boot (`SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3election/`)

1. **`electionServer__Campaign.lean`** (C-F1).
   - Premise: replace `∀ l : Int, effIn (campaignEff name value l) T` with
     `effIn (campaignEff (name ++ go!"/") value l) T`. The election's prefix is `name + "/"`
     (`NewElection`).
   - `campaignEff` now writes only `sessKey (name ++ "/") l`, so `campaignEff name …` no longer
     contains it.
   - Post: replace `waitedFor name k cr σ` with `waitedFor (name ++ go!"/") k cr σ`. You may add
     `k = sessKey (name ++ go!"/") (sint.Z l)` as v3lock does.
2. **`electionServer__Leader.lean`** (C-F1): the post already reads
   `firstCreate (name ++ go!"/") …`. Nothing to do if that is the repaired text.
3. **`electionServer__Proclaim.lean`** (C-F1b).
   - The create-revision clause `r.createRev = uint.nat x.rev` is false at `x.rev = 0`: an absent
     key passes the compare and `putKey` creates it at `σ.kv.rev + 1`.
   - Guard the clause with `x.rev ≠ 0 →`, or state 1d's post as it is: the compare held at `σ`,
     and `etcdLb (putKey σ x.key value l)`.
4. **Observe** (C-F3): `electionServer.Observe` is translated with a body but has no spec. 1d
   provides `observeAt_recvAu.spec` for its `select`, and `m.kvs = [_]` makes `Kvs[0]` safe.
5. **Lent token** (C-F7): `lockServer.Lock`, and `electionServer.Campaign`/`Proclaim`/`Resign`,
   take `P` without giving it back. 1d returns it on every definite outcome, so the posts could
   return `P` on `nil` and on 1d's definite errors.
6. **Error value** (informational, from F4): 1d no longer has `concErrVal`. If a v3election spec
   needs `ErrElectionNoLeader`'s value, read it from `globalAddr …ErrElectionNoLeader ↦□ err`
   (1d's `Election.Leader.spec`).

## Requests to client-watch (`SpecPlan/Spec/go_etcd_io/etcd/client/v3/ApiWatch.lean`)

1. **Unconditional event facts** (P-F3's stronger fix). In `watchStep`'s events branch, add
   outside the `exactFrom` gate:
   - every event's key is in `w.range`;
   - each event's key-value is the record its mod revision wrote at `σ.kv`, i.e.
     `(σ.kv.storeAt e.modRev) e.key = some e.record` for a put.

   Both are true of the server: compaction affects only which revisions are reported, not what a
   reported event is. The recipes' Dequeue specs could then state the front's prefix and
   `v = kr.value` unconditionally, and `ReqDequeueClosed` would not need the package-level
   assumption. Not urgent: the snippets now assume `exactFrom`.

## New decisions

- **Sentinel errors are read from their globals; the package's error values are existential.**
  `concErrVal` and `recipeErr` are gone. A spec that returns a sentinel says
  `globalAddr ErrX ↦□ err`. A spec that excludes the sentinels says `notConcErr err` or
  `notRecipeErr e err`, which existentially carry the globals' points-to and an inequality.
  `init.spec` gives the values with their distinctness, including from `context.Canceled`'s value.
  This is the cache's shape, extended with the `Canceled` fact that W0's `callErr_errorsNew`
  needs.
- **A mutex and an election write only their session's key** (`sessKey`). This narrows the
  permission callers give, which only makes it easier to provide. With `leaseExpiry = false` it
  gives time exclusion between holders of distinct sessions. Callers that passed
  `mutexEff name l` for an arbitrary `l` must use the real prefix `name ++ "/"` (server-boot has
  done so for v3lock; v3election is requested).
- **P-F3 took the cheap fix.** The Dequeue facts stay gated on `exactFrom` on every path, and the
  snippets assume it. Ungating the read path needs 1b's unconditional event facts (requested).

## Build

`etc/specs-build.sh --dir` was run on all five owned directories: `client/v3/concurrency`,
`client/v3/experimental/recipes`, `client/v3/leasing`, `cache/v3` and the k8s `btree`. Result:
**OK (331 modules)**. The earlier attempts failed only because other groups' files
(`client/v3/Api.lean`, `grpc/Api.lean`) were mid-edit.

Snippets: `go vet ./specreq/{concurrency,recipes,leasing,cache,btree}/` is clean, and `gofmt -l`
prints nothing.

No new findings in the Go code.

## Second pass (coordinator, `second-pass.md`)

These follow client-core's and client-watch's repairs.

### W0's `KV.GetStreamTriple` no longer takes a thread token

- `leasingKV__GetStream.lean` states its contract as `KV.GetStreamTriple`, so it follows the change
  without an edit to the triple. I updated its proof sketch and its `Changes` text.
- I also updated the snippet header of `ReqGetStreamUnsupported` (`leasing/reads.go`).

### W0's KV triples take `emptyEnd = false`

- The leasing contract now takes the same scope premise as W0's: `LKV.GetTriple`,
  `LKV.DeleteTriple`, `LKV.DoTriple` (`o.emptyEnd = false`), and `LTxn.ThenTriple`/`ElseTriple`
  (`OpM.anyEmptyEnd os = false`). Without it, `kvAt_lkvAt` could not be proved, and the leasing
  code, which forwards these ops to the client's KV, could not meet W0's preconditions.
- The internal `leasingKV.get` and `leasingKV.delete` take `o.emptyEnd = false` too.
  `leasingKV.deleteRange` already requires a non-empty range end.
- The leasing note is in the Api header.
- My other users (concurrency, recipes, cache) only build ops without an empty range end, so their
  sketches discharge the premise directly. No snippet passes `WithRange("")`.

### W0's `callErr_errorsNew` has a new `io.EOF` disjunct

- `concErrsOk` and `recipeErrsOk` take `io.EOF`'s value `eof` as well, and each sentinel is
  distinct from it.
- Each `init.spec` gives `globalAddr io.EOF ↦□ eof`. `notConcErr` and `notRecipeErr` stay derivable
  for every `callErr`.

### W0's `ctxPrin_todo` is now an entailment

- The citations in recipes' `Api.lean` and `deleteRevKey.lean` now read: `Context.TODO.spec` names
  `todoCtxVal`, then the law `ctxPrin_todo`.

### Recipes' Dequeue: the claimed key and the value are no longer gated

client-watch's `watchStep` now says, outside the `exactFrom` gate, that each delivered event is a
real event of its revision kept by the watch.

- **Watch helpers.** `waitEvents`, `WaitEvents` and `WaitPrefixEvents` now give this fact
  unconditionally for the returned event.
- **Dequeue update.** In `Queue.Dequeue` and `PriorityQueue.Dequeue`, the caller's update now gets
  two facts unconditionally: the claimed key is under the prefix, and `σ.kv.store k = some kr`.
  - On the read path, these come from the read.
  - On the watch path, they come from the event's key and its record. A successful
    `deleteRevReq` at the event's mod revision claims exactly that record (`putOnce`).
- **Dequeue post.** `v = kr.value` is now unconditional.
- **Still gated.** Only the front condition (`frontByRev`/`frontByKey`) stays under `exactFrom`.
  The watch path's "first put after the read" needs exact events, and a caller cannot tell the two
  paths apart.
- **Snippets that drop the compaction assumption:**
  - `ReqEveryItemOnce` and `ReqPQEveryItemOnce`: distinct claims of distinct records give distinct
    values.
  - `ReqDequeueClosed`: a `nil` would need a claimed key under the empty, owned prefix. It no longer
    needs the package-level assumption.
- **Snippets that keep it:** `ReqFIFO`, `ReqPriorityOrder`, `ReqSamePriority` and
  `ReqDequeueWaitThenFed`. They need the order, i.e. the front.
- The recipes Api header and the snippet package comment are updated to match.

### Build

`etc/specs-build.sh --dir` on all five owned directories: **OK (331 modules)**. `gofmt -l` prints
nothing, and `go vet` is clean on concurrency, recipes and leasing.

## Re-review (`R-A3-client-users.md`)

### N1: `ReqMutexNoTwoHolders` needs the two leases to differ — fixed

- **The fix.** `NewSession.spec`'s grant branch now also gives the grant's pre-state:
  `∃ σg σ, etcdLb γ σg ∗ etcdLb γ σ ∗ ⌜Reach σ0 σg ∧ σg.leases id = none ∧ Reach σg σ ∧ σ.leases id ≠ none⌝`.
  - This is `grantEff`'s pre-state. The model refuses a collision with `ErrLeaseExist`.
  - It strengthens the post, so callers are unaffected.
- **How the snippet gets distinct leases.** It passes the first session's post state as the second
  call's `σ0`.
  - The first lease `id1` is still live at the second grant's `σg`. This holds because there is no
    lease expiry and, as a new `Assumes` line says, no other client revokes the two sessions'
    leases.
  - `σg` lacks `id2`, so `id1 ≠ id2`.
  - Hence the two keys differ: `sessKey` is injective in the lease.

### Stale `Changes` lines — fixed

The verify-round lines in `Queue__Dequeue.lean` and `PriorityQueue__Dequeue.lean` now say that the
second pass narrowed the compaction assumption to the snippets that check the order. They no longer
say the in-range fact is still "requested".

### Election time exclusion (optional) — added

- New snippet `ReqElectionNoTwoLeaders` in `concurrency/election.go`. Users: `TestElectionWait` and
  `TestElectionFailover` in `tests/integration/v3_election_test.go`, and `etcdctl elect`.
- **Proof idea.**
  - The leases differ by `NewSession.spec`'s grant pre-state, as in N1. So, by `campaignEff`, each
    election writes only its own session's key.
  - `Election.Campaign.spec`'s post gives `k`'s exact create revision `cr` at a state after `σ0`,
    so e2's `cr` is above e1's key's revision.
  - e2's `waitedFor` (`noOlder`) then excludes e1's key, which the program's invariant keeps
    present until `e1.Resign`.
- No spec changes were needed for this beyond N1's.
- The Api header lists the new snippet.

### Build

`etc/specs-build.sh --dir` on all five owned directories: **OK (331 modules)**. `gofmt -l` and
`go vet ./specreq/concurrency/` are clean.
