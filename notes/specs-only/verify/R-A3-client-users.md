# Re-review A3, client users (2026-11-09)

Reviewer: fresh and independent. Read-only. I wrote my verdicts before reading
`repair-client-users.md`; afterwards I read it only to check N1 below.

**Scope.**
- Batches: 1d `client/v3/concurrency`, 1e `client/v3/leasing`, 1f `client/v3/experimental/recipes`
  (with `Spec/fmt`), 1g `cache/v3` and the btree.
- The server side of lock and election: `etcdserver/api/{v3lock,v3election}`, for A3's prefix findings.
- Snippets: `examples/specreq/{concurrency,leasing,recipes,cache,btree}`.

**Baseline.** `1aa6fc1337`, against HEAD `974e05095b`. 56 files changed in the area (`git diff --stat`).

**Build check.**
- `lake build --no-build` on the changed modules reports "All targets up-to-date".
- `go vet ./specreq/{concurrency,recipes,leasing,btree,cache}/` is clean.

## Verdicts

| batch | verdict |
|---|---|
| 1d concurrency | **FAIL**: one new first-tier finding (N1). All original first-tier findings are resolved. |
| 1e leasing | **PASS WITH OPEN DECISIONS**: 1.8 (weak contract or the fixes), 1.9 (reader slots). |
| 1f recipes (+ fmt) | **PASS WITH OPEN DECISIONS**: 1.10; C11 and C12 are recorded as new decisions. |
| 1g cache + btree | **PASS WITH OPEN DECISIONS**: 1.11 (including the cache's "no progress without `WithProgressNotify`" gap, A3-C F5). |
| 2e v3lock / v3election (prefix findings only) | **PASS**. |

1d would be PASS WITH OPEN DECISIONS (1.13 / C10) once N1 is fixed. N1 is a one-conjunct
strengthening of `NewSession.spec`'s post.

## Original first-tier findings

| finding | status | evidence at HEAD |
|---|---|---|
| A3-P F1: `Mutex.Unlock` admits any error on a released mutex | **Resolved** | See (a) below. |
| A3-P F2: `Campaign`'s cleanup `Resign` with the empty key | **Resolved** | See (b) below. |
| A3-P F3: queue snippets rely on facts gated by `exactFrom` | **Resolved differently, and fine** (decision C11) | See (c) below. |
| A3-P F4: sentinel errors as opaque Lean constants | **Resolved** (decision C12) | See (d) below. |
| A3-C F1: 2e's posts use `name`, not `name ++ "/"` | **Resolved** | See (e) below. |
| A3-C F1b: 2e `Proclaim`'s post is false at `rev = 0` | **Resolved** | See (f) below. |
| A3-C F2: `mutexEff`/`campaignEff` allow any key under `pfx`, so time exclusion cannot be proved | **Resolved** (decision C10, 1.13 updated) | See (g) below. One new snippet does not close: N1. |

**(a) A3-P F1, `Mutex.Unlock`.**
- In `Mutex__Unlock.lean:58-63`, the `nil` disjunct and the third disjunct (other errors) now carry
  `¬(st.key = [] ∨ rev ≤ 0 ∨ st.key = [W8 0])`. The `ErrLockReleased` disjunct is `globalAddr
  ErrLockReleased ↦□ err`.
- This matches `mutex.go:134-137`. The `fmt.Errorf` path at `:139-141` falls under the third
  disjunct.
- `lockerMutex.Unlock` follows suit: it returns only on a held mutex.
- `ReqTryLock` and `ReqLockUnlock` close: the released state leaves only disjunct 2.

**(b) A3-P F2, `Campaign`'s cleanup `Resign`.**
- `Election__Resign.lean:56` now has `delEff (k = st.leaderKey ∧ k ≠ [])`, so at `""` the step is
  the identity.
- That is sound. W0's model refuses an empty key in a transaction without a state change
  (`Model.lean:1004,1017`).
- `Proclaim`'s premise is sharpened the same way (`Election__Proclaim.lean:66`).
- The `Campaign` sketch (`Election__Campaign.lean:16-18`) closes. After `ErrElectionNotLeader`
  (`election.go:122-124`) the step is the identity. After any other error the key is `sessKey`,
  which is inside `campaignEff`'s delete.

**(c) A3-P F3, queue snippets.**
- The cheap fix: `ReqFIFO`, `ReqPriorityOrder`, `ReqSamePriority` and `ReqDequeueWaitThenFed` now
  state `Assumes (compaction)`.
- The strong fix:
  - `Queue__Dequeue.lean:86-92` and `PriorityQueue__Dequeue.lean:66-73` give `(pfxRange).mem k ∧
    σ.kv.store k = some kr` and `v = kr.value` unconditionally.
  - This rests on 1b's unconditional event fact (`ApiWatch.lean:322-323`), which is true of the
    server.
  - On the watch path, `queue.go:72-79` deletes by `ev.Kv.ModRevision`. A successful compare on
    the mod revision plus `putOnce` gives the record and its value.
- `ReqEveryItemOnce`, `ReqPQEveryItemOnce` and `ReqDequeueClosed` close with no assumption.

**(d) A3-P F4, sentinel errors.**
- `concErrVal` and `recipeErr` are gone; a grep finds no remaining use.
- `init.spec` (`concurrency/Api.lean:677-685`, `recipes/Api.lean:446-450`) gives existential
  values with `concErrsOk`/`recipeErrsOk`. Posts read `globalAddr ErrX ↦□ err`; the exclusions are
  `notConcErr`/`notRecipeErr`.
- This can be realized:
  - Perennial's `errors.New` code allocates a fresh `*errorString` (`Perennial/Proof/errors/NewVar.lean:56-72`).
  - The initializer can step through it while the allocation is still owned.
  - W0's `callErr_errorsNew` (`client/v3/Api.lean:1223-1226`) plus `concErrsOk`'s `≠ cv, ≠ eof`
    gives `notConcErr` for every client-call error.

**(e) A3-C F1, 2e's prefix.**
- `lockServer__Lock.lean:47-54` now uses `mutexEff (name ++ "/")` and `lockedSince (name ++ "/")`.
- `electionServer__Campaign.lean:55-63` now uses `campaignEff (name ++ "/")`, `waitedFor (name ++
  "/")` and `sessKey`.
- `electionServer__Leader.lean:48` now uses `firstCreate (name ++ "/")`. It follows from 1d's
  `holdsAt` together with `σ.kv.store v.key = some (recOf v)`.
- Checked against `v3lock/lock.go:35-50` and `v3election/election.go:40-58,98-108`.
- `ReqLockOverInProc` (`etcdserverboot/lock.go`) closes.

**(f) A3-C F1b, 2e `Proclaim` at `rev = 0`.**
- `electionServer__Proclaim.lean:57-60` now gives 1d's `ownerCmp … holds σ` and `etcdLb (putKey σ
  x.key value id)`. It no longer claims `createRev = x.rev`.

**(g) A3-C F2, time exclusion.**
- `mutexEff`/`campaignEff` now touch only `sessKey pfx lease` (`concurrency/Api.lean:224-241`).
- `sessKey` is `pfx ++ Perennial.fmt.hexadecimal lease`. That is exactly what Perennial's
  `SprintfOut.hex` gives for `"%s%x"` (`.lake/packages/perennial/Perennial/Proof/fmt/Base.lean:234,
  504-507`).
- `Mutex.Lock` adds `σ0.kv.rev < cr ∨ (k present at σ0 with createRev cr)`. That is a true pure fact
  by induction on `Reach`: a created record gets `rev+1`, and a kept record keeps its create
  revision.

The completeness report's second-tier items:
- F3: `electionServer.Observe` now has a spec (`electionServer__Observe.lean`). It closes
  (`resp.Kvs[0]` is safe through 1d's `m.kvs = [_]`).
- F4: btree snippet `ReqTreeOfSnapshots` added. It closes.
- F6: leasing snippet `ReqDoPutDelete` added. It closes.
- F7: 2e gives `P` back on success.
- F5 (cache): left open under 1.11.

## New first-tier finding

### N1 (1d). `ReqMutexNoTwoHolders` needs the two sessions' leases to differ, and `NewSession.spec` does not give it

**Where.** `examples/specreq/concurrency/mutex.go:159-204`. The snippet's header claims
"`NewSession.spec` (grantEff: a fresh lease id)" and "distinct: the first is live at the second
grant".

**The step that does not close.** The snippet's proof needs `id1 ≠ id2`.
- If the ids were equal, `k1 = k2 = sessKey pfx id1`.
- `m2`'s `tryAcquire` would then take the `Else` branch with `myRev = r1`, and the owner check
  `ownerKey[0].CreateRevision == m.myRev` would hold (`mutex.go:82`).
- So `m2.Lock` returns at once with `released = false`, and the snippet panics.
- In the specs, `Mutex.Lock`'s post is then satisfiable with `k2 = k1` and `cr2 = r1` (its second
  disjunct). So nothing excludes this.

**Why the specs do not give it.**
- `NewSession.spec`'s grant branch (`NewSession.lean`, post) gives only `∃ σ, etcdLb γ σ ∗ ⌜Reach
  σ0 σ ∧ σ.leases (sint.Z id) ≠ none⌝`.
- That is consistent with `id2 = id1`, because `id1` is live at every such `σ`.
- The freshness in `grantEff` (`σ.leases id = none` at the grant's pre-state,
  `concurrency/Api.lean:246-249`) is a condition on the caller's `T`. It is not a fact returned to
  the caller.
- `etcdPerm` (`api/v3/State.lean:171-173`) commits with only `etcdLb` of the two states. Nothing
  ties the returned `id` to the step the permission fired.

**Is it true of the code?** Yes.
- The server grants only an id absent from its lease table. A collision is `ErrLeaseExist`, an
  error: W0 `Model.lean:1057-1076`.
- `NewSession`'s proof sees the grant's reply and the step it linearized.

**Suggested fix.**
- Strengthen `NewSession.spec`'s grant branch to name the grant's pre-state:
  `∃ σg σ, etcdLb γ σ ∗ ⌜Reach σ0 σg ∧ σg.leases (sint.Z id) = none ∧ Reach σg σ ∧ σ.leases
  (sint.Z id) ≠ none⌝`.
- With `leaseExpiry = false` and `id1` live from `σ1` on (only `s1.Close` revokes it, deferred to
  after `<-done`), this gives `id2 ≠ id1`.
- The snippet's `Assumes` should also say that no other client revokes the two sessions' leases.
  "pfx+"/" owned" covers keys, not `LeaseRevoke` on these ids.
- The weaker alternative is to make distinctness an explicit `Assumes`. But that is a server
  guarantee, not something the caller keeps, so it belongs in the spec.

## Regressions (files changed since `1aa6fc1337`)

**1d.** Every changed spec closes.
- `tryAcquire`, `Lock`, `TryLock`, `Unlock`, `lockerMutex.{Lock,Unlock}`, `Campaign`, `Proclaim`,
  `Resign` and `Leader` were each re-planned against `mutex.go:52-175` and `election.go:69-158`.
- Every cleanup `Unlock`/`Resign` sits inside the narrowed `mutexEff`/`campaignEff`: the key is
  `sessKey` at each call.
- `notConcErr` holds on every client-error arm. No way to prove `False` was found:
  - `concErrsOk` is satisfiable;
  - `init.spec` is existential;
  - the `Unlock` arms partition on the released condition.

**1e.**
- The `emptyEnd = false` premises on `LKV.{Get,Delete,Do}Triple`, `LTxn.{Then,Else}Triple`,
  `leasingKV.{get,delete}` are W0's scope premise (A1-P F5).
- Users can establish them. The proxy builds ops only when `len(r.RangeEnd) != 0`
  (`grpcproxy/kv.go:178,221`), and the leasing code adds no empty end.
- Uncertain: I did not trace each internal leasing op builder (`gatherOps`, `evalOps`).

**1f.**
- `putNewRet` is parameterized by `ke`, and `putNewRetAt` reads it from the global. The 10 changed
  `new*`/`Hold`/`Enqueue` posts are consistent.
- `DoubleBarrier.Enter` matches `double_barrier.go:46-97`.
- `errorsIs_recipeErr` now takes the sentinel's value from its global. It is plausible.
- `WaitEvents`/`waitEvents` gain the unconditional event fact, which matches 1b.
- `Spec/fmt/Sprintf_md.lean` and `printMD_inj` (new, client-core's) are plausible trust claims of
  Go's map printing.
- Doc nit: `Queue__Dequeue.lean:45` ("Changes (verify-round)") still says the read path's facts
  "need 1b's … fact (requested)". Lines 37-43 and the triple show that this is done. The same
  stale text appears in `PriorityQueue__Dequeue.lean:26`. Second tier.

**1g.**
- No cache spec changed.
- The btree `Api.lean` change is header text only.
- `ReqTreeOfSnapshots` closes: `Clone` gives two full trees; `ownBTree_persist` freezes the clone;
  `Get` and `DescendLessOrEqual` take any `dq`; `Min`, `DeleteMin`, `Clear` and `Len` are as
  stated.

**2e.**
- The messages are now 3h's abbreviations.
- `electionServer.Observe` (new) closes against `v3election/election.go:75-96` through
  `observeAt_recvAu`.
- `P` comes back on success in `Lock`, `Campaign`, `Proclaim` and `Resign`; 1d returns it on those
  paths.

## Snippets (changed or added)

| snippet | status |
|---|---|
| `ReqTryLock` | Closes. `ErrLocked` is identified by agreement of `↦□`, the others by `notConcErr`; `Unlock` on the released state gives only `ErrLockReleased`. |
| `ReqLockUnlock` | Closes. |
| `ReqMutexNoTwoHolders` (new) | **Does not close: N1.** The rest of its proof idea closes: `k1` present while `released = false`, because only `m1`'s `Unlock` can delete it; then `cr2 > σ0'.rev ≥ r1`, and `noOlder pfx cr2 σ2` excludes `k1`. |
| `ReqDoPutDelete` (new) | Closes (`LKV.DoTriple`, `emptyEnd` false). It covers A3-C F6. |
| `ReqTreeOfSnapshots` (new) | Closes. It covers A3-C F4. |
| `ReqHoldTwice` | Closes (`putNewRetAt`, `errorsIs_recipeErr`). |
| `ReqFIFO`, `ReqPriorityOrder`, `ReqSamePriority`, `ReqDequeueWaitThenFed` | Close under the added compaction assumption. |
| `ReqEveryItemOnce`, `ReqPQEveryItemOnce`, `ReqDequeueClosed` | Close with no compaction assumption. |
| `ReqGetStreamUnsupported` | Closes. The header change is text only. |

**Coverage of the completeness report's patterns.**
- Every pattern it listed now has a snippet, except the cache's progress-notification clause (F5),
  which is recorded under 1.11.
- Second-tier gap: no snippet covers time exclusion between two *elections*.
  - The specs do allow it. `Campaign`'s `σv` gives `k` with create revision exactly `cr`, so a
    client can derive the order itself.
  - But it needs the same lease distinctness as N1.
  - `etcdctl elect` relies on it.

## Counts

- **Original first-tier findings:** 7. All 7 are resolved, 2 of them differently (F3, F2-C).
- **New first-tier findings:** 1 (N1).
- **Files re-checked:** the 56 changed in the area (specs and snippets), plus the 2e callers.
  Every changed spec closes; the one failure is the snippet `ReqMutexNoTwoHolders` (N1).
- **Snippets:**
  - 89 REQ/UNMET headers in the five packages;
  - 3 added and 9 changed, all checked;
  - 11 close; 1 does not (N1).
- **Second tier:**
  - stale Changes text in the two Dequeue files;
  - `ReqMutexNoTwoHolders`'s lease-revocation assumption;
  - no election-exclusion snippet;
  - cache F5 (open, 1.11).

## Bugs in the Go code

None new.
