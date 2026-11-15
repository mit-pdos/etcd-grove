# Review: batch 3c (the lessor), provability, round 1

Reviewer agent, 2026-11-09, at `a098c18d14` (the 3c draft). Read-only. Targets:
`SpecPlan/Spec/go_etcd_io/etcd/server/v3/lease/` (Api, Internal, the 44 specs), `examples/specreq/lease/lessor.go`,
`nonissues/etcd-lease-keys-mid-apply.md`, the `## from 3c` sections of `notes/specs-only/req/*.md`.
Go: `.lake/src/server` (`a4d2bb17`): `lease/lessor.go`, `lease/lease.go`, `lease/lease_queue.go`;
callers in `etcdserver/server.go`, `etcdserver/v3_server.go`, `storage/mvcc/kvstore_txn.go`. Callee
specs read: W0's `Model.lean`/`State.lean` (lease part), mvcc's `mvccDeleter_rdOk.spec`
(`storage/mvcc/Api.lean:653`), Perennial's `sort.Sort.spec` and `isSorter`. Findings formed before
reading `batch-3c.md`; what it changes is at the end.

## First tier

### P1. `Revoke` is unsound for the `rdOk` it admits: the deleter may change the lessor arbitrarily

`rdOk`'s `DeleteRange` triple (`Api.lean`, `rdOk`) lends the writer's token and gets back
`∃ n'' ls'', D … ∗ lessorState γ n'' ls''`, with no relation between `ls''` and `ls'`. So a
deleter whose `DeleteRange` uses the token to `Revoke(id)` the lease being revoked (once, by a
flag; it can build its own `rdOk` for the nested call) or to `Recover` the lessor meets `rdOk`.
The Go code then breaks:

- nested `Revoke(id)`: the inner call closes `l.revokec` (`lessor.go:335`, deferred) and removes
  the lease; the outer's deferred `close(l.revokec)` runs again: **panic, close of closed channel**;
- nested `Recover(b2, …)`: the outer's `UnsafeDeleteLease(le.b.BatchTx(), …)` (`lessor.go:359`)
  writes `b2`'s bucket, whose batch lock this thread does not hold (`rdOk` lends `beTxHeld ls.be`
  for the *old* `ls.be`): an unlocked write, and the proof has no `beLeases`/`beTxHeld` pair for it.

The proof sketch also takes the close right "at the first lock" (`lessor__Revoke.lean`, sketch),
which leaves no way to prove even the inner call (its close right is gone while the object is
still in the map).

Fix: in `rdOk`'s `DeleteRange` post, `⌜ls''.leases = ls'.leases ∧ ls''.be = ls'.be ∧ ls''.bkt =
ls'.bkt⌝` (or the sharper `ls'' = ls'` or `ls''= ls'.detach id' [k]` for some `id'`); mvcc's
instance meets it (its `D` has `ls' = delsLs ls (…)`, and `delLs` only detaches:
`storage/mvcc/Api.lean:129-140`), and so does the snippet's `recordDel`. Restate the sketch: the
close right is taken at the **second** lock, where the constraint (by induction over the deletes)
shows `leaseMap[id] = e.obj` still, so it is in the invariant.

### P2. `SetCheckpointer` (assumed) is false: a second call races, and `nil` after non-`nil` panics

`SetCheckpointer.spec` takes no token: any goroutine, any number of times, `cp = func.nil` allowed.
The code reads `le.cp` **unlocked** after a locked test: the run loop at `lessor.go:679`
(`le.cp(...)`, after `findDueScheduledCheckpoints` saw `le.cp != nil` under the lock, `:773`), and
`Renew` at `:437` (after `clearRemainingTTL := le.cp != nil && …` under the read lock, `:412`). A
`SetCheckpointer(nil)` between the test and the call makes Go call a nil func: **panic**; a
`SetCheckpointer(cp2)` there is a data race (stuck in Perennial's heap model). Reachable from the
specs: `NewLessor`, `SetCheckpointer(cp)`, `Promote`, a `Grant` with a TTL above the checkpoint
interval, then `SetCheckpointer(nil)` concurrently with the run loop's due checkpoint (or with a
`Renew` of a checkpointed lease). A single call from `nil` is safe (the unlocked read is ordered
after the write by the lock), which is the server's only use (`server.go:395`, before the member
can be primary).

Fix: a once token, `lessorCkptTok le` (exclusive), from `NewLessor`'s post, consumed by
`SetCheckpointer` (realization: `le.cp ↦ nil` in the lock invariant with the token's half; after
the write, `le.cp ↦□ cp ∗ (cp = nil ∨ ckptOk cp)`, so the unlocked reads are of a frozen field).
Worth a `nonissues/` entry ("`SetCheckpointer` must be called at most once, before the lessor is
primary"; the `Lessor` interface does not say so; etcd meets it).

### P3. `NewLessor` (assumed) with a negative `leaseRevokeRate` makes `Promote` panic

`NewLessor.spec` quantifies every `cfg : LessorConfig`, including the unexported
`leaseRevokeRate'` (only `0` is defaulted, `lessor.go:222`). With a negative rate and an empty
`leaseMap`, `Promote` skips the early return (`len(le.leaseMap) < le.leaseRevokeRate` is false,
`:494`) and indexes `leases[0]` of an empty slice (`:503`): **index out of range**. `Promote.spec`
says no panic from `isLessor`, so the two assumed specs together are false. Fix: premise
`0 ≤ sint.Z cfg.leaseRevokeRate'` on `NewLessor` (every caller outside the package passes `0`;
2e's `NewServer` too). (A positive rate is safe: `leases[0]` exists, and the float divisions and
the float-to-int conversion at `:521-525` cannot panic.)

## Second tier

### P4. `Leases` and `Revoke` cite sort specs that are not on the branch

- `Leases` (`lessor__Leases.lean`, sketch and margin: "a proof matter, not a premise"): Perennial's
  `sort.Sort.spec` needs `isSorter x own R` with a **fixed strict weak order** `R` and `Less`
  returning exactly `R a b` (`Perennial/Proof/sort/SorterBasics.lean:59-67`). `leasesByExpiry.Less`
  compares two `Remaining()` reads of the clock (`lease.go:134`); `Lease.Remaining.spec` returns
  any duration. No `R` fits, so the proof cannot call Perennial's spec. The old development had a
  trust-boundary spec for exactly this, `sort.Sort.anyLessSpec` (`specs-ref`'s
  `SpecPlan/Spec/sort/SortAnyLess.lean`: any `Less`, the result a permutation; its comment cites
  `zsortinterface.go`'s index bounds and a 1200-sort test), deleted on this branch. Is the
  inconsistent comparison a real problem? No for Go: every index pdqsort passes to `Less`/`Swap`
  is bounded by the slice's bounds, never by `Less`'s answers, and only `Swap` mutates, so it
  permutes and does not panic. No spec of the batch claims an order (`Leases`' post is a
  permutation of the live objects, `Forall₂` to `Nodup` ids), so nothing is wrong in the
  statements. Fix: restore `SpecPlan/Spec/sort/SortAnyLess.lean` as a trust-boundary spec (with its
  comment) and cite it in the sketch; `Promote` is assumed, so it needs nothing.
- `Revoke`'s `sort.StringSlice(keys).Sort()` (`Code/…/lease.lean:979`, a `MethodResolve` on
  `sort.StringSlice`): Perennial has no spec of `StringSlice.Sort` (or of its `Len`/`Less`/`Swap`),
  and the old local one (`specs-ref`'s `Spec/sort/StringSlice__Sort.lean`) is gone too. Its `Less`
  is Go's `<` on strings, a strict order (`keyLt = go.GoStringLt`), so a proved spec over
  Perennial's `sort.Sort` exists. Fix: restore the spec and cite it. The length bound (`≤ 2^62`)
  comes from the item set's size; say where from.

### P5. A law is missing for `TimeToLive`'s `0 < GrantedTTL`: every state's TTLs are at least the minimum

W0's `leaseTimeToLive` answer needs `0 < gttl` (`Model.lean:1004`); 2c answers with
`le.TTL()` of an object `Lookup` returned at some state `j ≥ i`. `leaseObj_live` gives a history
state with `e.ttl = ttl`, but nothing says that a state's TTLs are `≥ c.minTTL`, and 2d's history
tie (`req/…_etcdserver.md`, "from 3c", item 4) agrees with W0's tables on ids only (per-member TTLs).
The fact is true of the lessor (only `grant` and `loaded` set TTLs, both through `grantTTL`; the
other steps keep them; every history state comes from the lessor's own writer specs). Add
`lessorAt_minTTL.spec : isLessor le γ c ∗ lessorAt γ n ls ⊢ ⌜∀ id e, ls.leases id = some e →
c.minTTL ≤ e.ttl⌝`; 2e then supplies `0 < c.minTTL ≤ maxLeaseTTL` from the server's
configuration (also needed by 3a for W0's grant step, `0 < ttl' ≤ maxLeaseTTL`).

### P6. The realization of the lease bucket contradicts `lessorState_bkt`

`Api.lean`'s "Intended realization" puts `beLeases ls.be ls.bkt` in `le.mu`'s invariant; the law
`lessorState_bkt` lends it from the token alone (a pure entailment: it cannot take the lock), and
the Resources section says the bucket is inside `lessorState`. Only the token holder writes the
bucket (`Grant`, `Checkpoint`, `Revoke`, `Recover`/`initAndRecover`, all with the token), so the
realization that works is: `beLeases` in `lessorState`, and `lessorFields … (own 1)` = the lock
invariant's part plus the token's bucket. Restate the header (and `Recover`'s sketch, "leaves the
invariant to the caller").

### P7. The run loop mutates the notifier under the **read** lock: the realization must say who owns it

`revokeExpiredLeases` holds `le.mu.RLock()` (`lessor.go:646`) while `expireExists` calls
`Unregister`/`RegisterOrUpdate` and writes `item.time` (`:710-722`). No race in Go (no other
reader touches the notifier; its other writers, `Grant`, `Renew`, `Promote`, `Demote`, hold the
write lock), so the assumed `NewLessor` is true; but the realization ("the notifier … well-formed,
in `le.mu`'s invariant") gives a read-lock holder only a fraction of it. The realization needs the
notifier owned by "the write-lock holder, or the run loop's reader section" (a run-loop token in
the invariant). Say so in the header: it is part of what the assumed run loop rests on, and the
translated writers' proofs must use the same split. (Uncertain how Perennial's `RWMutex` spec
expresses it; it is the realization, not a statement, that changes.)

### P8. The mid-apply finding: real; the requested W0 relaxation misses one window

Traced: `Revoke` takes `l.Keys()` (`lessor.go:347`), then each `txn.DeleteRange` calls mvcc's
`delete`, which `GetLease`s and `Detach`es the key (`kvstore_txn.go:335-345`), each `Detach` a
separate critical section of `le.mu` and `l.mu` (`lessor.go:582-597`); `leaseTimeToLive`
(`v3_server.go:645-664`) reads `le.Keys()` under `l.mu` only. A leader's `TimeToLive(keys)` between
two detaches returns a strict subset of the lease's keys, a set no revision had (and W0's
`r` is independent of the lease table `i`, so only the strict partial sets are a problem: `∅` after
the last delete is `attached(r')` of the revocation's revision). Puts of one transaction
(`kvstore_txn.go:285`, an `Attach` each) likewise. The nonissue is right, and `Lease.Keys.spec`
says what the code does.

Other reads: `Lookup`, `Leases`, `Renew` read only `leaseMap`, which changes in one critical
section per `Grant`, `Revoke` (the removal, `:353-355`) and `Recover`; `GetLease` reads
`itemMap` (the apply thread's own reads only). None sees a half-applied state of the lease table.

The window the relaxation in `req/go_etcd_io_etcd_api_v3.md` ("between `attached(r) ∩
attached(r+1)` and `attached(r) ∪ attached(r+1)`") does not cover: after `Recover` (fresh objects,
empty item sets), mvcc's `Restore` re-attaches the snapshot's keys one `Attach` at a time
(`kvstore.go:390-403`), so `Keys.spec` also admits any subset of `attached(r_snap)`. In Go this is
answered `ErrLeaderChanged`, because the fresh objects' expiry is `forever` (`lessor.go:826`) and
`leaseTimeToLive` checks `le.Demoted()` (`v3_server.go:662`) — but `Lease.Demoted.spec` returns
"some boolean", so 2c cannot use that. Either W0's relaxation also admits any subset of the keys
attached at one revision during a snapshot's restore, or `Demoted` gets content (e.g. an object
made by `Recover`/`NewLessor` and not refreshed since answers `true`), or 2c keeps a premise. Add
the window to the nonissue.

### P9. Snippets: two assumptions missing

All ten snippets are provable from the specs as stated (sketches below), with these repairs:
- `ReqRecover`: `len(le.Leases()) != len(ids)` needs `ids` distinct; add it to `Assumes`.
- `ReqReaderLowerBound`, `ReqRenew`: "never revoked" must also exclude a `Recover` dropping or
  replacing the lease (`ReqRenew` says "nor recovered over"; `ReqReaderLowerBound` does not).
Missing, call-only: `Promote`/`Demote`/`SetCheckpointer` (no snippet reaches them, and P2/P3 are
exactly a call-only snippet's concern).

### P10. Smaller

- `leasesOutliveRun`'s docstring ("every lease's TTL outlasts the run from its last refresh")
  is not what the run loop tests: `refresh` uses the checkpointed `remainingTTL` and `Promote`
  adds `extend` (`lease.go:85`, `lessor.go:488`). State it as what `NewLessor` relies on: "no run
  loop of this run's lessors finds a lease expired (`Remaining() ≤ 0` while primary)".
- `Revoke`'s `rdOk` `End` triple: the comment says `End` "must not call the lessor"; the triple
  does not give the token, so the only lessor calls left are readers, which deadlock on `le.mu`
  (partial correctness: fine). Say "may only block", not "must not".

## (a)–(g) of the brief

**(a) Writer token / reader history vs the locking.** Every `LessorState` change is under `le.mu`
(write) by a holder of the token: `Grant`, `Revoke`'s removal, `Checkpoint`, `Attach`/`Detach`
(mvcc on the apply thread, or the bootstrap's `NewStore`/`restore`), `SetRangeDeleter` (NewStore,
`kvstore.go:117`, `watchable_store.go:107`), `Recover` (`server.go:1087`, apply thread). The other
writers of the lessor's fields (`Renew`, `Promote`, `Demote` on the raft loop, `server.go:769`,
the run loop) change only time-related fields (expiry, notifier, heaps, `demotec`), not the model:
consistent with taking `isLessor` only. `le.rd` read unlocked in `Revoke` (`:339`): the token's
half, fine. `l.ttl` read unlocked by `TTL()`/`Renew`: frozen before publication (`Grant` raises it
before `leaseMap[id] = l`, `:301-311`). Readers: `Lookup`/`Leases`/`GetLease` under `RLock` see the
current state, `≥` any `lessorLb` (monotone history); `Keys` under `l.mu` only sees the current
state's `keys l` provided every itemSet writer (`Attach`, `Detach`: both locks; `SetLeaseItem` has
no caller) appends the history under both locks (as the sketch says); `Renew`'s `ErrLeaseNotFound`
from `revokec` is at the removal state, after its read (needs P1's fix for "closed only after
removal"). Sound, with P1, P2, P6, P7.

**(b) The seven assumed specs.** `Stop`: true (`lessorStop` once; `<-doneC` may block).
`Demoted`, `scheduleCheckpointIfNeeded` (the `Debug` is guarded by `le.lg != nil`, `:759`; a non-nil
zero `Logger` would panic, which `isLogger` excludes; `heap.Push` with `LeaseQueue.Less` a strict
order; `int64(d.Seconds())` cannot panic): true. `Renew`: true given `ckptOk` and P2's once-ness
(its `ErrLeaseNotFound` via `revokec` also needs P1). `Promote`: true given P3 (no TTL change: only
expiries move; W0's `TimeToLive` already allows a remaining TTL above the granted one).
`NewLessor`: true given P3 and the realization notes P6/P7. `SetCheckpointer`: false (P2).

**(c) Mid-apply.** Real (P8); no other read sees a half-applied lease table.

**(d) `rdOk`, `ckptOk`.** `rdOk` is too weak in what it requires of `DeleteRange` (P1); with the
fix, mvcc's `mvccDeleter_rdOk.spec` discharges it (`D`'s `ls' = delsLs ls (presentKeys …)`; its
`beTxHeld` from `mvccTxn_held`, once 4a identifies `kbHeld B` with `beTxHeld (storage B)`). (The
completeness review's F3, the server's own `s.kv.Write` closure passed to `Recover`, needs the same
law for that closure.) `ckptOk`: the server's closure (`server.go:395-404`) returns
`lease.ErrNotPrimary` or `nil` (the `raftRequest` error dropped): dischargeable by 2d with a
`raftRequest` spec callable from any goroutine with `context.Background()`; the restriction is
sound because the error set is the closure's.

**(e) Expiry.** `expiredCh_recv` gives the payload only with `c.expiry = true`; W0's
`EnvStep.leaseExpire` needs only `cfg.leaseExpiry = true` and the lease live at the revoke's apply
(the applier's `Revoke` answers `ErrLeaseNotFound` otherwise, no step), so nothing more about
"really expired" is needed, and `expiredSl`'s `leaseObj` gives the `ID` read
(`server.go:882`). With the mode off, `leasesOutliveRun` at `NewLessor` is the only premise: no
other lessor path revokes, and `Renew`/`Promote`/`Checkpoint` are model no-ops. (Docstring: P10.)

**(f) Sorts.** P4: no spec claims an order; the comparator's inconsistency is harmless in Go but
needs the any-`Less` trust-boundary spec, which the branch lost.

**(g) Snippets.** Proof sketches, in brief:
- `ReqGrantLookup`: `Grant` (success disjunct: `id ≠ 0`, `ttl ≤ Max`, not live), `lessorState_at`,
  `lessorAt_obj`, `leaseObj_id` (`l.ID`), `TTL.spec` (`max ttl minTTL`, `c.minTTL = minTTL`),
  `Lookup` at the writer's own `lessorAt` (`lessorState_le`, `lessorAt_agree`); the three error
  calls: each leaves one disjunct; `init`'s `errIs` for the comparisons.
- `ReqAttachDetach`: `GetLease` (items `k = 0`), `Attach` (live), `GetLease` (`= id`),
  `Lookup` + `Keys` (`ls.keys e.obj k`), `Detach`, `GetLease` (`0`), `Attach(id+1)` (not live).
- `ReqRevokeDeletes`: `SetRangeDeleter`; `rdOk` with `P := beApplyTok be`, `D` = `recordDel`'s
  fields, the lock (`beTxHeld be`), `ls'` the detaches; `Revoke`'s success post gives `ks` sorted
  and equal to `{a, b}`; `Q` gives `ended`, the token back; `Lookup`/`GetLease` on `ls'.remove id`;
  the second `Revoke` is `ErrLeaseNotFound`. `recordDel` satisfies P1's constraint.
- `ReqLeasesList`, `ReqReaderLowerBound`, `ReqRenew`, `ReqCheckpointNoop`, `ReqRecover`,
  `ReqExpiredChannel` (contradiction from `c.expiry = true` when `expiry` is false), `ReqStop`:
  provable (P9's repairs).

## Not vacuous

`lessorState_le`/`lessorAt_agree`/`leaseObj_agree` fail at `True` (they conclude pure facts);
`expiredCh_recv`'s gate has content at `expiry = false`; `NewLessor`'s `exp` constrains the
receive. No vacuous disjunct found (`Checkpoint`'s two outcomes are a real case split).

## After reading `batch-3c.md`

The author lists the sort question as open (P4 answers it: restore the two local sort specs) and
asks the user about `ckptOk`'s restricted errors (sound, P (d)). The report does not mention the
nested-deleter problem (P1), the checkpointer race (P2), the rate premise (P3) or the restore
window (P8). No Go bug found beyond the nonissues already filed; P2's once-only call is a
`nonissues/` candidate (a precondition etcd meets, undocumented).

## Ranking (need of revision)

1. `Api.lean` (`rdOk`: P1; realization: P6, P7; missing law: P5) and `lessor__Revoke.lean` (P1's sketch).
2. `lessor__SetCheckpointer.lean` + `NewLessor.lean` (P2's token, P3's premise).
3. `lessor__Leases.lean`, `lessor__Revoke.lean` (P4: the sort specs).
4. `nonissues/etcd-lease-keys-mid-apply.md` and the W0 request (P8's restore window);
   `Lease__Demoted.lean` if that route is chosen.
5. `examples/specreq/lease/lessor.go` (P9).
6. The rest (`Grant`, `Checkpoint`, `Attach`, `Detach`, `GetLease`, `Lookup`, `Keys`, `TTL`,
   `Remaining`, `Recover`, `ExpiredLeasesC`, `Stop`, `Promote`, `Demote`, the internal helpers): sound as
   stated.

## Verdict

Not done: three first-tier findings, each with a local fix (a constraint in `rdOk`'s delete
triple, a once token for `SetCheckpointer`, a `leaseRevokeRate` premise on `NewLessor`). The
design (one writer token, a persistent reader history) fits the code's locking and serves W0's
lease reads and 2d's expiry loop; with P4's sort specs restored and P5's law, the lease part of
W0 is provable from these specs, up to the `TimeToLive` key set (P8), which W0 must relax.
