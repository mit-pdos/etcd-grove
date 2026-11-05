# `lease.NewLessor` widened with the requested-TTL map (axiom review, 2026-11-05)

**Reviewed**: the trust-boundary axiom `lease.NewLessor.wp_proof`
(`Proof/go_etcd_io/etcd/server/v3/lease/NewLessor.lean`, its triple in
`Spec/go_etcd_io/etcd/server/v3/lease/NewLessor.lean`) as commit `decf626b24` changes it against
`6d7f64326e` (the lease-expiry plan's S2–S4, Q-S6 (A-ii)): the readers' names `LessorRdNames` gain a
fifth component, a ghost map `Q` (id to requested TTL) allocated empty, its whole authority in
`lessorRdBody` with the new clause

    reqOk hs Q := (∀ i σ id t r, hs[i]? = some σ → id live in σ → σ.2.2[id] = t → Q[id] = r → r ≤ t)
                ∧ (∀ id r, Q[id] = r → everIn hs id)

(signed), and `histOnce` made ids-only (an id live at `i` and `k ≥ i` is live between, whatever
`*Lease`). Read with it (all in `Proof/go_etcd_io/etcd/server/v3/lease/` and
`Spec/go_etcd_io/etcd/server/v3/lease/` at `decf626b24`): `leaseReqIs` (`InvLessor.lean:429`, a
discarded element of `Q`), `ttlTie`, `histIn`, `leaseEver`; the proved `lessor.Grant.spec` (returns
`leaseReqIs γl id ttl`) and `lessor.Recover.spec` (records' ids may now be in `U` when live, `id ∈
L`; the caller names `rq` with `rq id ≤` the record's TTL and holds `leaseReqIs γl id (rq id)` for an
id of `U`; returns every record's `leaseReqIs`); the law `leaseTTLAt_ge_req`
(`LessorHist.lean:566`); the axioms used beside it: `Renew`, `Promote`, `Demote`,
`scheduleCheckpointIfNeeded`, `schema.MustUnsafeGetAllLeases`, `EtcdServer.leaseTimeToLive` (its
`leaseTTLRow` arm); and the client that uses the law, `examples/etcd/leaseexpiry`'s `Main`. Go at the
etcd pin `673da07c8` (`server/lease/{lessor,lease}.go`; identical to `.lake/go-src/etcd` at
`249d76bea7` for these two files), `GOTOOLCHAIN=go1.27.3`.

## Verdict

**Survives.** The widening is ghost-only: a fresh ghost map at `∅` is allocatable
(`ghost_map_alloc`) and `reqOk [(∅, ∅, ∅)] ∅` holds vacuously. The claim the clause makes of Go,
"every TTL a lease has while it is in the lessor's map is at least the TTL it was requested at", is
true of Go, because the `ttl` field (the history's TTL, through `ttlTie`'s `lsF "ttl" l ↦□ t`) is
written only twice, both times raising and both before the lease enters the map; and the specs that
issue requests (`Grant`, `Recover`) or remove ids (`Revoke`, `Recover`) keep an id's request unique
over the history. No program found that panics on a TTL below its request and verifies. The three
DRAFT `sorry`s in `Recover`'s proof stand for true statements (below).

## The claim, from the Go code

`l.ttl` is written at exactly two places in `server/lease/*.go` (non-test):

- `Grant`, `lessor.go:292,301-302`: `NewLease(id, ttl)` then `if l.ttl < le.minLeaseTTL { l.ttl =
  le.minLeaseTTL }`, before `le.leaseMap[id] = l` (`:311`). So the TTL is `grantTTL mt ttl ≥ ttl`
  (`grantTTL_ge`, signed, as Go's `int64` compare). `minLeaseTTL` is written only by `newLessor`
  (`:231`; `lF "minLeaseTTL" lp ↦□ mt`).
- `initAndRecover`, `lessor.go:817-822`: `if lpb.TTL < le.minLeaseTTL { lpb.TTL = le.minLeaseTTL }`,
  then `&Lease{ttl: lpb.TTL, ...}` into the map. So the TTL is `grantTTL mt` of the record's TTL, at
  least the record's TTL, at least any `rq` with `rq ≤` the record's TTL (`Recover.spec`'s premise).

Everything else only reads it: `persistTo` (`lease.go:56`), `TTL()` (`:65`, `:80`), `Renew`'s return
(`lessor.go:455`), the checkpoint scheduler (`:794`). `Checkpoint` writes `remainingTTL` (`:373`),
`Promote` `expiry` (through `refresh`, from `remainingTTL`), `Demote` `expiry` (`forever`), `Renew`
`expiry` and, with a checkpointer, proposes a checkpoint; none writes `ttl` or the maps. So a TTL the
history records for an id (`ttlTie`: the `ttl` field of the id's `*Lease` in that snapshot) is fixed
for that `*Lease`; it can differ between snapshots only when the `*Lease` is replaced (`Recover`), and
then it is again `≥` the recovered record's TTL. (It may go down across a `Recover`, e.g. a member
with `minLeaseTTL` 7 recovering a leader's record at 3 with its own minimum 1; that is why
`leaseTTLAt_ttl_agree` was replaced by the inequality, and the inequality to the request survives
it.)

**Go check** (`examples/axiomcx/newlessorreqmap/newlessorreqmap_test.go`, public API, real
backend, run at the pin): `TestTTLNeverBelowRequest` grants requests `3, -7, 10, 0` on a lessor
with minimum 2, then `Promote`, `Renew`+`Checkpoint(id, 1)`, `Demote`+`Promote`; another with minimum
7 grants the same and `Recover`s the first's backend; a third (minimum 1) `Recover`s the second's.
After each step `Lookup(id).TTL() ≥ request`, else `panic`. Output: TTLs `3, 2, 10, 2` (A at every
stage), `7, 7, 10, 7` (B before and after `Recover`), `7, 7, 10, 7` (C); `PASS`.
`TestRegrantBelowRequest` shows the one Go path to a TTL below an earlier request:
`Grant(5, 100)`, `Revoke(5)`, `Grant(5, 10)`, after which `TTL() = 10`; `PASS` (it only logs). The
specs exclude it (attack 2).

## Attacks tried

1. **Renew, Checkpoint, Promote, Demote lower a TTL** (the brief's focus). They do not touch `ttl`
   (above); the history's TTL is not `remainingTTL` (that is `Checkpoint`'s, read by `Promote`), and
   `TimeToLive`'s spec ties the history to `GrantedTTL` (`l.TTL()`, `v3_server.go`), not to the
   answer's `TTL` (`Remaining()`, which does go below the request, and negative). Their specs give
   no ghost resource and take only `lessorInv` (persistent), so they cannot append to the history;
   `ttlTie`'s `↦□` of `ttl` would make a spec writing it unprovable anyway. `Checkpoint`'s post
   leaves the backend record's TTL existential (`∃ t`): weaker than Go (it is `l.ttl`), which only
   stops a later `Recover` caller from proving its `rq ≤` premise for that record: incompleteness,
   not a gap.
2. **Re-granting a revoked id with a smaller TTL** (Go allows it, `TestRegrantBelowRequest`): a
   holder of `leaseReqIs γl 5 100` would then see `leaseTTLAt γl i 5 10`, and `leaseTTLAt_ge_req`
   would prove `100 ≤ 10`. Blocked: `Grant.spec` in the revocable mode needs `id ∉ U`, and `5 ∈ U`
   (`leaseEver`, `histIn`) once granted; in the monotone mode `Revoke` is not callable
   (`lessorRevocable`). At the server, the apply thread discharges `id ∉ U` from the log's
   revocable-mode grant ids being distinct (`srvGrantFresh`, `srvEverOk`, `kvGrantIds`: a premise of
   the cluster's clients, not of this axiom). With the second `Grant` unprovable, `Q[5]` can never
   be inserted twice either (`ghost_map` elements are discarded, so agreement would refute it).
3. **`Recover` lowering a TTL below an earlier request**: a member grants `5` at `100`; a snapshot
   brings a record `5` at `10` (only possible in Go after a revoke and a re-grant, attack 2). The
   record's id is in `U`, so `Recover.spec` needs `id ∈ L` and `leaseReqIs γl 5 (rq 5)`, which by
   agreement is `rq 5 = 100`, and the premise `rq 5 ≤ 10`: false, so the call is unprovable. The
   caller (`applySnapshot`, DRAFT) must derive `rq ≤` the record's TTL from the log, which needs the
   distinct grant ids again (`appliedTable_granted_live`, `ImageLeases.lean`, DRAFT): true of Go
   under that premise, since the leader's record of a grant at request `r` has TTL
   `max(r, leader's minimum) ≥ r`.
4. **A client opening `lessorRdN` and inserting into `Q`** (the invariant and `lessorRdBody` are
   public): it can insert only a key not in `Q` with `everIn hs id` and `r ≤` every TTL the history
   has given `id` (to re-establish `reqOk`); the future TTLs of such an id are again bounded by `Q`:
   `Grant` needs `id ∉ U ⊇` the history's ids, `Recover` needs the `leaseReqIs` that agrees with the
   inserted value and `rq ≤` the record's TTL. It cannot change or delete an issued value (the
   elements are discarded). So such an insertion asserts nothing false.
5. **A request issued for an id that never becomes live, then granted later lower**: `Grant` issues
   `leaseReqIs` only on success (the error arms leave `U` and `Q`), `Recover` only for its records,
   which become live in the appended snapshot (`reqOk`'s second clause holds of them).
6. **Signedness**: a negative request (`Grant(2, -7)`) is raised to the minimum; `reqOk` and
   `grantTTL` compare with `sint.Z`, as Go's `int64` `<`. A request above `MaxLeaseTTL` is
   `ErrLeaseTTLTooLarge` (`:286`), no request issued.
7. **The records `Recover` reads** (`MustUnsafeGetAllLeases`): its post gives each record's id, TTL
   and remaining TTL as the caller's `recs` with `bktEnts = recs.map leaseRecEnc`; `leaseEnc` is
   opaque, so a caller can only name the triples that were written (`Grant`'s `rbSet ... (leaseEnc id
   (grantTTL mt ttl) 0)`, `Checkpoint`'s `∃ t`), not a smaller TTL with the same bytes. The ids are
   distinct (`leaseRecs_nodup`, from the bucket's keys).
8. **`TimeToLive`'s `GrantedTTL`** (the client side of the law, `leaseexpiry`'s `Main`): under the
   row the leader path's `GrantedTTL` is `l.TTL()` of the `*Lease` `Lookup` found, the snapshot's TTL
   at that index (`ttlTie`), so `≥` the request. `Main` uses it only to exclude `GrantedTTL = 0` for
   a lease requested at `1`, true in Go (TTL `≥ max(1, minLeaseTTL)`). The `TTL = -1` answer (an
   expired, not yet revoked lease's `Remaining()`) is not tied to the history.
9. **`NewLessor` itself**: the post's history is the single empty snapshot because the precondition's
   `lease` bucket is empty (`newlessor-lease-ever.md`, attack 1); `Q = ∅` matches it. The started
   `runLoop` writes no TTL.

Not tried: a Lean counterexample (no Go panic found to build one from); concurrent `Grant`/`Recover`
on one lessor (both under `le.mu`'s write lock; the history is appended under it).

## The DRAFT `sorry`s inside `Recover`'s proof

All three are in `Proof/go_etcd_io/etcd/server/v3/lease/LessorRecoverLemmas.lean`; each stands for a
statement true of Go (and of the ghost state):

- `recover_hist` (`:382`): from `Q` with `reqOk hs Q`, insert `rq id` for the ids of `Un` not in `U`
  and give `□ [∗list] id ∈ Un, leaseReqIs γl id (rq id)` with `reqOk (hs ++ [σ']) Q'`. True: an id
  not in `U` is in no snapshot (`histIn`), so not in `Q` (`reqOk`'s second clause); an id of `U` comes
  with `leaseReqIs γl id (rq id)`, which agrees with `Q` (so no insert); every id live in `σ'` is in
  `Un` (`hin`), so the new snapshot's TTLs are bounded by `hrq`; the old snapshots' bounds are
  unchanged (new keys are not in them); the new keys are live in `σ'` (`hUn`). Duplicates in `Un`
  insert the same value.
- `closers_recover` (`:648`, the `hrq` argument of `recover_hist`): a live id of the recovered
  snapshot has TTL `grantTTL mt` of its record's TTL (`recTTLs_lookup`, ids distinct: `hnd`), which
  is `≥` the record's TTL (`grantTTL_ge`) `≥ rq id` (the premise). This is exactly Go's
  `initAndRecover` raise (`:817-818`).
- `lessor_live_perm` (`:729`): the live set reordered to a permutation `Lr`. True: with the
  authority at `1` and both halves of element `true` the ghost map is updatable to `Lr`
  (`lessor_live_set`'s proof); `lessorAuth`'s grants, `leaseClosers`' and `leaseRevokers`'
  membership facts (`id ∈ L ↔ C.lookup id`, item ids `∈ L`) are invariant under `Perm`. Go has no
  order: the list is ghost.

The `sorry`s on `Recover`'s caller side (`ImageLeases.lean:84,94,105`, `EtcdServer__applySnapshot.lean:136,141`)
are outside this review; the one that bears on `reqOk` is attack 3's: it is true only with the log's
revocable-mode grant ids distinct.
