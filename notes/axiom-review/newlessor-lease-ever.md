# `lease.NewLessor` widened with `leaseEver γl []` (axiom review, 2026-11-05)

**Reviewed**: the trust-boundary axiom `lease.NewLessor.wp_proof`
(`Spec/go_etcd_io/etcd/server/v3/lease/NewLessor.lean`) as the lease-expiry plan's E3 (c), route (A)
widens it: the postcondition gains `lease.leaseEver γl []` (the owner's half of a ghost variable `U`,
the ids the lessor ever had; the other half in `lessorRdBody` with `histOnce hs ∧ histIn hs U`).
Text as applied on branch `lease-expiry` at `2796280ca2` (definitions in
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`: `LessorRdNames`' fourth name, `snapHas`,
`histIn`, `leaseEver`, `lessorAt_empty`); this branch is based on `f5eec16dd1`, before the widening,
and adds no code. Read with it: the proved specs that use `leaseEver` (`lessor.Grant.spec`: `id ∉ U`
unless monotone, returns `U ++ [id]`; `lessor.Recover.spec`: `⌜recs = []⌝ ∨ leaseEver γl U`, records'
ids `∉ U`, returns `U ++ ids`; `Revoke`/`Attach`/`Detach` leave `U`), the other lessor axioms
(`Renew`, `Promote`, `Demote`, `Stop`, `scheduleCheckpointIfNeeded`), the rest of `NewLessor`'s post
(`leaseOwn γl [] ∅`, `leaseRevokers γl []`, `lessorRdInv`, `ttlTie`, the `Lookup` clause,
`lessorExpiredC`), and `NewServer`'s call. Go at the etcd pin (`.lake/go-src/etcd`, `249d76bea7`):
`server/lease/lessor.go`, `server/storage/schema/lease.go`.

## Verdict

**Survives.** No Go program found that panics or returns a wrong result under a proof from the
widened axiom with the lessor's other specs. The new conjunct is ghost state that a proof of
`NewLessor` would allocate at `[]` beside the single snapshot `(∅, ∅, ∅)`, where `histOnce` and
`histIn` hold vacuously; it is true because the Go lessor is empty when `NewLessor` returns, which
the precondition (an empty `lease` bucket) guarantees.

## The key question: does a fresh lessor really have no lease?

Go: `newLessor` (`lessor.go:212-249`) makes empty `leaseMap`/`itemMap`, then `initAndRecover`
(`:808-835`) loads one `*Lease` per record of the `lease` bucket (`schema.MustUnsafeGetAllLeases`,
`UnsafeForEach` through the batch transaction: the writer's contents). So with records in the bucket
the fresh lessor has leases, and `leaseEver γl []` (hence `lessorAt γl 0 (∅, ∅, ∅)`, by
`lessorAt_empty`) would be false.

The precondition excludes it: `backend.rbPart d.γB S r ∗ ⌜(r.lookup "lease").getD ∅ = ∅⌝` with
`S "lease"` and `mvcc.leaseParams d.P` (the `lease` bucket tracked, in `γ.rbD`). `rbPartF`
(`storage/backend/InvBackend.lean:387`) holds, for every tracked bucket of `S`, the ghost element at
`r.lookup n`, the writer's contents of that bucket (absent if absent). So the `lease` bucket is absent
or empty in the writer's contents, which is what `UnsafeForEach` reads: `lpbs = []`, the loop adds
nothing. Its only caller, `NewServer` (`NewServer.lean:601`), discharges it from the fresh file's rest
buckets (`HDr.1`, `bootBackend_of_bootLeft`): a first start only, as E2 revision 5 says. A restart
over a backend with leases cannot call it (the precondition is false there), which is a limit of the
spec, not a soundness gap.

## Attacks tried

1. **Leases already in the bucket** (above): refuted by the precondition; the backend's tracked-bucket
   ghost state is tied to Go by the backend's own (reviewed) axioms, `openbackend-recs.md`,
   `lessor-apply-ok.md`.
2. **A second lessor on the same backend**: lessor A grants `5` (its record put through the caller's
   `rbPart (· = "lease")`); a second `NewLessor` needs that part at an empty bucket, false while the
   record is there; after a direct `schema.UnsafeDeleteLease` it is empty in Go too, and B is empty.
   Each `NewLessor` allocates its own `γl` (`lessorPinR`), so A's and B's `leaseEver` never meet.
3. **Duplicating `leaseEver γl []`**: only `NewLessor` gives one, once per `γl`; it is a half of a
   `dghostVar` whose other half the invariant holds, so a second copy would agree to `False`. `Grant`
   returns `U ++ [id]` (never `[]`); `Recover` with `recs = []` takes the `⌜recs = []⌝` arm and does
   not consume the caller's half, which then still says `U`: true, since the snapshot `Recover`
   appends has no id.
4. **Something else writes the maps or `ttl`** (so the history, `histIn`, `ttlTie` drift from Go):
   every write in `server/lease/*.go` is in a proved function: `leaseMap` `:311` `Grant`, `:355`
   `Revoke`, `:606` `Recover`, `:820` `initAndRecover` (in `NewLessor` and the proved `Recover`);
   `itemMap` `:567` `Attach`, `:594` `Detach`, `:607` `Recover`; `l.ttl` `:302` `Grant`, before the
   lease is inserted, and `:820`. The axioms `Renew` (`refresh`, reads `ttl`), `Promote`
   (`refresh`), `Demote` (`forever`), `Stop`, `scheduleCheckpointIfNeeded` (reads `ttl`,
   `remainingTTL`), and `runLoop` (reads the map, sends on `expiredC`, calls the checkpointer) write
   none of them, and their posts give no ghost resource.
5. **Re-granting a revoked id** (`histOnce`: one `*Lease` per id over an interval): Go allows
   `Grant(5)` after `Revoke(5)` with a new `*Lease`; the revocable mode's `id ∉ U` refuses it, so
   the spec is weaker than Go there (completeness: the apply thread must show the log's grant ids
   distinct, the plan's E3 (b)), not unsound. In the monotone mode no lease leaves the map (only
   `Revoke`/`Recover` remove one, both need the revocable mode or `L ⊆` the records), so `id ∈ U`
   means `id ∈ L` and Go's `ErrLeaseExists` (`:297`) is the error arm.
6. **`Recover` reusing an id with a fresh `*Lease`**: an id live before `Recover` is in `U`
   (`histIn`), and the records' ids must be `∉ U`; in the monotone mode the premise `L ⊆` records'
   ids then forces `L = []`. So `histOnce` is not broken by `Recover`'s fresh objects (and `Recover`
   is proved).
7. **The goroutine started by `NewLessor`** changing the state before the caller looks: `runLoop`
   only reads `leaseMap` (`findExpiredLeases`, `expireExists`) and the heap; with an empty map it
   sends nothing and schedules no checkpoint.
8. **`Lookup` and expiry** (`NewLessor`'s `Lookup` clause, `lessorExpiredC lp GA`): unchanged by the
   widening; they give `GA id` of a lease in the map, never `U`-facts. Reviewed earlier
   (`lease-grant-lessor.md`).

Not tried: a Lean counterexample (no attack reached a Go panic or wrong result); restarts that
recover leases (no spec covers them yet: the plan's S3/S4).

## Results resting on it

Unchanged set: every result through `NewServer` (`etc/tcb-report.py --roots NewLessor` after the
widening lands); the new consumers are `lessorAt_empty` in `NewServer` and E2's `leaseTTLRow`.
