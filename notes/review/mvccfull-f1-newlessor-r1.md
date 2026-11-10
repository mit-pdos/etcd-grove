# Review r1: `lease.NewLessor.specR` (mvccfull F1 Draft, HEAD `a4c071c7dd`)

Target: `Spec/go_etcd_io/etcd/server/v3/lease/NewLessorR.lean`, a restatement of the axiom
`lease.NewLessor.spec` (`Spec/.../lease/NewLessor.lean`, assumed in `Proof/.../lease/NewLessor.lean:26`)
over a `Lease` bucket that holds records. It is meant to become an axiom, so it is trusted text. Go:
`/home/ubuntu/.claude-F/jobs/fa46cf72/tmp/srv/lease/lessor.go` (cited as `lessor.go`), the backend
`.../srv/storage/backend/batch_tx.go`, `backend.go`, `.../srv/storage/schema/lease.go`.
The review is read-only: nothing was built. I ran `etc/bounds-check.py`, which only reads.

## What is good

- **The recovered state is what the proved `Recover` gives.** Every new post conjunct (`leaseOwn γl Lr ∅`,
  `leaseRevokers γl Lr`, `leaseEver γl ids`, `□ leaseReqIs`, `lessorAt … (recMap (recs.zip ls), ∅, recTTLs …)`)
  is `lessor.Recover.spec`'s post at a fresh lessor (`L = []`, `U = []`, `[] ++ ids = ids`). That post is
  proved (`Proof/.../lease/lessor__Recover.lean:29`, via `closers_recover` and `lessor_live_perm`). So
  `lessorInv`, `lessorAuth` and `lessorRdBody` provably admit such a state for any `recs` that meets the
  entries' equation, including id `0`. Only the index (`0`, not some `i`), the TTL minimum (cfg's) and the
  token count go beyond what `Recover` proves. I check those three below.
- **Each clause checked against Go:**
  - *The records are read and decoded without a panic.* `initAndRecover` takes the lock outside apply,
    creates the bucket and calls `MustUnsafeGetAllLeases` (`lessor.go:811-813`). That function panics only
    on a value that does not decode (`schema/lease.go:31-45`). The premise
    `bktEnts … = recs.map leaseRecEnc` excludes such a value, through the trusted
    `schema.MustUnsafeGetAllLeases.spec` (`Spec/.../schema/MustUnsafeGetAllLeases.lean`), which the proved
    `initAndRecover.spec` already uses.
  - *The bucket is unchanged.* `CreateBucketIfNotExists` (`batch_tx.go:137`) does nothing to an existing
    bucket, so the post's `r.insert "lease" (getD ∅)` is right.
  - *The record ids are distinct.* The premise implies it: `lease.leaseRecs_nodup`
    (`MustUnsafeGetAllLeases.lean:29`). A key is the id's big-endian bytes, and the equation forces the
    key and the value's id to agree.
  - *TTLs raised to the minimum.* Go uses a signed `lpb.TTL < le.minLeaseTTL` (`lessor.go:817-819`), and
    `grantTTL` (`LeaseRecord.lean:32`) compares with `sint`. `le.minLeaseTTL = cfg.MinLeaseTTL` with no
    default (`lessor.go:231`). The only writes to `ttl` are at construction (`lease.go:45`,
    `lessor.go:302`, `:822`), so `ttlTie`'s read-only `ttl` holds. `remainingTTL` is the record's
    (`:828`) and `expiry` is `forever = time.Time{}` (`:43`, `:826`), the zero value `recLease` has.
  - *Notifier and heap empty.* `Init` of the fresh notifier rebuilds from its empty queue
    (`lease_queue.go:75-81`), and `heap.Init` runs on the fresh heap (`:832`). So no recovered lease
    expires before `Promote`: `Remaining()` is `MaxInt64` at a zero expiry (`lease.go:117-123`).
  - *One write-back.* `UnsafeCreateBucket` always does `pending++` (`batch_tx.go:144`), whether or not
    the bucket held records. So the first `Unlock` writes back once (`:328-333`), and it may also commit
    when `pending >= batchLimit` (`:355`). `ForceCommit` (`backend.go:377`) is `Commit`, i.e. `lock`, then
    `commit`, then `Unlock` (`batch_tx.go:362-366`). The commit may run hooks that write, but `commit`
    sets `pending = 0` (`:300`), so that `Unlock` does not write back. One token is true with records as
    without them, because the records change neither `pending` nor the commits.
  - *The mono mode.* The single snapshot is `histMono`, and `histCover`/`histIn` hold for `U = ids`.
    `ever_live_mono`'s conclusion (every id ever had is live) holds trivially.
  - *The history index.* `lessorAt γl 0 σ` for a freshly allocated history `[σ]` does not contradict
    `lessorAt_empty` (`InvLessor.lean:1243`), which needs `leaseEver γl []`. With records the caller gets
    `leaseEver γl ids`, so it cannot derive `lessorAt γl 0 (∅, ∅, ∅)`.
  - *`runLoop` with live leases.* `revokeExpiredLeases` reads only under the lessor's read lock and sends
    only map leases (`lessor.go:640-662`). Every map lease has `GA` of its id, from the new
    `□ GA id` premise, so `lessorExpiredC` and the `Lookup` clause carry over unchanged.
- **The original is an instance.** I checked conjunct by conjunct: at `recs = []` the original's
  `getD ∅ = ∅` gives `bktEnts ∅ = []`; take `Lr = []`; the `GA` premise is `emp`; the post's `getD ∅`
  rewrites to `∅`; `leaseEver γl []`. The extra conjuncts are dropped (affine). The `sorry` in
  `spec_of_specR` is only proof engineering.
- **The tester can use it.** `lessorW` (`Writer.lean:445`) gets everything it needs from it: `GA := True`,
  `reqOf := 3600` (from `leaseRecsOk`'s `3600 ≤ ttl`), `mono := false` (`lessorRevocable`),
  `Lr := L = recs.map (·.1)`, and the `leaseReqIs` list over `U = L`. A fresh member (`newMember` →
  `open`) is the `recs = []` case.

## Findings

### First tier

**F1. A counted resource the original never gave out: the receipt `⧖ |recs|`, sealed in `lessorInv`.**

- *Principle:* "A trusted statement never gives out a counted resource it did not take", which lists
  receipts by name. Also "In each post, name the caller that gave every counted resource".
- *Evidence:*
  - `lessorMu` holds `⧖ (GMap.size M)` (`InvLessor.lean:937`). With `M = recMap (recs.zip ls)`, the axiom
    asserts `⧖ |recs|`. The original's `M = ∅` needed only `⧖ 0`.
  - `⧖ n` means "at least `n` counted steps have been taken" (Perennial `GooseLang/Receipts.lean:1-25`).
    It gives `n < receiptBound` (`preceipt_lt`, which `Leases` uses for `sort.Sort`).
  - In the proved chain the receipt is earned: `initAndRecover.spec`'s post has `⧖ recs.length`, raised
    once per loop iteration.
  - In the axiom nothing earns it. `NewLessor` is names-only, so how many counted steps the model takes
    for the call is not established. At the server's restart the records come from a file written by an
    earlier process, so no step of this execution produced them.
  - Each recovered lease also brings fresh counted resources: a `revokeCloser` for each new `revokec`
    (`:827`), and reader slots of each new `Lease.mu`, inside `leaseOwn`'s `closerAt`. These are honest
    allocations in Go (`&Lease{…}`), but the docstring names none of them.
- *Callers affected:* every proof that reaches `lessor.Leases` or `Promote`'s sort through this lessor:
  the tester's `checkLeases` and the server after its restart.
- *Restatement:* choose one of these, and put the choice to the user.
  - (a) Keep the receipt, and say in the docstring where it comes from: Go's `initAndRecover` loop runs
    `|recs|` iterations, and its translation, proved as `lessor.initAndRecover.spec`, earns
    `⧖ recs.length`. State that the axiom claims those counted steps happen. Also name the per-lease
    resources as allocations (`make(chan struct{})`, the zero `RWMutex` of `&Lease{}`).
  - (b) Take `⧖ |recs|` in the precondition.

  I judge (a) true of the code, since the receipt is a lower bound on steps, not a share of a fixed
  stock like `threadTok`. But the step count of a names-only call is part of the trust, so I mark it
  **uncertain**, and the decision is the user's.

**F2. Two trusted statements of one function, and `etc/bounds-check.py --check` fails at HEAD because of it.**

- *Principle:* "One spec per function; special cases are instances". Also the bounds rule: a new spec
  mentions no `actualMaxReaders` or count of reader slots.
- *Evidence:*
  - `etc/bounds-check.py --check` reports `spec-readers in go_etcd_io/etcd/server/v3/lease: 2, baseline 1`
    and `stock in …/lease: 3, baseline 2`. Both new matches are `NewLessorR.lean:105`
    (`List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), lease.lessorRdOf γl`), copied from
    `NewLessor.lean:152`.
  - `mvccfull/Link.lean:586` takes `specR` as a hypothesis beside the original axiom. If `specR` becomes
    a second axiom, the trust base has two statements of `NewLessor`.
- *Callers affected:*
  - `NewServer.lean:310/2641/2784` and `etcdserver/Link.lean:2782` (the original).
  - `mvccrand/runChecks.lean:59`, `mvccrand/Link.lean:313`.
  - mvccfull's chain (`specR`).
- *Restatement:*
  - Make `specR` the only axiom (`lease.NewLessor.wp_proofR : lease.NewLessor.specR`).
  - Prove `spec_of_specR`, and derive `lease.NewLessor.wp_proof` from it, as a theorem rather than an
    axiom. `NewLessor.lean` then keeps the spec text, and its `List.replicate` is the one match left.
  - Or, better for the bounds plan, have both give the lessor's reader pool or slots through the
    owner's handle and not the count.
  - List the collections whose results now rest on the stronger claim (`etc/tcb-report.py --check`
    flags the rename, not the strengthening).
  - Until then the bounds gate fails on this branch.

### Second tier

**S1. Docstring citations are off by one or two, and the write-back argument cites the wrong mechanism.**
(Principle: "Sound: true of the code"; a trusted docstring is the argument.)
- `minLeaseTTL` is set at `lessor.go:231`, not `:233`, and `go l.runLoop()` is at `:245`, not `:246`.
- "the records change neither the lock nor the commit" is right, but the reason the first `Unlock`
  writes back is `UnsafeCreateBucket`'s unconditional `pending++` (`batch_tx.go:144`, `:329`). That
  `Unlock` can also commit (`:355`), and `ForceCommit`'s `Unlock` finds `pending = 0` because `commit`
  resets it (`:300`). Cite these.
- Say that one token is stronger than what the proved `lessor.initAndRecover.spec` gives
  (`ownToks γB.wb 2`). This is the original's known coarseness ("know the margin"), and it is unchanged
  by records.

**S2. The minimum TTL is not tied to the configuration's field.**
- `Recover`'s post gives `lF "minLeaseTTL" lp ↦□ mt` next to its snapshot. `specR` writes the
  snapshot's TTLs at `cfg.MinLeaseTTL'`, but `lessorCfg lp`'s `mt` stays existential.
- A client that relates a later `Grant`'s TTL (computed from `lessorCfg`'s `mt`) to the recovered ones
  cannot join the two.
- True of Go and cheap to add: `lF go!"minLeaseTTL" lp ↦□ cfg.MinLeaseTTL'` (`lessor.go:231`; the field
  is never written again, checked by grep). No current client needs it ("prefer the stronger spec";
  optional).

**S3. The request premise could be weaker.**
- `∀ x ∈ recs, reqOf x.1 ≤ x.2.1` mirrors `Recover`, whose minimum is unknown to the caller. Here the
  minimum is `cfg.MinLeaseTTL'`, so `reqOk` needs only `reqOf x.1 ≤ grantTTL cfg.MinLeaseTTL' x.2.1`,
  which is implied by the current premise.
- Optional ("no unneeded premise"). Keeping it parallel to `Recover` is a defensible choice; say so in
  the docstring if kept.

**S4. The `GA` premise limits the server's restart (R2d'b).**
- The premise is needed: `lessorAuth` keeps `GA` for every map lease, and `Lookup` returns `□ GA id`.
- The server's guard is `srvGrantGuard lg on = ⌜lg = true ∧ on = false⌝` (`InvApplier.lean:511`). So a
  restart whose bucket holds records is covered only in the lease-granting, auth-off mode. With auth on,
  or `lg = false`, the restart must have an empty bucket.
- That matches the server's current scope, but record it in `notes/restart-plan.md` (R2d'b) as a scope
  restriction, not as an issue of `specR`.

**S5. `spec_of_specR` is a `sorry`.**
The instance is valid (checked above), and it should be proved before `specR` replaces the axiom (F2):
otherwise the original's users gain a `sorry`.

**S6. No Go test of the trusted post with records.**
- Principle "know what it rests on", and `examples/bootok-whole.md`: check a trusted post whole against Go.
- A small test at the pin would check the decidable parts on a bucket of `Grant`-written records:
  `NewLessor` on it; the leases' ids, the raised TTLs, `remainingTTL`, `expiry` zero; the bucket bytes
  unchanged; one write-back (the read buffer's version, as `etc/spec-test/bootstrap/` measures it).
- The original cites `TestBksNewLessorIdle`, which I did not find in this worktree. **Uncertain** where
  it lives.

**S7. Scope of `leaseRecEnc`.**
The premise admits only buckets whose values are exactly `leaseEnc` (proto.Marshal of the three
fields). A bucket written by another tool, or a record with unknown fields, is outside it. Go would
decode the latter. Mark this as a scope restriction in the docstring, as `Recover`'s does.

**S8. (Inherited, not new) the loop's read lock.**
`runLoop`'s `revokeExpiredLeases` takes `le.mu.RLock()` (`lessor.go:646`) while the caller receives
`actualMaxReaders` slots of `mu`. The original argues this only for `Lookup` (the 2^30 bound); the
loop's own slot is not mentioned. It is not changed by records. Noted for the original's next review.

## Go bugs

None found. Nothing for `issues/` or `nonissues/`.

## Ranking (need of revision)

There is one target. In order:
1. F2: a gate failure at HEAD, and the one-axiom plan.
2. F1: a decision on the receipt, and naming the counted resources.
3. S1 and S5, before Freeze.
4. S2, S3, S6 and S7: optional strengthenings or checks.
5. S4: notes only.
