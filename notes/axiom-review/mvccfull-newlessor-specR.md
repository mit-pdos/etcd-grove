# Axiom review: `lease.NewLessor.specR` (mvccfull F1, restart over a populated lease bucket)

Reviewed 2026-11-10 by the `axiom` skill, worktree `mvcc-full-tester` at `d595560967`.

- Target: `lease.NewLessor.specR`, `Spec/go_etcd_io/etcd/server/v3/lease/NewLessorR.lean` (a draft
  restatement of the axiom `lease.NewLessor.wp_proof`, `Proof/.../lease/NewLessor.lean`; used by
  `examples/mvccfull`'s `runner.open`, `Link.lean`). Review round 1:
  `notes/review/mvccfull-f1-newlessor-r1.md`.
- Go: etcd at the pin `a4d2bb17` (fork `upamanyus/etcd`, branch `goose-lean`; extracted into the
  scratch dir `.lake/axiomcx-newlessor/`): `server/lease/lessor.go` (`NewLessor`/`newLessor`
  `:208-249`, `runLoop` `:620-636`, `revokeExpiredLeases` `:640-663`, `checkpointScheduledLeases`
  `:667-687`, `initAndRecover` `:808-835`), `server/storage/schema/lease.go:27-56`.
- No Lean file edited, nothing built.

## Verdict

**Survives.** I found no Go program that uses `NewLessor` as `specR` allows and panics. The receipt
`⧖ |recs|` is sound: keep it, as option (a), with a better docstring argument (below).

## The claims, and why each holds

1. **The bucket's records are read without a panic** (pre `bktEnts … = recs.map leaseRecEnc`).
   `MustUnsafeGetAllLeases` panics only if `proto.Unmarshal` fails (`schema/lease.go:33-43`). Every
   value here is `proto.Marshal` of a `leasepb.Lease`, so it decodes. The premise also ties each key
   to its record's id (8 big-endian bytes), so ids are distinct. `UnsafeCreateLeaseBucket` on an
   existing bucket does nothing to it.
2. **One lease per record, TTL raised to `cfg.MinLeaseTTL`, `remainingTTL` the record's, `expiry`
   zero, fresh `revokec`, empty item set** (`:815-830`). `minLeaseTTL` is `cfg.MinLeaseTTL`
   (`:231`) and is never written again. Checked in Go (below).
3. **The recovered ghost state** (`leaseOwn γl Lr ∅`, `leaseRevokers`, `leaseEver γl ids`,
   `□ leaseReqIs`, `lessorAt γl 0 σ`). This is word for word the proved `lessor.Recover.spec` post
   at `L = U = []`, so the invariants provably admit it. The index `0` is safe:
   - the history is freshly allocated at `[σ]`;
   - `lessorAt_empty` (the only lemma that pins index `0` to the empty snapshot) needs
     `leaseEver γl []`, and the caller gets `leaseEver γl ids` instead.
4. **The receipt `⧖ |recs|`**, inside `lessorMu`'s `⧖ (size M)`. See "The receipt question".
5. **The goroutine `runLoop` runs while the post holds.** Before `Promote` the lessor is not
   primary (`demotec` nil). So `revokeExpiredLeases` and `checkpointScheduledLeases` touch neither
   the lease map nor the leases, and `leaseOwn γl Lr ∅` (the live set) cannot be invalidated
   concurrently. After `Promote`:
   - the recovered leases are refreshed, registered with the notifier and checkpointed like
     granted ones;
   - every lease `runLoop` sends on `expiredC` is a map lease, with `□ GA id` from the new premise;
   - `lessorExpiredC` and the `Lookup` clause carry over unchanged.
6. **The reader slots** (`actualMaxReaders` × `lessorRdOf`). These are unchanged from the original.
   A client reaches `le.mu` only through methods that release it, so it cannot hold a slot across
   calls. Exhausting the slots needs `2^30` live goroutines, which is not runnable.
   - Inherited observation, not new and not exploitable through the API: `revokeExpiredLeases`
     mutates the expiry notifier under `le.mu.RLock()` (`:646-650`, `findExpiredLeases`), which a
     fractional `notifierAt` under a read lock does not describe.
   - It is safe because the readers the proved methods run (`Lookup`, `Leases`, `GetLease`) never
     read the notifier, and only `runLoop` writes it under the read lock.
   - `-race` reports nothing (below).

## Attacks tried

- **Edge records**: the bucket holds
  - id `0` with TTL `-3` and `RemainingTTL = MaxInt64`;
  - id `7` with TTL `100`;
  - id `-1` with TTL `2` and `RemainingTTL = -5`;
  - id `MaxInt64` with TTL `MaxInt64` and `RemainingTTL = 1`.

  `NewLessor` with `MinLeaseTTL = 5` and `leaseRevokeRate = 1`. Then:
  - each `Lookup` checks the id, the raised TTL, `remainingTTL` and the zero expiry;
  - the bucket is re-read unchanged;
  - `SetCheckpointer`, `Promote(0)` (refresh with overflowing `Duration`s, the notifier, the
    checkpoint heap), `Leases()` (the sort);
  - the expiry loop is drained for 3 s (3 expired leases sent), then `Demote`, `Stop`.

  Test: `.lake/axiomcx-newlessor/server/lease/axiomcx_newlessorr_test.go` (scratch, not committed).
  `GOTOOLCHAIN=go1.27.3 go test ./lease -run TestAxiomcxNewLessorRecs -count=3 -race`: PASS 3/3,
  no panic, no race report.
- **Double `Revoke` with no range deleter**: my first draft of the test panicked (close of closed
  `revokec`, `lessor.go:335/365`). This is already recorded
  (`nonissues/etcd-lease-revoke-twice-no-range-deleter.md`, `notes/axiom-review/lessor-methods.md`).
  `Revoke`'s proved spec excludes it, since it takes `mvccDeleter rd γ`. It does not involve
  `specR`.
- **Duplicate ids or a key/id mismatch**: excluded by the entries' premise (`leaseRecs_nodup`).
- **An undecodable value, or a record with unknown fields**: outside the premise, which is a scope
  restriction the docstring states. It is not a soundness gap.
- **Derive a contradiction from `lessorAt γl 0 σ` with a non-empty `σ`**: blocked, see claim 3.
- **`GA`**: every map lease needs `GA` of its id (`lessorAuth`). The premise `□ GA id` for each
  record supplies it, which is the same thing `Recover` takes as `leaseGranted`.

Not tried:
- the write-back token count (one, against the proved `initAndRecover`'s two). This margin is
  inherited and unchanged by records (r1's S1);
- a closed adequacy theorem.

## The receipt question

`⧖ n` is a persistent lower bound on the model's counted steps, and gives `n < receiptBound`
(`Receipts.lean`). It is not an exclusive stock: giving it out twice duplicates nothing. The only
way it could be unsound is if fewer than `|recs|` counted steps had run. They have, for two
reasons:

- **The translated code earns it.** `NewLessor` → `newLessor` → `initAndRecover`, and
  `initAndRecover` is translated. Its proved spec (`lessor__initAndRecover.lean`) starts from
  `preceipt_zero` and raises the receipt once per loop iteration (`wp_raise_receipt`, line 223). Its
  post has `⧖ recs.length` with no receipt in its pre. So the claim is exactly what the translation
  of the same Go code proves. The only unverified step is `newLessor`'s names-only wrapper.
- **The real Go does the work.** It loops over every record twice: in `UnsafeForEach` and in the
  recovery loop.

Option (b), the receipt in the pre, is strictly weaker for clients. It would cost the server a new
law (`recs.length ≤ logCh L` of the image) and buy no soundness.

**Recommendation: keep (a).** In the docstring:
- cite `lessor.initAndRecover.spec`'s post (proved, receipt earned per iteration) as the source;
- state that the axiom adds only `newLessor`'s wrapper.

Longer term: translating `newLessor` and proving `NewLessor` from `initAndRecover.spec` would
retire the claim entirely.

## Go bugs

None new (the double-`Revoke` panic is already in `nonissues/`).
