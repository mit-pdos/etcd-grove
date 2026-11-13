# mvccfull F1 Prove: the writer (2026-11-10)

The writer's proofs of stage F1's Prove (`notes/mvccfull-proof-plan.md`), against the frozen specs
(`notes/decisions.md`, "mvccfull F1's Freeze"). What is proved, the gaps of frozen specs found, the
modules added.

## Proved (no `sorry`)

- `runner.end` (the leader's snapshot check against `histW`, `appendRev`, the counter, `end()`
  through `endCb`, `KV.Rev` at `read_au`, `revLo`/`revHi` through `bnd_acc`).
- `runner.checkHook`, `runner.view`, `runner.begin`, `runner.checkAll`, `runner.shut`,
  `runner.open`, `runner.newMember` (see their commits; `open`/`newMember` add `OpenLemmas.lean`).
- Generator leaves: see the generators' commits (`gen` has one case open, below).

## Post-Freeze spec changes (tester's own specs only; approved by the coordinator, 2026-11-10)

Commit `33050af361`. Each closes a gap found in Prove; every caller still meets the new premise.

1. **`pending.del.spec` takes `ks.Pairwise go.GoStringLt`.** Cause: the spec's count filters over
   `ks`, so a repeated key counts twice while Go deletes it once (`ks = [k, k]`: Go 1, spec 2; found
   by the readers agent). Caller: `writeSub` (from `runnerKeys`). `pending.del` proved (`ca64f1d69d`).
2. **`runner.writeSub.spec` takes `∀ k ∈ ks, (k.length : Int) < 2 ^ 63 - 1`.** Cause: `Txn.Put`
   needs the put key shorter than `2 ^ 63 - 1`; the slice gives only `≤ 2 ^ 63 - 1`. Callers: `txn`,
   `apply` (from `writerCtx`'s key-length conjunct).
3. **`runner.gen.spec` assumes `1 ≤ s.rev`, and its post says a grant advances `nextLease`**
   (`if o.kind = kGrant then o.id = nl + 1 ∧ nl' = nl + 1 else nl' = nl`, for the disjunction
   `nl' = nl ∨ (grant ∧ …)`). Causes: `CompactAt`'s case 2 compacts at `s.rev`, against `opValid`'s
   positive revision when `s.rev = 0`; a grant leaving `nl' = nl` has an id `writerCtrs` cannot bound.
   Caller: `write` (`runM` starts at `hist0`, so `s.rev ≥ 1`).
4. **`writerCtrs` (in `writerOwn`) bounds `nextLease` by the log's length** (`sint.Z nl ≤ |ops|`).
   Cause: `gen` needs `nextLease + 1 < 2 ^ 63`, and `writerOwn` (in `write`'s, `restore`'s and
   `restart`'s specs) bounded it only from below. Kept by `write` (one grant per operation); `Run`
   starts at `0`, `[]`.
5. **`writerCtx` and `Run.spec`'s `runCfgOk` bound the key count, `< 2 ^ 60`** (`runCfgOk` had
   `≤ 2 ^ 62`, outside `writerCtx`). Cause: `writeSub`'s `|pend| + |ks| < 2 ^ 62`, at `txn`'s
   `|pend| ≤ |ks|`. `Main`'s configuration (120 keys) meets it.

With these, `writeSub`, `write`, `gen` and `txn` are proved without `sorry`.

**Second round (2026-11-10, the coordinator under the "minor spec fixes" rule):**

6. **mvcc's `compactChan.law`** (new API module `Spec/.../mvcc/ApiCompactChan.lean`, additive:
   `Api.lean` unchanged). Cause: `KV.Compact.contract`'s `compactChanOk` is met by a `nil` channel
   and its receive returns any value, while `runner.compact` checks `ch != nil` and takes `<-ch`'s
   `Fst`. True of the Go code: `store.Compact` returns `make(chan struct{})` in both the success
   (`compact`, `kvstore.go:235`) and the `ErrCompacted` arm (`updateCompactRev`, `:200`), `nil` only
   at `ErrFutureRev`; a receive on a `chan struct{}` is the pair. `compactChanRecv ch` is
   `compactChanOk` with `ch ≠ nil` and the pair; `compactChan.law`: at every handle, `Compact` meets
   `KV.Compact.contractC` (the contract with `compactChanRecv`). Proved
   (`Proof/.../mvcc/Api/CompactChan.lean`, a copy of `CmpCb`'s proofs with the channel's `isChan`;
   linked in `ApiCompactChanResults.lean`); `etc/api/mvcc.txt` lists the module (vocab), interface
   generated. `runner.compact` takes the law: proved.
7. **`runner.checkLeases.spec` and `runner.apply.spec` take (and give back) the caller's
   `threadTok`, and the classes `ThreadBoundLe GF (2 ^ 28)`, `ReceiptBoundLe GF (2 ^ 38)` (as `write`'s,
   `restore`'s, `open`'s specs).** Cause: `lessor.Leases.spec` (the `len(m.le.Leases())` check) takes a thread token
   (its sort borrows each lease's `expiryMu` slot) and the bounds `threadBound ≤ 2^30 - 1`,
   `receiptBound ≤ 2^62`. Callers `open`, `restore`, `write` hold one;
   `apply` lends it to `checkLeases` (its default arm).
8. **`lessorW` holds the lessor's reader pool** (`lease.lessorRdPool (mvccLeases γk)`, persistent,
   its last conjunct). Cause: `Leases.spec` borrows a reader slot from the pool, not the member's
   own slot. `open` makes it (`lessorRdPool_init`) of the `2^30 - 3` reader slots of `NewLessor`'s it
   used to drop (`threadBound ≤ 2^28`); every other proof carries it.
9. **lease's `leaseOwn_leases`** (new module `Proof/.../lease/LeaseOwnLeases.lean`, proved): the
   owner gives a lower bound `m` of the lessor's history (its last index) such that a lease map at
   an index `≥ m` (`Leases()`'s post) has exactly the live set's ids, once each.

**Invariant change (not a spec change; the coordinator, 2026-11-10):** `isInc` (`Members.lean`)
records that the incarnation's handle is a watchable store's
(`⌜∃ s, kv = interface.mkOk (PointerType watchableStore.ty) #s⌝`), which `runner.open` has from
`New`'s post (`inc_alloc` takes it). Cause: `startEpoch`'s `m.kv.NewWatchStream()` needs
`isWatchableKV`, which `shapes.law` gives only at `*watchableStore`. `EpochLemmas.inc_watchable`
proved from it.

## Not proved

- (none of `apply`: its revoke arm is proved, 2026-11-10, with `RevokeLemmas.lean`: the revoke's
  model `opPend_revoke`, `pendOk_revoke'` (it is the store's `leaseDels`, via
  `leaseDelKeys_eq_onLease`), `runM_succ_revoke`, `stMatch_length_le'` (Revoke's `≤ 2 ^ 62` from
  `ks.length < 2 ^ 60`), and `revoke_au`/`end_au`: `Revoke`'s `auBegin`/`auEnd` from the
  incarnation's `incW`, as `write_au` and `endCb_txnEnd`'s steps; no spec change.)
- `runner.compact` and `runner.checkLeases` are proved (second round of spec changes above, 6-9;
  `CompactLemmas.lean`, `CheckLeasesLemmas.lean`).

## Modules added (the writer's own)

`CheckLeasesLemmas` (`checkLeases`' model facts over `ks`), `EndLemmas` (commitSt's facts at mvccfull's `commitSt`), `WriterLemmas` (`incW_bndOk`,
`endCb_txnEnd`: `tw.End` is `end`'s callback at the incarnation's invariant; `write_au`,
`end_readT`, `pendItems_commit`, `bndOk_notify/commit`), `WriteSubLemmas` (the pending model's put
and delete at mvccfull's keys), `StepModel` (`σOf_succ_commit`: the member's state after a write is
the committed transaction's), `WriteLoopLemmas` (`logOk_snoc`, `memCore_snoc`, the `writerOwn`
accessors for the loop: `writerOwn_ops`, `_follower`, `_leader`, `_check0/1`).

## Tooling

`etc/lean-check.py`'s incremental checks reported `0 errors` on broken proofs several times (also
seen by the open/newMember agent); every commit here was checked with `lake env lean` or
`lake build`.

## Bounds

`etc/bounds-allow.txt`: the writer's `rev + 2 < 2 ^ 63` premises of `end`/`gen` (the tester's own
model counter) and `WriterShares`' lending stock are listed as owners'.
