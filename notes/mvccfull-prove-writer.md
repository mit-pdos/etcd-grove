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

## Proved but for a gap of a frozen spec (a marked `sorry` at the gap; everything else checked)

1. **`runner.writeSub`, the put's key length.** `Txn.Put.contract` needs `|key| < 2 ^ 63 - 1`.
   writeSub's pre gives the key only as a slice (`|key| ≤ 2 ^ 63 - 1`) in `ks`, and no length bound
   on `ks` (`writerCtx` has `∀ k ∈ ks, |k| < 2 ^ 63 - 1`, but writeSub does not take `writerCtx`).
   Fix: writeSub's pre takes `⌜∀ k ∈ ks, (k.length : Int) < 2 ^ 63 - 1⌝` (its callers have it).
2. **`runner.write`, `nextLease`.** (a) `gen` needs `nextLease + 1 < 2 ^ 63`; `writerCtrs` bounds
   `nextLease` only from below (`0 ≤ nl`, `≥` every granted id), so `write.spec`'s `writerOwn` admits
   `nl = 2 ^ 63 - 1`. (b) `gen`'s post (`nl' = nl ∨ (grant ∧ id = nl + 1 ∧ nl' = nl + 1)`) admits a
   grant with `nl' = nl`, whose id `writerCtrs` cannot then bound. Fix: `writerCtrs` keeps
   `sint.Z nl ≤ |ops|` (each grant is one operation; `Run` starts at 0), and `gen`'s post says a
   grant always takes the second disjunct (`o.kind = kGrant → o.id = nl + 1 ∧ nl' = nl + 1`).

## Not proved (blocked by a frozen spec)

- **`runner.checkLeases`**: `lease.lessor.Leases.spec` needs `threadTok`, `lessorRdPool`,
  `lessorLb` and thread/receipt bound facts, none of which `checkLeases.spec`'s pre (`memCore`'s
  `lessorW` holds a reader slot, not the pool) gives; and lease has no law from `Leases()`'s post to
  the owner's live set in `leaseOwn`. Fix: the spec (or `lessorW`) carries the pool and a token;
  lease adds that law.
- **`runner.compact`**: `mvcc.api.KV.Compact.contract` gives no `ch ≠ chan.nil` in its
  ErrCompacted and success branches, which the tester checks (`compactChanOk` is met by a nil
  channel, whose receive blocks). Fix: the contract says `ch ≠ nil` there (true of mvcc: both paths
  `make` the channel). A proof modulo that fact was started (CompactLemmas).

## Modules added (the writer's own)

`EndLemmas` (commitSt's facts at mvccfull's `commitSt`), `WriterLemmas` (`incW_bndOk`,
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
