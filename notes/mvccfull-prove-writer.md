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

## Not proved (blocked by a frozen spec)

- **`runner.checkLeases`**: `lease.lessor.Leases.spec` needs `threadTok`, `lessorRdPool`,
  `lessorLb` and thread/receipt bound facts, none of which `checkLeases.spec`'s pre (`memCore`'s
  `lessorW` holds a reader slot, not the pool) gives; and lease has no law from `Leases()`'s post to
  the owner's live set in `leaseOwn`. Fix: the spec (or `lessorW`) carries the pool and a token;
  lease adds that law.
- **`runner.compact`: proved but for four `sorry`s, two gaps of the frozen mvcc API** (each in the
  ErrCompacted and the success branch; `7700669085`, `CompactLemmas.lean`): (1) `KV.Compact.contract`
  gives no `ch ≠ chan.nil`, which the tester checks (`compactChanOk` is met by a nil channel, whose
  receive blocks); (2) `compactChanOk`'s receive returns an arbitrary value, and the code's `<-ch`
  takes its `Fst`. Fix (mvcc's API, the user's): `ch ≠ nil` in both branches, and the receive's
  result a pair. Everything else proved (`compact_au`, the bounds, the hook, the history).

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
