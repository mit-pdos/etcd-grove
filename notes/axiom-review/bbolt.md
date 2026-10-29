# Axiom review: bbolt's key-value axioms (2026-10-29)

**Reviewed** (`origin/lean` `58fc8512e7`; bbolt v1.5.0, go1.27.3, amd64): the 20 triples
`Spec/go_etcd_io/bbolt/*_kv.lean` (axioms in `Proof/go_etcd_io/bbolt/`), the predicate model they
are written in (`Proof/go_etcd_io/etcd/server/v3/storage/backend/InvBbolt.lean`: `ownDB`,
`txLive`, `txBytes`, `txBytes_acc`, `ownWTxG`, `ownWTxG_fill`, `wBkt`, `ownCur`, ...), the `Options`
rules (`BboltOptions.lean`, `BboltOptsDefs.lean`: `optsAt`, `OptsM.ok`, `wp_optsLit`,
`wp_optsAlloc`, ...), and the three package-initializer axioms (`Proof/go_etcd_io/bbolt/Init.lean`,
`internal/common/Initialize.lean`, `errors/Init.lean`). Method: `.claude/skills/axiom`.

## Verdict: refuted, twice

### 1. `ownWTxG_fill` (with `Tx.Commit_kv`): a NaN `FillPercent` — counterexample proved

**The claim.** `ownWTxG_fill` gives a write transaction's bucket handle's `FillPercent` field
and takes it back with *any* value (`∀ f' : w64, ... ↦ f' -∗ ownWTxG ...`); `Tx.Commit_kv`
returns (an error at worst, never a panic).

**Why it is false.** `node.splitTwo` (bbolt `node.go`) clamps `FillPercent` with `<` and `>`,
both false for NaN; `int(float64(pageSize) * NaN)` is `MinInt64` on amd64, which `splitIndex`
compares as the `uintptr` `2^63`, so a leaf of `N` entries is split only into `N-3` and `3`, and
`node.write` panics on a page of `0xFFFF` entries or more (`issues/bbolt-fillpercent-nan.md`).

**The counterexample**:

- Go: `examples/axiomcx/bboltnan/bboltnan.go`, `Run(path)`: `Open` (`&bolt.Options{}`),
  `Begin(true)`, `CreateBucketIfNotExists("b")`, `b.FillPercent = z / z` (`z := 0.0`), 70000
  `Put`s of three-byte keys with empty values, `Commit`. Its test:
  `cd examples && GOTOOLCHAIN=go1.27.3 go test ./axiomcx/bboltnan/` —
  `Run panicked: inode overflow: 69997 (pgid=4)` (0.14 s, deterministic).
- Translation: project `axiomcx-bboltnan` of `etc/goose.py`,
  `Code/.../examples/axiomcx/bboltnan.lean`.
- Proof: `Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/bboltnan/Run.lean`.
  `Run.wp_proof` proves `{{ isPkgInit bboltnan ∗ fileHolds path ∅ }} Run #path {{ RET #(); True }}`
  from the five specs it calls (`Open_kv`, `DB.Begin_kv`, `Tx.CreateBucketIfNotExists_kv`,
  `Bucket.Put_kv`, `Tx.Commit_kv`, as hypotheses); `Run.wp_axioms` instantiates them with the
  axioms. No `sorry`. `#print axioms Run.wp_axioms`: Lean's three; the five `*.wp_proof` axioms;
  bbolt's predicate model (`ownDB`, `wrTok`, `isDB`, `txLive`, `txDB`, `txDone`, `ownWTxG`,
  `ownWTxG_fill`, `wBkt`, `rtxSnap`, `rtxStats`, `fileHolds`, `boltLogger`, the persistence
  instances); the `Options` rules (`optsAt`, `optsVal`, `wp_optsLit`, `wp_optsAlloc`); and the
  type declarations of untranslated types (`fmt.pp`, `sync.Map`, `DB.underlying`, ...), which
  carry no behaviour. The proof also takes the generated `Assumptions` classes of bbolt and of
  the counterexample package, as every proof here does. The NaN itself is not used: the wand
  accepts any `f'`, and the proof never looks at the value.
- `fileHolds path ∅` is the counterexample's premise, as it is the closed theorems' (a new file);
  the closed adequacy form (`putget_safe`'s) was not done.

**Reach.** The backend's only use (`batchTx__unsafePut.lean`) writes `0.9`, so no result proves
anything false of etcd through this; but every result that rests on `ownWTxG_fill` rests on a
false axiom. (`etc/tcb-report.py --roots` was not run: it needs a current full build.)

**Proposed restatement** (not applied): take the field back only with a value that is not a NaN,
`∀ f', ⌜¬ float64IsNaN f'⌝ → ...` (a NaN is an exponent of all ones with a non-zero mantissa);
every other value is clamped into `[0.1, 1.0]`. The backend's `0.9` discharges it by computation.

### 2. `Bucket.Put_kv` (with `Tx.Commit_kv`, `Cursor.Seek_kv`/`Next_kv`): values `Put` accepts but bbolt cannot store

**The claim.** `Put_kv` returns `nil` for any value of at most `MaxValueSize` (`2^31 - 2`)
bytes and the entry is in the transaction's contents; `Commit_kv` does not panic; cursors return
the committed entries.

**Why it is false.** Already reproduced in `issues/`, by the bbolt proof's spill (branch
`bbolt`), on 2026-10-19/23, after `notes/audit.md` judged `Put_kv` ok (2026-10-18); nobody had
connected them to these axioms:

- `issues/bbolt-max-value-size-unusable.md`: `Put(key, value)` with `len(value) = MaxValueSize`
  and a key of 2 bytes or more: `Commit` panics (`slice bounds out of range [::2147483648]`);
  with a 1-byte key the commit succeeds and every read of the entry panics.
- `issues/bbolt-large-values-leaf-unreadable.md`: two values of `MaxAllocSize/2` bytes commit to
  one page and `Get`/cursor reads of the second panic.

Both are counterexamples of the same shape as `Run` (no `FillPercent` step), but their Go
reproductions need several GB of memory, so neither was re-run nor given a Lean proof here.

**Proposed restatement** (not applied; it moves the backend's spec): `Put_kv` premises
`kb.length + vb.length ≤ 2^28`, the bound the bbolt proof's spill assumes (`SpillFit.lean`,
with the default page size). The backend's `unsafePut` would then need the bound from its callers:
etcd's request limit (`MaxRequestBytes`, 1.5 MiB by default) is far below it, but no spec carries
it to the backend today. A decision for the user.

## Survives: what was tried

Each attack below was read against bbolt v1.5.0's code and, where it can run, tested:

- **Mutating a value after `Put`** (bbolt keeps the caller's value slice): `Put_kv` takes
  `value ↦*□`, read-only for good.
- **Keeping a returned slice past its transaction** (mmap memory, unmapped at remap or `Close`):
  `txBytes_acc` needs `txLive`; persisting the access spends a fraction of `txLive`, after which
  `Rollback`/`Commit` (which need all of it) cannot run, so the map is never released; Go blocks
  (`Close`, remap), which a WP allows. The fraction `dq` is the axiom's, so no proof writes to
  the (read-only) map.
- **`txBytes` stability while the transaction is live**, across the writer's `Put`/`Delete`/
  `DeleteBucket`/`CreateBucketIfNotExists` and other transactions' commits with freed-page reuse:
  `node.put`/`del` replace slice headers, never bytes; pages a reader can see stay pending.
  Tested: the differential fuzzer `etc/spec-test/bbolt-diff` (its `README.md`; every
  retained slice re-checked after every step, readers kept open across commits with
  `InitialMmapSize` 1 GiB, buckets to depth 3 with overflow pages, keys up to `MaxKeySize`, nil
  and empty values, bulk deletes emptying leaves, `FillPercent` set to NaN, ±Inf, 0, negative and
  random bits): 24000 runs of 10000 steps, nothing (its trees never reach the 65538 entries the
  NaN panic needs). A model bug planted in it is found at once (`-plant-model`).
- **Write cursors over leaves emptied by `Delete`**, stale branch keys: `Cursor.next` skips
  empty pages; stale keys only move where the search starts. Fuzzed as above.
- **`Close` racing transactions**: `Close` takes `rwlock`, `metalock`, `mmaplock`, so it waits for
  every transaction; `Stats` (never-nil `db.stats`), `Info` (needs a live transaction), `Begin`
  (`!db.opened`), `removeTx` (`db.freelist != nil`) are guarded after it.
- **Read transactions used from several goroutines** (`txLive` is fractional): read-only
  cursors write no shared state; `rtxStats` serializes `Bucket`/`Cursor`.
- **Key order**: `GoStringLt` compares bytes unsigned, as `bytes.Compare`.
- **`Open`'s options**: `OptsM.ok` constrains `ReadOnly`, `PageSize`, `OpenFile` only; the
  others (`MmapFlags`, `Mlock`, `MaxSize`, `FreelistType`, `Timeout`, `InitialMmapSize`, ...) end
  in errors, which `Open_kv`/`Commit_kv` allow.
- **A fresh `*Tx` aliasing an old one** (`Begin_kv` does not say fresh): unusable, a proof cannot
  show the equality, and Go keeps the old pointer alive.
- **`Commit` errors** (`issues/bbolt-commit-meta-error-frees-reader-pages.md` frees a reader's
  pages): `Commit_kv`'s error branch gives back neither `ownDB` nor `wrTok`, so no later writer
  exists in the model to reuse them.
- **Package initializers** (`opaqueInitsOk`, `errorsNewVarsInit`): reachable only through Go's
  one-time package initialization; the messages match `bbolt/errors`.

**Not tried:** the closed adequacy form of the counterexample; Lean counterexamples for the two
`issues/` findings; `etc/tcb-report.py`'s list of the results resting on the refuted axioms;
crash and I/O-error behaviour beyond `Commit`'s error branch; 32-bit platforms
(`issues/bbolt-txstats-unaligned-32bit.md`; the model is 64-bit).
