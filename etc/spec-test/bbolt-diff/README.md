# bbolt-diff

A differential fuzzer of the real bbolt v1.5.0 against the key-value model of the bbolt axioms
(`Spec/go_etcd_io/bbolt/*_kv.lean`, over `InvBbolt.lean`), written for the axiom review
`notes/axiom-review/bbolt.md`. Where `../bbolt` (`bbolt-spec-test`) tracks every predicate
instance and transcribes each spec, this one drives one database hard: long runs, big trees,
readers kept open across many commits, and every slice bbolt returned re-checked after every step.

    go run . -runs 200 -steps 3000     # no finding expected
    go run . -plant-model              # sanity check: drops one Put from the model, must be found
    go run . -stats                    # also print each bucket's shape (depth, pages) per run

`-seed N -runs 1` replays one run. Exit status 1 on a finding (the last 15 operations are printed).

**What a run does.** It opens a new database (`InitialMmapSize` 1 GiB, so a commit never waits for
a remap while readers are open, and `NoSync`; both left free by `OptsM.ok`), begins the write
transaction, and makes `-steps` random operations, each within the axioms' premises:
`Put` (keys of 1..`MaxKeySize` bytes, values nil, empty, small, page-sized, multi-page),
`Delete` (of a present key half the time), a bulk delete of a key range (to empty leaves),
`CreateBucketIfNotExists`, `DeleteBucket` (its handles are dropped: `Put_kv` takes only a current
generation's), `Tx.Bucket`, a write `FillPercent` (`ownWTxG_fill`: NaN, ±Inf, 0, negative,
random bits, or in range), a write-cursor scan (`Seek` then up to 40 `Next`s), `Commit` and a
new writer, `Begin` of a reader (up to 4 open), a reader's scan, and `Rollback` of a reader.

**The model and the checks.** It keeps the committed data `D` and the writer's contents `S`
(bucket name → key → value), and for each reader the snapshot it began at (`rtxSnap`). It reports:

- a panic, or an error the spec excludes (`Put`, `Delete`, `CreateBucketIfNotExists`, `Begin`,
  `Commit`, `Rollback` of a reader, `DeleteBucket` of a present bucket, or not
  `ErrBucketNotFound` for an absent one);
- `Tx.Bucket` present or nil against the model;
- a cursor's `(key, value)` at each step against the model's sorted entries (`curAt` at
  `seekIdx`, then the next index; nil, nil past the end);
- a slice a cursor returned whose bytes changed while its transaction is open (`txBytes` is
  persistent; a third of the returned keys and values are kept, and all of them re-read after
  every operation; a writer's are dropped at its `Commit`, a reader's at its `Rollback`).

**What it does not reach.** Buckets stay at hundreds of keys, so the NaN `FillPercent` panic
(65538 entries in one leaf; `issues/bbolt-fillpercent-nan.md`, counterexample
`examples/axiomcx/bboltnan`) and the huge-value panics (`issues/bbolt-max-value-size-unusable.md`)
are out of its range; one database, one goroutine, no `Close` or reopen, no I/O errors.
