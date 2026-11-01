# `storage.OpenBackend`/`OpenSnapshotBackend` with the open's records: survives (2026-10-30)

**Reviewed.**
- The axiom `storage.OpenBackend.wp_proof` (`Proof/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean`,
  its triple in `Spec/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean`, premise `openPre` in
  `InvOpen.lean`), and `storage.OpenSnapshotBackend` (not an axiom: proved over `OpenBackend`'s axiom
  and `os.Rename`'s spec, `Proof/.../storage/OpenSnapshotBackend.lean`).
- As on branch `m2-storage` at `6e838fe36f`. The axioms' texts are unchanged since
  `openbackend-post.md`, but their post `newPostK γ P W Pk K b D` now means more: `fkCl γ P D`
  (`backend/InvBackend.lean`) is `fkOwn γ (fkInit D) ∗ fkVR γ (fkWInit P D, fkInit D, fkVals D)`.
  So the post records the open (`fkOpen γ (fkInit D) (fkVals D)`, `fkCl_open`): while the client's
  half of the flag stays at its open value, every state of the backend holds `D`'s two compaction-key
  values and no buffered entry at them (`fkOkG`, `fkRd_open`).
- etcd at the pin (the fork's `249d76bea`), bbolt v1.5.0, `GOTOOLCHAIN=go1.27.3`.
- Review branch `axiom/openbackend-recs`, off `m2-storage` at `6e838fe36f`.

**Verdict: survives.** The open record is `backend.New`'s proved post: `OpenBackend`'s axiom
adds nothing to it. The record also stays true under every spec path that changes the keys. No
counterexample, no `issues/` finding. The two earlier refutations (the mmap size) are fixed by
`openMmapOk` and are not re-attacked here.

## The record is `New`'s, not the axiom's

- **Allocated from `D`.** `NewAlloc.lean:499-516` allocates `γ.fkv` at
  `(fkWInit P D, fkInit D, fkVals D)` and the batch lock's half with `fkOkG_init`, over the initial
  state `st0 D wtx` (committed data and writer's contents `D`, both buffers empty). `D` is what bbolt's
  `Open_kv` returns for `fileHolds path D`.
- **Linked, no `sorry`.** `#print axioms Perennial.EtcdGrove.backend.wp_New` (`backend/Link.lean:637`,
  `New.wp_proof wp_newBackend`) prints 424 names and no `sorryAx`. Besides Lean's three and the
  imported translations' opaque type declarations, they are:
  - bbolt's model (`fileHolds`, `ownDB`, `ownWTxG`, `Open_kv`, `Begin_kv`, `Commit_kv`, ...);
  - the backend's option-struct axioms (`optsAt*`, `wp_opts*`, `wp_mutexLit`);
  - zap's and `time`'s specs.

  `bbolt.md`'s refuted `ownWTxG_fill` is among them. It concerns `FillPercent` and gives no handle on
  the compaction keys.
- **What the axiom adds.** Only that `OpenBackend` returns what `newBackend` returns, `backend.New`
  of `bcfg`, without panicking. `openbackend-post.md` checked field by field that `openPre` maps onto
  `New`'s premise (path, batch limit, hooks, creator's step). Since the same `D` reaches `fkCl`, the
  new record inherits that mapping and asks nothing more of it.
- **Go does not inspect the keys at the open.** `OpenBackend`, `newBackend`
  (`server/storage/backend.go:32-108`) and `backend.New` never read `meta`. Only mvcc's `restore`
  parses the records. So the axiom's no-panic claim does not depend on the keys' content.

## Attacks (all fail)

1. **`fkOpen` values that differ from the file.**
   - `fkVals D` is `(dget D "meta" "finishedCompactRev", dget D "meta" "scheduledCompactRev")`,
     computed from the `fileHolds` data. A false `D` is a false `fileHolds`. That is the claim of
     whatever produced it:
     - the server's start (`bootOk`, a proved `backend.New`);
     - the transport's received image (`rafthttp/Net.lean`, `boltImage` of `snapshot.WriteTo`, whose
       `D` is the sender's bbolt committed data);
     - `os.Rename`.

     It is not this axiom's claim.
   - **Keys set:** `fkInit D = 1` and the record holds the values. Correct.
   - **`meta` absent:** `(none, none)`, `fkInit D = 0`. Correct.
   - **Values that are not revisions:** the record holds the bytes as they are and claims nothing of
     their form. The bit `fkWInit P D = decide (fkWfD P D)` is `false` on values outside `P.FV`.
   - Go agrees: `TestOpenOddValues` opens a file whose `finishedCompactRev` is `"abc"` and whose
     `scheduledCompactRev` is empty, and reads back exactly those values; `TestOpenNoMeta` reads
     both keys absent.
   - That a received image's records are 8-byte revisions (`recsVals r`, `kbRecs`) is the restore
     chain's (`restoreImageM`'s `recsOk`), not this axiom's (`m2-storage-plan.md`, item 30, D2).
2. **A stale record after writing the keys.**
   - **`UnsafePut`** of a compaction key needs `fkPut` (the client's half, `fkOwn γ f`), and
     `fkHalf_raise` gives it back at `f + 1` behind an existential. `fkRd_open` needs `fkOwn γ n` at
     the open's `n`. After a put the client holds `fkOwn γ f'` with `f' > n` (`fkOkG`'s `g.2.1 ≤ f`),
     and nothing returns the half at a given value. `fkVR` is one discarded ghost value, so there is
     no second `fkOpen` at another `n`.
   - **`UnsafeSeqPut`** has the premise `¬ fkKey bi.name kb`.
   - **The pre-commit hook** returns `batchLocked γ P b st'`, which holds `fkHalf` with `fkOkG` of
     `st'` (`InvBatch.lean:479`). A hook that writes a compaction key must therefore do it through
     `UnsafePut`'s `fkPut`, with the client's half in its `Pk`.
     - At the open (`newBatchTxBuffered`'s dummy commit runs the hook), the creator's step has no
       `fkOwn` to give.
   - **Readers** keep a lower bound taken when their state was set (`fkRd`, `fkOkRvG`). The put
     raises the flag before `Unlock`'s write-back can show the value to any reader, so a reader with
     the new value has a lower bound past `n`.
   - Go agrees (`TestPutThenRead`: the new value is read before and after the commit).
   - **Defragmentation** has no spec, so no proof can call it. Nothing proved calls `defrag`. In Go
     it copies the keys unchanged.
3. **A second open of the same path.**
   - In the model, `Open_kv` consumes `fileHolds`, and `backend.Close`'s spec does not give it back.
     So no proof reopens a path, and so no record goes stale across opens.
   - In Go, a second `OpenBackend` while the first is open blocks on bbolt's file lock: no panic
     (`TestSecondOpenBlocks`: no return within 2 s; after `Close` it returns over the same file).
   - A path spelled two ways for one file needs two `fileHolds` for the same file. That is the
     environment's or the producer's claim (`pathOwn`, the closed-world data directory).
4. **`OpenSnapshotBackend` over a received file.**
   - The rename moves `fileHolds` from the snapshot's path to the backend's (it needs `pathOwn` of
     the latter). The record is computed from the received `D`, compaction keys included once the
     leader compacts (M2).
   - The old backend keeps its inode and its own `γ`. Its record speaks of the old file, which only
     it writes.
   - On an error the file and the path come back, with no backend and no record.
5. **Deleting a compaction key or `meta` through a path the new premises miss.**
   - `batchTxBuffered.UnsafeDelete` takes `¬ fkKey bi.name kb`, and `UnsafeDeleteBucket` takes
     `∀ k, ¬ fkKey bi.name k` (which rules out `meta`).
   - The unbuffered `batchTx.UnsafeDelete`/`UnsafeDeleteBucket` specs work on `btW`, the package's
     internal resource. In Go they are shadowed by `batchTxBuffered`'s own methods
     (`batch_tx.go:418-426`) and unreachable outside the package. Their only callers are those
     wrappers, which are proved.
   - **Aliasing a bucket.** `isBucket` fixes the Go value's `Name()` to `bi.name`, and `P.has bi`
     with `P.Wf`'s distinct ids rules out a second bucket with `meta`'s name or id. So the buffers
     (by id) and bbolt (by name) cannot disagree on which bucket holds the keys.
   - **`UnsafeCreateBucket`** of an existing `meta` keeps it, in the model (`BSess.create`) and in Go
     (`CreateBucketIfNotExists`).
   - **The key set.** `fkKey`'s `"meta"`, `"scheduledCompactRev"`, `"finishedCompactRev"` are
     `schema/bucket.go:26,82-83`.
6. **Combining with other trusted statements.**
   - `backend.Snapshot`'s axiom (`snapshot.md`) commits inside but neither takes nor gives the flag.
     Its observation `Q` sees `viewAt`, `W`, `Pk`, `hkOwn` and `rbOwn`, never `fkRd`/`fkOpen`.
   - A program holding two backends (`OpenBackend` and a direct `New`) gets two `γ`s. Every law is
     per `γ`.

Not tried: the closed adequacy form; a crash between a compaction-key put and its commit (bbolt's
recovery is `fileHolds`'s claim); `RecoverSnapshotBackend` (names only, no spec).

Not a counterexample, recorded for completeness: an `UnsafePut` to a bucket bbolt lacks reaches
`lg.Fatal`, which zap's spec models as not returning. That is `os.Exit`, not a panic, and it
predates this change.

## The Go checks

`examples/axiomcx/openrecs/openrecs_test.go` (test files only, no Goose project; etcd and bbolt at
the pins of `examples/go.mod`, `GOTOOLCHAIN=go1.27.3`):

```
--- PASS: TestOpenOddValues (0.00s)
--- PASS: TestOpenNoMeta (0.00s)
--- PASS: TestPutThenRead (0.00s)
--- PASS: TestSecondOpenBlocks (2.01s)
ok  	github.com/mit-pdos/etcd-grove/examples/axiomcx/openrecs	2.021s
```

## What rests on it

Unchanged from `openbackend-post.md`: `NewServer.spec`'s snapshot path and `applySnapshot` through
`OpenSnapshotBackend`. The record's users are:
- `fkCl_open` in the restore chain's `kbRecs` (`mvcc/BackendRecs.lean`'s `rt_metaRecs`);
- `SnapApplyWalk`'s `bkNoCmp_of_fkCl`.

No restatement is proposed.
