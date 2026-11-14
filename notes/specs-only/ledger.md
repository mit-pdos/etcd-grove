# The spec plan's change ledger

A spec defect that a proof (or a review, a test, a user's critique) finds in a spec of the spec plan
(`SpecPlan/Spec/`), or a divergence between a real spec (`Spec/`) and the plan's, is recorded here
**before** either spec is edited (CLAUDE.md, "The spec plan and convergence"). The ledger is how the
plan stays the target the real proofs converge toward: no silent edits.

One entry per defect, newest first, in this format:

```
## <date>: <spec> -- <one-line defect>

- **Spec.** The file and the declaration (`SpecPlan/Spec/<pkg>/<fn>.lean`, `<fn>.spec`; or a law,
  `<pred>_<law>.spec`), and the real spec it corresponds to (`Spec/<pkg>/<fn>.lean`), if any.
- **Defect.** What is wrong: unprovable (false of the Go code), too weak for a user, too strong (a
  premise no caller can meet), not local, vacuous, ...
- **Evidence.** What shows it: the proof step that fails (file:line, the goal), the Go path (a
  panic, an error the post omits), the user or snippet (`examples/specreq/<alias>/`) it breaks, a
  failing test.
- **Proposed change.** The new statement (or its delta), and what else it moves: the snippets, the
  callers' and callees' specs and proof sketches, the open questions it touches.
- **Decision.** Pending / accepted (by whom, date; the commit that applied it) / rejected (why).
```

A change that needs the user's approval (a spec's statement at the client boundary, new
client-visible ghost state, a trust-boundary spec) says so in **Decision** and waits for it.

## 2026-11-12: `Bucket.node.spec`, `Cursor.node.spec` (internal) -- no panic promised on a deleted handle

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Bucket__node.lean`, `SpecPlan/Spec/go_etcd_io/bbolt/Cursor__node.lean`
  (internal); no real spec.
- **Defect.** Unsound: `Bucket.node` begins with `common.Assert(b.nodes != nil, ...)`
  (`bucket.go:867`), and `DeleteBucket` sets `child.nodes = nil` on the handle it deletes (`:321`).
  A deleted handle keeps its persistent `bktH` (and its cursors their `boltCur`), so the pre
  `wtxCore ∗ bktH b p` holds where Go panics; `Cursor.node` calls `c.bucket.node(...)` when the
  stack has no leaf node, with its currency `C.bkts b = some p` only as a hypothesis of its post.
- **Evidence.** The 2026-11-12 review of the bucket-handle change (`9fb353a5d1`), finding 1. No
  public triple is affected: each supplies `bktUse`, from which `wtxCore_bktOwn` gives the currency.
- **Proposed change.** `⌜C.bkts b = some p⌝` a premise of both (the cache holds the handle, so it
  is not a deleted one: `DeleteBucket` drops it from `bkts` before clearing its `nodes`); both posts
  keep `C'.bkts = C.bkts` (materializing nodes touches no bucket cache), so a caller's later calls
  keep it. Callers: `Put`, `Delete`, `CreateBucket*`, `Cursor.Delete`, `DeleteBucket` (its `seek`
  on the parent), `SetSequence`/`NextSequence` get it from their `bktUse` by `wtxCore_bktOwn`;
  `node.childAt` from a cached node's bucket; `spill`/`rebalance` walk the cached handles
  (`b.buckets`, `bucket.go:860`).
- **Decision.** Accepted by the coordinator, 2026-11-12. Applied in `c1297a6c6d`.

## 2026-11-12: bbolt's bucket handles -- a generation counter in the view is unobservable, redundant state

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Model.lean` (`TxView.gen`, `TxView.gens`, `TxView.dropBkt`), `SpecPlan/Spec/go_etcd_io/bbolt/Api.lean`
  (`bktH tx γ b p gs`, `boltCur … gs …`, `bktH_live`), and every triple taking a handle (`Tx.Bucket`,
  `Tx.CreateBucket(IfNotExists)`, `Tx.DeleteBucket`, `Tx.Cursor`, `Tx.ForEach`, `Bucket.*`,
  `Cursor.*`). Real spec: `Spec/go_etcd_io/bbolt/Api.lean` (`boltBkt tx b n g`, the same counter).
- **Defect.** A handle is valid while the per-path counters `T.gens p` equal those it was made at;
  `DeleteBucket` bumps them. No operation lets the client observe the counter: it is state in the
  client's view that exists only to invalidate stale handles, which ownership already does (using
  a bucket takes its token, deleting it consumes the token). The user, 2026-11-12: "it was
  unobservable state. It introduced a redundancy in the specs which we found was not necessary by
  instead using ownership."
- **Evidence.** What the counter excludes is real (`nonissues/bbolt-deleted-bucket-handle.md`: a
  handle used after delete and re-creation panics in `Put`), and Go has a field that says which
  handle is current: in a write transaction `Tx.Bucket`/`Bucket.Bucket` return the parent's cached
  `*Bucket` (`bucket.go:89-110`), `DeleteBucket` removes the cache entry (`bucket.go:318`),
  `CreateBucket` returns a newly allocated one (`bucket.go`, `return b.Bucket(newKey)`;
  `newBucket`, `:116`). A read transaction has no cache (`bucket.go:50`) and cannot delete.
- **Proposed change.** Write transactions: ownership of buckets, `bktOwn tx γ p o q` (fractional;
  `o : Option Loc` the parent's cache entry for `p`), the only handle predicate of a writer.
  `Begin(true)` gives `bktOwn tx γ p none 1` for every bucket path of the data; a lookup turns `o`
  into `some b` (fraction 1 to fill the cache), `CreateBucket` gives `bktOwn … (some b') 1`,
  `DeleteBucket` consumes the full tokens of the deleted bucket and every bucket below it. Read
  transactions: a persistent `bktH tx γ b p` without generations. One handle premise by cases
  (`bktUse`), so each function keeps one triple. `TxView.gen`/`gens` removed; `bktH_live` restated
  over `bktUse`. Moves no spec above bbolt (none names a handle); the real proved bbolt converges
  to it later.
- **Decision.** Accepted by the user, 2026-11-12 ("I want the ownership version"); read
  transactions keep a persistent handle (the coordinator's proposal: no Go operation can
  invalidate one, and etcd's shared read transaction caches handles across goroutines,
  `read_tx.go:49, 97-104`). Applied in `9fb353a5d1` (with the departures recorded there: `Tx`,
  `Writable`, `Cursor` and `openBucket` take only the persistent `bktH`, which they need alone and
  `bktOwn_bktH` gives from a token; the root's handle, in both kinds, is the persistent `bktH`, which
  `Tx.Cursor` returns; every cursor move, `Next`/`Prev`/`Delete` included, takes the handle premise,
  since without generations a deleted and re-created bucket can leave the view as it was; the
  lookup token is `bktTok`; the data's bucket paths `Ent.bktPaths`, `Ent.bktsUnder`).

## 2026-11-12: `Tx.DeleteBucket.spec`, `Bucket.DeleteBucket.spec` -- the empty name's error arm is false after the first leaf is emptied

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Tx__DeleteBucket.lean`, `SpecPlan/Spec/go_etcd_io/bbolt/Bucket__DeleteBucket.lean`; real spec
  `Spec/go_etcd_io/bbolt/Tx__DeleteBucket.lean` (D-M: either error, true).
- **Defect.** Unsound: `ErrIncompatibleValue` only when `kb = [] ∧ T.ents p = []`, else
  `ErrBucketNotFound`.
- **Evidence.** `c.seek("")` descends to the first leaf; a leaf node emptied by the transaction's
  deletes gives a nil key, `bytes.Equal([]byte{}, nil)`, flags 0: `ErrIncompatibleValue`
  (`bucket.go:296-305`) with buckets left. Test:
  `nonissues/bbolt-deletebucket-empty-name/emptied_leaf_test.go` (2000 buckets, first 50 deleted:
  `incompatible value`).
- **Proposed change.** For `kb = []`: either error, the transaction unchanged (the frozen spec's
  arm). No caller passes the empty name.
- **Decision.** Accepted (coordinator, 2026-11-12; a sound repair to the real spec's form).
  Applied in `9fb353a5d1` (the `kb = []` arm before the lookup: either error, the transaction
  unchanged).

## 2026-11-12: `Model.lean` -- no laws over the data model

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Model.lean` (`Ent.setKey`, `modAt`, `atPath`, `curEnts`, `bktAt`).
- **Defect.** Too weak for users: nothing states lookup after a put or delete, the cursor order
  after a put, or what `modAt` leaves at other paths; each client (the backend's range and
  compaction proofs) would re-derive them.
- **Evidence.** The 2026-11-12 strength review (etcd's server path); `examples/specreq/bbolt/
  backend.go`'s range-after-put in `ReqBackendBatch`.
- **Proposed change.** Pure laws as `def … .spec : Prop` in `Model.lean`: `atPath` after `modAt`
  (same path, other paths), `setKey` then lookup, `curEnts` of `setKey` (sorted insertion/removal),
  `wf` preserved by `setKey`/`modAt` under the entry bounds.
- **Decision.** Accepted (coordinator, 2026-11-12; adds laws, changes no triple). Applied in
  `b899a66c70` (`Ent.atPath_modAt`, `atPath_modAt_other`, `lookup_setKey`, `atPath_child_setKey`,
  `curEnts_put`, `curEnts_del`, `wf_setKey`, `wf_delKey`, `wf_modAt`, `bktPaths_mem`,
  `bktsUnder_mem`). The review of 2026-11-12 (finding 3): how `bktPaths` changes, so the backend's
  lock invariant can rebuild its token list (`Ent.bktPaths_create`, `bktPaths_dropBkt` up to
  `List.Perm`, `bktPaths_setVal`, `bktPaths_setSeq` equal), applied in `e6c84e32fd`.

## 2026-11-12: `DB.Path.spec` (and the close right) -- `Path` needs the exclusive close right, which non-blocking defrag does not hold

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/DB__Path.lean`, `SpecPlan/Spec/go_etcd_io/bbolt/Api.lean` (`boltOpened db γ`, exclusive), `DB.Sync.spec`,
  `DB.Close.spec`.
- **Defect.** Too strong a premise: etcd's defrag calls `b.db.Path()` without the backend's lock
  (`backend.go:515, 712`), so it cannot hold the exclusive right. A share is enough: `Path` reads
  `db.path`, which only `close()` writes (`db.go:832` at the pin, `db.path = ""`).
- **Evidence.** The 2026-11-12 completeness review (etcd's server).
- **Proposed change.** `boltOpened db γ q` fractional; `Path` (and `Sync`, if its Go body only
  races with `close()`) take a share and return it; `Close` takes the whole. Exclusivity at 1.
- **Decision.** Accepted (coordinator, 2026-11-12; weakens a premise, no new ghost state).
  Applied in `9fb353a5d1` (`boltOpened db γ q`, used at `1`) and `6eae035a46` (`Path` and `Sync`
  take a share: `Sync`'s body, `Logger`, `db.path` and `fdatasync`'s `db.file`, races only with
  `close()`, `db.go:829, 832` at the pin).

## 2026-11-12: `Open.spec` -- written against bbolt `743299d`, the pin is `ea4cab5`

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Open.lean`; the API's header (`743299d`).
- **Defect.** Out of date: at the pin a writable `Open` with `NoSync` off (`!db.NoSync ||
  IgnoreNoSync`) `fdatasync`s the file before any commit and, on its error, closes under the locks
  and returns it (`db.go:320-334`; `issues/bbolt-open-unsynced-meta-kill-then-power-loss.md`,
  blocks-proof: yes). The spec has neither the sync's effect on the durable state nor the error path.
- **Evidence.** `diff` of the two module versions: the only non-test change (`db.go`).
- **Proposed change.** `Open.spec` at `ea4cab5`: with `NoSync` off, the state `Open` read is durable
  (the post's state records it, as a successful sync does), the sync's error is an `Open` error
  (`boltClosed` back); the API header names the pin.
- **Decision.** Accepted (coordinator, 2026-11-12; follows the pinned code). Applied in
  `ac1de7621a`: with `NoSync` off (`IgnoreNoSync` is false on Linux) `Open` takes a sync update
  (`σ.sync ok`, as `DB.Sync.spec`'s), the success post gives `Ss true`, an error `Ss` of the outcome
  or the update back. With `NoFreelistSync` off too, the freelist commit's updates are nested in
  the sync update's `COMM` (a holder of one `boltState` builds both; the review's finding 2):
  applied in `dc5d1f1826`.

## 2026-11-12: `Open.spec`, `DB.Close.spec` -- their errors cannot be excluded, and the server panics on both

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Open.lean`, `SpecPlan/Spec/go_etcd_io/bbolt/DB__Close.lean`; the backend's `New`/`Close` specs.
- **Defect.** Too weak for the server: over OsFs every system call may fail; `newBackend` panics
  on an `Open` error (`backend.go:234-236`), `applySnapshot` on the old backend's `Close` error
  (`server.go:1149-1151`). The backend's opaque `dbOpenOk` is tied to nothing, so a proof closes
  only if it is `False`.
- **Evidence.** The 2026-11-12 completeness review; `req/go_etcd_io_bbolt.md` item 1.
- **Proposed change.** As the main tree (the user's decision for mvccrand, 2026-11-08): named
  environment premises `dbOpenOk`/`dbCloseOk`, with `Open`'s/`Close`'s error giving their negation
  (a trust-boundary layer over the proved specs); or an environment resource the call consumes.
- **Decision.** Pending: the user's (a trust-boundary statement).

## 2026-11-12: bbolt's file vocabulary -- no law for a file renamed over while open (snapshot install)

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Api.lean` (`fileHolds`, `boltFile`, `boltRelease`, `boltCrash`).
- **Defect.** Incomplete: the snapshot install renames the new file onto the open database's path
  (`storage/backend.go:68`) and closes the old database later; bbolt names a file by its path, so
  its release and crash laws would hand out the path's resources, now the new file's.
- **Evidence.** The 2026-11-12 completeness review; recorded only as the generic missing OsFs
  `rename` (C42/C43).
- **Proposed change.** Name a database by its OsFs file, not its path, or a rename law moving the
  path's name to the new file while the old file's resources stay with `boltFile γ`. With OsFs's
  `rename`.
- **Decision.** Pending (needs OsFs's `rename`; the file extension's owner).

## 2026-11-12: `backend.Defrag.spec` -- no reader slot, yet defrag opens read transactions

- **Spec.** `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Defrag.lean` (or its
  file).
- **Defect.** Unprovable: defrag's read transactions (`backend.go:597, 812, 883, 963`) each need a
  `threadTok` for `Begin(false)`; the spec takes none (`Hash` takes one).
- **Evidence.** The 2026-11-12 completeness review.
- **Proposed change.** `Defrag.spec` takes a `threadTok` and gives it back, as `Hash`.
- **Decision.** Pending (a new premise on a spec with clients: the user's).

## 2026-11-12: the backend's realization -- bbolt's state in `mu`, though commits and non-blocking defrag run without it

- **Spec.** `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/Api.lean:44` (realization
  note), `batchTx__commit.lean:4-5`, `Durable.lean:36-39`.
- **Defect.** The intended realization keeps `boltState` in the `mu` lock; batch commits and
  non-blocking defrag's `Begin` run without `mu`, and the crash law wants a share in a
  crash-surviving invariant, so the commit's update cannot be built as sketched.
- **Evidence.** The 2026-11-12 reviews (both).
- **Proposed change.** The realization keeps `boltState` in an invariant (the bank's pattern),
  the commit's update opening it.
- **Decision.** Pending (the backend's; no statement changes).

## 2026-11-13: `wal.WAL.ReadAll.spec` -- the success post `walReadCut … = some σ` is false of a Save-then-SaveSnapshot history

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__ReadAll.lean` (the W4a axiom; its proved
  replacement over `fsExt`, `notes/wal-fsext-plan.md`).
- **Defect.** Unprovable: Go's `ReadAll` folds from `Open`'s start snapshot `s` (the entries' base fixed
  at `s.Index`), while `walReadCut`'s fold moves its base only at snapshot records it has read.
- **Evidence.** `readAllFold_zero_dev` (branch `wal-fold`, `Proof/go_etcd_io/etcd/server/v3/storage/WalEncFold.lean`,
  proved): the history `Save({Term 1, Commit 5}, [entry 6 term 1])`, `SaveSnapshot({Index 5, Term 1})`;
  `Open` starts at `(5,1)`; Go's `ReadAll` succeeds with `[e6]`, `walRead I = none`. Raft does not
  produce this order (etcd saves the snapshot record before entries above it), but `Save`'s spec allows it.
- **Proposed change.** `ReadAll`'s success post states Go's fold, `walReadAt I k s` (the fold from the
  base `s`), and a lemma gives `walReadAt I k s = walReadCut I k` under a history condition the server's
  and the tester's histories meet (the condition to be found: e.g. every entry above a snapshot record's
  index is saved after it), so the clients keep `walReadCut`.
- **Decision.** Adopted (the coordinator, the user away; an intermediate spec, no client-visible ghost
  state added); the condition and the lemma on branch `wal-fold`.

## 2026-11-13: the WAL decoder's `isEofOk` -- `errors.Is` asked of `nil`, and `io.EOF` must be neither `io.ErrUnexpectedEOF` nor an `IoE` error

- **Spec.** `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/DecDefs.lean`, `isEofOk` (in `decEnv`, the
  precondition of `decoder.Decode`/`decodeRecord`; W3a of `notes/wal-fsext-plan.md`).
- **Defect.** Unprovable `decodeRecord`: (1) Go asks `errors.Is(err, io.EOF)` of `readInt64`'s error also
  when it is `nil` (decoder.go:95), which `isEofOk` did not cover; (2) with `io.EOF = io.ErrUnexpectedEOF`
  a short length word would drop the file; (3) with `IoE io.EOF` a reader may end a file early with
  `io.EOF` (`decRdErr`), and the decoder goes on in the next file, which `goDecode` does not say.
- **Evidence.** The proof of `decoder.decodeRecord` (branch `wal-dec2`): the three cases are where it stuck.
- **Proposed change.** `isEofOk` also covers `e = nil` and carries `⌜eof ≠ ueof ∧ ¬ IoE eof⌝`; all three are
  true of Go (`errors.Is(nil, t)` is `nil == t`; the two `errors.New` allocations differ; the client's `IoE`, the
  `os` file errors, are expected not to include `io.EOF`), a client obligation like the rest of `isEofOk`.
- **Decision.** Adopted (proof agent, minor: an intermediate client obligation, no ghost state).

## 2026-11-13: the WAL decoder's `proto.Unmarshal` -- a failure is not `recDecode bs = none`; the decoded record cannot be reset

- **Spec.** `LinuxFs/Spec/google_golang_org/protobuf/proto/UnmarshalWalRecord.lean` (a hypothesis of
  `decoder.decodeRecord`), `walpb.Record.Reset.spec`, `decoder.{decodeRecord,Decode}.spec` and `decPost`
  (`DecDefs.lean`), the registered `walpb.Record`'s `decC` (`PbRecord.lean`); W3a of `notes/wal-fsext-plan.md`.
- **Defect.** (1) `UnmarshalWalRecord.spec` said `Unmarshal` fails exactly when the canonical decoding
  `recDecode` does; `proto.UnmarshalPb.spec` (D1/D2) gives only "success is the canonical decoding" and
  "a valid encoding succeeds", so it was not derivable. (2) Its precondition `l ↦ zero_val` and `Reset`'s
  post, against the registration's `blank`. (3) The registered `decC` put the record's hidden fields in an
  invariant, so a decoded record could never be `Reset` (the decoder reuses `rec`) without duplicating them.
- **Evidence.** The derivation attempt (`wal-dec2`, notes W3a), and `UnmarshalPb`'s error post, which
  returns no record.
- **Proposed change.** The coordinator's decision (2026-11-13): the weaker model. `Unmarshal` may fail on
  bytes that are no record's encoding (`UFail`), a failure being a `badRec` stop of the Go decoder
  (`GoFail`, `decPost`'s third disjunct, the record not given back; `ReaderRun.fail`); success is
  `recDecode`. The spec stated over `walCodec` and `pbRecordC.data.blank`, derived from `UnmarshalPb`;
  `decodeRecord`/`Decode` take `C = walCodec`; `Reset` returns `blank`; `decEnv` gains `isPkgInit proto`;
  the registered `decC` owns the decoded record whole (trusted, pending the user's review with the
  registration).
- **Decision.** Adopted (the coordinator for the model; proof agent for the `decC` ownership, flagged for review).

## 2026-11-13: `wal.WAL.Sync.spec` -- the error arm keeps the handle, though a failed flush leaves a partial write

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Sync.lean` (the W4a axiom; its proved replacement
  over `fsExt`, `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/`, branch `wal-save`).
- **Defect.** Unprovable: `sync` flushes the encoder's page writer first; a failed flush drops the pending
  buffer after part of it reached the file, so the handle's state no longer matches the file and no
  later operation on it can be proved.
- **Evidence.** The W6 proof attempt (`notes/wal-fsext-plan.md`, W6 log); `ioutil.PageWriter.Flush.spec`'s
  error post (proved, branch `wal-enc3`).
- **Proposed change.** On error, `Sync` consumes the handle (as `Save`'s and `SaveSnapshot`'s error arms
  do, plan §3); etcd's callers stop on that error (`Fatal`).
- **Decision.** Adopted (the coordinator, the user away; an intermediate spec, every client stops there).

## 2026-11-13: `wal.WAL.SaveSnapshot.spec` -- a snapshot's index must not be below an earlier snapshot record's

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__SaveSnapshot.lean` (the W4a axiom; its proved
  replacement over `fsExt`, `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/`).
- **Defect.** `SaveSnapshot` sets `w.snapi` to the saved snapshot's index (not the maximum), and `cut` names
  the next segment after `max(w.enti, w.snapi) + 1`, which must exceed every index in the history
  (`walLastIdx`) for the segment names to stay increasing; a snapshot saved below an earlier one breaks
  it (the W6/W2 proofs, `notes/wal-fsext-plan.md`).
- **Evidence.** The handle fact `walLastIdx H ≤ max(enti, snapi)` (W2, `wal-cut7`) cannot be kept by
  `SaveSnapshot` otherwise (W6, `wal-save8`'s log).
- **Proposed change.** `SaveSnapshot.spec` takes `∀ s ∈ snapshot records of H, s.Index ≤ m.Index`. etcd
  saves the snapshots raft hands it (received, above the committed index) and its own (at the applied
  index, at least every snapshot applied before): monotone, to be checked at C6.
- **Decision.** Adopted provisionally (the coordinator, the user away); **for the user's review**: a new
  client obligation on the server (C6).

## 2026-11-13: `wal.WAL.SaveSnapshot.spec` -- the index premise above is not needed (withdrawn); the handle's snapshot bound is

- **Spec.** The previous entry (`SaveSnapshot.spec`'s proposed `∀ s ∈ snapshot records of H, s.Index ≤ m.Index`);
  `walHandleIn` (`LinuxFs/Proof/.../wal/Handle.lean`).
- **Defect.** The previous entry's defect does not hold at the pin: the translated `SaveSnapshot` (fork
  `0b50f0426`, S/wal.go:1161-1167) raises `w.snapi` and `w.enti` to the snapshot's index only when it is
  larger, so `walLastIdx (H ++ [snap m]) ≤ max(enti', snapi')` follows from the old bound with no premise.
  The real gap is elsewhere: `Save` of entries below an earlier snapshot record (`saveEntry` *sets* `w.enti`,
  S/wal.go:1086) needs `walMaxSnapIdx H ≤ snapi`, which the handle did not carry (with `enti = 120`,
  `snapi = 50`, a snapshot record of 100 read back, a `Save` of entries 60-70 would leave `walLastIdx = 100 >
  max(70, 50)`).
- **Evidence.** The W6 proofs (`wal-save9`): `walLastIdx_snap`, the Go code above.
- **Proposed change.** No premise on `SaveSnapshot`. `walHandleIn`'s index facts become `(rest = 0 →
  walLastIdx H ≤ max(enti, snapi)) ∧ walMaxSnapIdx H ≤ snapi` (internal; `saveEntry`/`saveState` take the
  `rest = 1` case as a premise, which `Save` supplies). Obligation for `ReadAll` (W3/W5) and `Create` (W4) when
  they build the handle: `walMaxSnapIdx H ≤ snapi` (`ReadAll`: every snapshot record before its first segment
  is below that segment's name index, at most the target snapshot's, which it reads; `Create`: 0).
- **Decision.** Adopted (proof agent; withdraws a provisional client obligation, so nothing for the user to
  approve; flagged in the W6 log).

## 2026-11-14: `wal.WAL.Save.spec`, `wal.WAL.SaveSnapshot.spec` -- no bound on the records' size

- **Spec.** The WAL specs over `fsExt` (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Save.lean`,
  `WAL__SaveSnapshot.lean`).
- **Defect.** The append's commit (`walTail_append`, before any record is written) must keep the
  invariant's static relation, whose `fit` says every record's encoding is below `2^56` bytes (the
  frame's 56-bit length field: `encodeFrameSize` puts the padding in the top byte, so a longer record
  corrupts its frame); the encoder's spec needs each record below `2^47` (`encode.specG`'s `recSize`,
  protobuf-go's `MarshalAppend`). Nothing bounds `Mr.encEntry e` or `Mr.encSnap md`: the part's `Save`
  dropped the main tree's `walSaveEnts sized` (whose `entSizeOk` bounded the entries), and `entIn` has no
  size.
- **Evidence.** `Append.lean`/`HandleAppend.lean` (`walHandleIn_append`'s `hfit`: `∀ c, RecsFit walCodec
  (chainRecs walCodec c (opDs Mr o.toM))`); `encoder__encodeG.lean`.
- **Proposed change.** A premise of `Save`: `∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40`, and of
  `SaveSnapshot`: `(Mr.encSnap md).length < 2 ^ 40` (the hard state's record: `walAreaOk`'s law). True of
  etcd: raft entries are bounded by the server's request size limit (`--max-request-bytes`, below
  `2^31`), snapshot metadata is a few varints and the conf state's member ids. A C6 obligation on the
  server.
- **Decision.** Adopted as a minor fix (`wal-save11`, for the coordinator's and the user's review): the two premises
  are in the part's specs.

## 2026-11-14: `wal.WAL.SaveSnapshot.spec` -- `walSnapAt` does not determine the bytes `SaveSnapshot` writes

- **Spec.** `walSnapAt sp md cs` (the WAL vocabulary, `Proof/go_etcd_io/etcd/server/v3/storage/WalDisk.lean`),
  taken by `SaveSnapshot.spec`; in the part over `fsExt`, `LinuxFs/Spec/.../wal/WAL__SaveSnapshot.lean`, whose
  history records `.snap md` written as `Mr.encSnap md` (`WalEncRecs.opDs`).
- **Defect.** `walSnapAt` fixed the index, the term and whether the conf state is nil, not the conf state's
  content nor either level's unknown fields, all of which `pbutil.MustMarshalMessage` writes; so the bytes
  of the snapshot record were not a function of `md`, and the law `MustMarshalMessage.specWalSnap` (bytes
  `Mr.encSnap md`) was false of the real marshaller. It also held the object as a whole frozen struct
  (`sp ↦□ s`), which protobuf-go's `Marshal` (it writes `sizeCache`) cannot read.
- **Evidence.** The W6 proof (`notes/wal-fsext-plan.md`, W6 log, fifth and ninth sessions);
  `MustMarshalMessageWalSnap.lean`'s former "Open" note.
- **Proposed change (made, in the part).** `walSnapAt Mr sp md cs` (`LinuxFs/Proof/.../wal/walpb/
  PbSnapshot.lean`): a frozen `walpb.Snapshot` at a wire content `c` (`snapRoC`, the registered
  `walpb.Snapshot`, hidden fields of both levels in invariants) with `c.model = md`, `Index`/`Term` set,
  `cs = c.confState.isSome`, and **`snapEnc c = Mr.encSnap md`**. `walSnapIdTerm` is over the same content
  (the getters' index and term). **New client obligation (C6):** the server's marshaller parameter `Mr`
  must give one wire form per snapshot metadata, the one of every `walpb.Snapshot` it passes. Plausible: the
  server builds each one the same way (`storage.go:62-66`, `Index`/`Term` copied from raft's metadata, the
  conf state raft's own object), so `Mr.encSnap md` is `snapEnc` of that shape provided raft's conf states
  carry no unknown fields (raft builds them; a decoded one from a peer could, which C6 must exclude or
  carry). The main tree's `walSnapAt` (the W4a axioms' vocabulary) is unchanged until the part's specs
  replace them.
- **Decision.** Adopted (the coordinator's decision, W6 ninth-session plan; the user away). **For the
  user's review** with the two trusted axioms `snapEncC_ok`, `pbSnapC_reg` (plan §10).

## 2026-11-14: the WAL's marshaller parameter `Mr` -- a bound on the hard state's encoding

- **Spec.** The WAL specs over `fsExt` (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/`), their parameter
  `Mr : WalMarshal` (the client's marshallers of entries, hard states, snapshots).
- **Defect.** `cut` writes the hard-state record into a new segment's headers and needs
  `h.md.length + (Mr.encState h.st).length < 2^42` (W2, `wal-cut9`); nothing bounds `Mr.encState`.
- **Proposed change.** A law of `Mr` (in `walAreaOk` or `WalMarshal.Ok`): `(Mr.encState hs).length < 2^32` for
  every hard state; `md` is bounded at `Create`. raft's `HardState` encodes as three varints (at most
  ~33 bytes): discharged at C6 from raftpb's encoder.
- **Decision.** Adopted (the coordinator, the user away): a client-visible law on a parameter, true of
  etcd's marshaller.
- **Made** (`wal-save11`): the law is the last conjunct of `walAreaOk` (`CreateDefs.lean`;
  `walAreaOk_encState`); the metadata's bound `h.md.length < 2^41` is a conjunct of the sealed client
  handle `walOpenWF` (`Handle.lean`), an obligation of its producers: `Create` (a premise
  `md.length < 2^41` when its spec returns `walOpenWF`) and `ReadAll` (the WAL's metadata is `Create`'s:
  needs the invariant to keep `d.metadata.length < 2^41`, established at `Create`'s commit). The cuts'
  increase (`cut.spec`'s `h.cuts.Pairwise`) is not carried by the handle: the append's commit returns it
  from the invariant's static relation (`walTail_append`).

## 2026-11-14: `wal.Create.spec` (the part's, over `fsExt`) -- its success post is the ghost-only handle

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean` (`wal.Create.spec`), success arm:
  `walOpenW w dir` (the sealed ghost handle: mode and lock token) and `osCallPerm ½`.
- **Defect.** `Save`/`SaveSnapshot`/`Sync`/`Close` (W6/W10) take the client handle `walOpenWF P Mr w dir`
  (`Handle.lean`: `w`'s fields, encoder, tail, pipeline, directory share, `walOpenW` inside), as `ReadAll`
  returns it; a WAL made by `Create` could not be appended to. The commit's out-record, the tails' authority half,
  the named entry and the metadata belong in that handle, and were dropped.
- **Evidence.** W4 log, eleventh session ("For the coordinator"); the coordinator's decision of 2026-11-14
  (task 3 of `wal-create12`).
- **Change (made).** `wal.Create.spec (P : WalPbIn GF) (Mr : WalMarshal)` over `walAreaOk walCodec Mr` (the
  handle's codec, as `Save`'s), `HeapGS HasLC.hasLC` (the handle's receipts); success arm `Q ∗ walOpenWF P Mr w dir ∗
  walNamed dir ∗ walLenLb w dir 0 ∗ walSyncedLb dir 0 ∗ walPurgeW w dir`, the call permission's half now inside the
  handle (`walDirH`). An internal refinement: no new client-visible ghost state (`walOpenWF` is the existing
  handle; it implies `walOpenW`, `walOpenWF_iff`); no client of `Create`'s part spec exists yet.
- **Decision.** Adopted (coordinator's decision; proof agent, `wal-create12`).
- **Addendum (2026-11-14, `wal-save11`'s obligation).** `Create.spec` also takes `md.length < 2 ^ 41` (a
  premise: the handle `walOpenWF` now holds `h.md.length < 2^41`); minor, the metadata etcd writes is small.
  The invariant's `d.metadata.length < 2^41` (for `ReadAll`) is to be established at `Create`'s commit
  (`walCreate_osAUnc`), not yet done.

## 2026-11-14: `wal.Exist.spec` -- the lock token, and a `false` that `fsExt` cannot exclude

- **Spec.** `wal.Exist.spec` (the main tree's W4a axiom `Spec/go_etcd_io/etcd/server/v3/storage/wal/Exist.lean`),
  restated over `fsExt` in `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Exist.lean` (W12 of
  `notes/wal-fsext-plan.md`).
- **Defects.** (1) *The token.* To read a present WAL's directory, `Exist` needs a fraction of its directory's
  claim, which `walParked` holds while no handle is open; taking it out needs the lock (`walParked_lock`,
  as `Open`'s pin). The old spec took no token. (2) *Q4 (b).* `Create`'s failure after its rename leaves a
  fresh, unnamed WAL whose directory `cleanupWAL` may have moved aside (plan §11): `false` must allow it.
  (3) *`false` on a present WAL.* `Exist` returns `false` when `ReadDir` fails with an error
  `errors.Is(_, os.ErrNotExist)` accepts. `fsExt` lets every failing system call return any errno, `ENOENT`
  included (`IsFsStep` "Open", "Readdir"), so the model has runs where `Exist` of a present, named WAL
  returns `false`: the old post (`false → o = none`) is false of the model, though true on configuration C
  (Linux's `open(2)` returns `ENOENT` only for a missing component; `getdents64` only on a removed
  directory, which a WAL directory under the area discipline is not).
- **Evidence.** `GooseLang/Ext/Fs/Impl.lean`, "Environmental failure is a nondeterministic errno"; the W12
  proof (the plan's W7-W12 log).
- **Proposed change.** (1) `Exist` takes `walUnlockedTok` (framed), as `Open` and `Create` do; its callers
  (the server's bootstrap, the tester's restart) call it with no handle open. (2) `false → o = none ∨ ∃ d,
  o = some d ∧ d.H = [] ∧ d.named = false`. (3) Kept the strong post, proved over the hypothesis
  `fileutil.ReadDir.specChildIs` (a present directory's read fails only with an error `errors.Is` does not
  take for `os.ErrNotExist`), unprovable against the current model; the model fix ("`ENOENT` only when the
  path does not resolve", for `open` and `getdents`) is the user's (trusted semantics) -- the alternative,
  a `false` that claims nothing, would leave `Create` (which needs `walAbsent`) unreachable from the
  server's bootstrap.
- **Decision.** (1), (2) adopted (minor; (2) is the coordinator's Q4 (b)). (3) **for the user**: the
  hypothesis stays until the model tightens `ENOENT` (`notes/wal-fsext-plan.md`, W7-W12 log).
## 2026-11-14: `wal.openAtIndex.spec`, `wal.Open.spec`, `wal.OpenForRead.spec` (the part's, over `fsExt`) -- the WAL directory's length and name

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/{openAtIndex,Open,OpenForRead}.lean`.
- **Defect.** `openWALFiles` (`filepath.Join(dir, name)`) and `newFilePipeline` take `dir.length < 2^61`; the
  specs bound neither `dir` nor the area `r` (the invariant records no length of a WAL's directory path).
  For an absent WAL, `selectWALFiles.specAbsent` (`os.Open` of a missing name) takes `NameOk nm`, which
  `walNameOk nm` does not give (it allows a NUL byte).
- **Evidence.** `openAtIndex`'s proof (W3/W5 log, twelfth session): the premises of `openWALFiles.spec` and
  `newFilePipeline.spec`.
- **Change (made).** The three take `dir.length < 2 ^ 59` and `NameOk nm`, as `wal.Create.spec` does (a path to
  a WAL directory is short in practice: Linux's `PATH_MAX` is 4096; etcd's name is `wal`).
- **Decision.** Adopted (minor, proof agent `wal-read12`; no client of the part's `Open` exists yet).

## 2026-11-14: `wal.Open.spec` (the part's, over `fsExt`) -- the call permission counted twice

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Open.lean` (`wal.Open.spec`), success arm:
  `walOpeningF w dir s ∗ osCallPerm ½`.
- **Defect.** The client's `osCallPerm 1` is split by `openAtIndex` in write mode: half to the file pipeline
  (`walPipeH`), half returned. `Open` returned that half to the client, but the handle `ReadAll` makes from
  `walOpeningF` (`walOpenWF`, its `walDirH`) holds a half of its own (as `Create`'s does, ledger 2026-11-14):
  after `Open` and `ReadAll` the client would hold 3/2 of the permission, and `ReadAll` could not be proved
  (nothing in `walOpeningF` supplies the handle's half).
- **Evidence.** `openAtIndex`'s proof and `ReadAll`'s obligations (W3/W5 log, twelfth session, item (a)).
- **Change (made).** `Open`'s success arm is `walOpeningF w dir s` alone; the sealed `walOpeningF`
  (`ReadDefs.lean`) holds the half (`osCallPerm ½`), which `ReadAll` moves into `walDirH`. A resource
  placement, no new client-visible ghost state; `OpenForRead` (read mode: no pipeline, the whole permission
  returned to the client) and `openAtIndex` unchanged.
- **Decision.** Adopted (the coordinator's decision of 2026-11-14, task 1 of `wal-read13`; no client of the
  part's `Open` exists yet).

## 2026-11-14: `wal.decoder.Decode.spec` (the part's, over `fsExt`) -- the error's identity

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/decoder__Decode.lean` (`decPost`, `stopErr`,
  `isEofOk` in `DecDefs.lean`).
- **Defect.** A reader looping to the end (`ReadAll`, S/wal.go:523-611) tests `errors.Is(err, io.EOF)` on the
  error `Decode` returned. (1) `stopErr`'s catch-all (`e ≠ nil`, for a bad frame, a CRC mismatch, a frame too
  large) allows `io.EOF` itself: `ReadAll` would then take a stop in the middle of the WAL for its end and succeed
  with the records after it missing, so its success post cannot be proved. (2) `isEofOk` answers `errors.Is` only
  on `nil`, `io.EOF`, `io.ErrUnexpectedEOF` and the readers' `IoE` errors, not on the decoder's own errors
  (`fmt.Errorf`'s, `proto.Unmarshal`'s), so the call cannot be stepped on them at all.
- **Evidence.** `ReadAll`'s proof (W3/W5 log, fourteenth session): the loop's exit and the write-mode stop check.
- **Change (proposed, not made).** `Decode.spec` (and `decodeRecord.spec`) add to `decPost`: `err = io.EOF` only
  at `goDecode`'s `.eof` stop, and `errors.Is(err, io.EOF)`'s answer for a non-nil `err` (`isEofAns`). Stated as
  `decoder.Decode.specR` (`decoder__DecodeR.lean`), a hypothesis of `WAL.ReadAll.wp_proof` until then. The
  proof needs Perennial's `fmt.Errorf` model to give an error distinct from `io.EOF` with `errors.Is` answering
  false on it (its wrapping is not kept) and the same of `proto.Unmarshal`'s error.
- **Decision.** Adopted (the coordinator, 2026-11-14; made by `wal-readall15`). `decPost` (`DecDefs.lean`) is now
  `decPostB ∗ decAns eof err`: the old body, and `errors.Is(err, io.EOF)`'s answer on a non-nil error
  (`isEofAns`); `stopErr`'s catch-all is `e ≠ nil ∧ e ≠ eof`, so `io.EOF` comes only from the `.eof` stop
  (the `IoE` arm excludes it by `isEofOk`). `Decode.spec`'s and `decodeRecord.spec`'s statements read the same
  (over `decPost`); `decoder.Decode.specR` is gone. The proof's new inputs: `fmt.ErrorfErrsNot.spec` (`Errorf`'s
  result is not `t` and `errors.Is(_, t)` is false on it when it is so of every error argument, `t` a package
  variable's value; a hypothesis, `LinuxFs/Spec/fmt/ErrorfErrsNot.lean`), `proto.UnmarshalWalRecordE.spec`
  (`Unmarshal`'s error is not `io.EOF`, the same answer; a hypothesis), `walpb.Record.Validate.spec` with the
  same of its error (statement change: targets `X`/`t`, premise `errIsNot ErrCRCMismatch t`), and `decEnv`
  holding `errIsNot ErrCRCMismatch io.EOF` (a client obligation, as `isEofOk`). `notes/perennial-changes.md`,
  2026-11-14, "`errors.Is` on `fmt.Errorf`'s result".

## 2026-11-14: `wal.WAL.Save.spec` (the part's, over `fsExt`) -- the batch's size, not each entry's

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Save.lean`, premise
  `∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40` (ledger 2026-11-14, "Records' size").
- **Defect.** Each entry bounded, the batch is not: the tail's stream grows by the whole batch before `Save`
  checks `SegmentSizeBytes`, and nothing then bounds the encoder's offset and pending bytes by ext4's maximum
  offset (`0xffffffff000`, `walHandleIn`'s `o0 + |out| + |pend|` bound, `Seek`'s and the writes' arithmetic):
  `saveEntry`/`saveState`/`encode.specTail` claimed it in their posts with no source (W6 log, twelfth
  session).
- **Evidence.** W6 log, thirteenth session (`wal-save13`): the bound is the stream before the call (a handle
  fact at quiescence, below) plus the batch's frames; a frame is at most its data plus 64 bytes
  (`frame_walRecEnc_tight`).
- **Change (made).** `Save` takes `walBatchBytes Mr es < 2 ^ 40` (each entry's encoding plus 64 bytes, summed;
  implies the per-entry bound). `SaveSnapshot`'s per-record premise is already its batch's. The handle fact
  (sealed `walOpenWF`, no client-visible change): the tail's stream end `o0 + |out| + |pend| < 2 ^ 43` at
  quiescence (`Save` cuts once the offset reaches `SegmentSizeBytes`, the pending bytes at most the page
  writer's buffer, 2^18; a cut's or `Create`'s headers at most the metadata, below 2^41, and the state).
  **C6 obligation**: raft bounds a `Ready`'s entries (`MaxSizePerMsg`, the uncommitted-size limit), so the
  server's batches are far below 2^40 bytes.
- **Decision.** Adopted (the coordinator's decision of 2026-11-14 for `wal-save13`, task 2), with two
  corrections to its wording found in the proof: the fact is on the stream's end, not the offset (a `Save` that
  syncs flushes its pending bytes after its `Seek`, so the next `Save` may start at `SegmentSizeBytes` plus the
  buffer), and its bound covers a cut's headers (the metadata may reach 2^41 bytes).
- **Withdrawn (2026-11-14, `wal-maxb14`).** The model now bounds every file at ext4's `s_maxbytes`
  (`fsExt`'s `maxBytes = 0xffffffff000`, a trusted semantics change pending the user's review:
  `examples/osfs/semantics/data_maxbytes.go`, measured on configuration C). A write never lands a byte at or
  past it, so the tail's written stream stays below it by the writes' success alone, and nothing needs a
  bound on the stream before the write: `Save` is back to the per-entry premise of "no bound on the records'
  size" (needed by the frame encoding, not by the offsets), the handle's stream-end fact
  (`o0 + |out| + |pend|`, in `walHandleIn` and the sealed `walOpenWF`) is gone, and so are
  `saveEntry`/`saveState`'s stream premise and `encode.specTail`'s (entry below).

## 2026-11-14: `wal.WAL.Save.spec` (the part's, over `fsExt`) -- the batch premise withdrawn: the model's file-size bound

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Save.lean` (premise
  `walBatchBytes Mr es < 2 ^ 40`); the internal `WAL__saveEntry.lean`, `WAL__saveState.lean` (premise
  `(tailStream Mr h.H h.md h.cuts).length ≤ 0xffffffff000`), `encoder__encodeTail.lean` (premise
  `o0 + |out| + |pend| + |frame| ≤ 0xffffffff000`, and the same of the result in its post); the sealed handle
  (`walHandleIn`'s `o0 + |out| + |pend| ≤ 0xffffffff000`, `walOpenWF`'s `< 2 ^ 43`).
- **Defect.** `SaveSnapshot` never cuts (S/wal.go:1137-1162), so `n` calls in a row grow the tail by `n`
  records, and no constant bound on the stream holds across them (`SaveSnapshot.wp_proof`'s `sorry`, W6 log,
  thirteenth session); the batch premise only moved the problem.
- **Evidence.** W6 log, thirteenth and fourteenth sessions; ext4's `s_maxbytes` (`ext4_max_size`,
  `generic_write_check_limits`, `inode_newsize_ok`, `vfs_fallocate`), measured on C (`TestMaxBytes`).
- **Change (made).** The model: `PWriteFinish` lands nothing at or past `maxBytes`; `FtruncateFinish`,
  `FallocFinish` land no target past it; `CrashFile`, `FsInit` sizes at most it (`OsWf.sizes`). Clients get
  it through `PwCut` (a write's landed end) and `wp_osMeta_size` (any `OsMeta`'s size, before a step). The
  WAL: `Save`'s premise back to `∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40`; the stream premises and the
  handle's stream-end fact removed (the handle keeps `o0 + |out| ≤ sz ≤ 0xffffffff000`, which the writes'
  success now gives). A client-visible weakening of `Save`'s premise; no new ghost state.
- **Decision.** Adopted provisionally (the coordinator's decision of 2026-11-14 for `wal-maxb14`), pending
  the user's review of the trusted semantics change.

## 2026-11-14: `wal.WAL.Close.spec` (the part's, over `fsExt`) -- the directory's `Close` error after everything is closed

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Close.lean` (`wal.WAL.Close.spec`, new: the
  main tree's axiom's first conjunct with plan §3's binders), post `(∃ d, Q d ∗ walSyncedLb dir |d.H| ∗
  walUnlockedTok ∗ osCallPerm 1) ∨ ⌜err ≠ nil⌝`.
- **Defect (of the main axiom).** Its success arm required `err = nil`, its error arm was `¬ walCloseOk`. The Go
  code (S/wal.go:1053-1077) returns `w.dirFile.Close()`'s error after the sync, every lock's close and the
  put-back: an error there leaves everything closed and released, so a spec giving only `err ≠ nil` would lose
  the lock token and the update's `Q` for no reason; and `¬ walCloseOk` cannot be proved from an errno (plan §6 Q6).
- **Evidence.** `WAL.Close.wp_proof` (`LinuxFs/Proof/.../wal/WAL__Close.lean`): the put-back (`WalCloseLaw`) runs
  before `dirFile.Close()`.
- **Change (made).** The success resources whatever `err` (the left disjunct does not constrain it); a failed
  sync (S/wal.go:1064-1066, returned before the locks) gives only `err ≠ nil` (the handle is lost, as `sync`'s
  error arm loses it). The main axiom's second conjunct (`Close` of an opening or failed handle) is not restated
  here: `Open`'s error arm takes `WAL.Close.specOpening` (a hypothesis), the failed handle (`walReadFailedF`) waits
  for `ReadAll`.
- **Decision.** Adopted (the W10 session, 2026-11-14; plan §6 Q6's honest error posts; no client of the part's
  `Close` yet).

## 2026-11-14: `wal.WAL.saveEntry.spec` (the part's, internal) -- no bound on the entry's encoding

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__saveEntry.lean`.
- **Defect.** `encoder.encode.specTail` (as every encode spec) needs the record's size below `2 ^ 47`
  (`recSize`, the frame's length word); `saveEntry.spec` gave no bound on `Mr.encEntry e` (the per-entry
  bound was withdrawn with the batch premise, 2026-11-14, and moved back to `Save`'s premise only).
- **Evidence.** `WAL.saveEntry.wp_proof` (W6, fifteenth session): the encode's premise.
- **Change (made).** `saveEntry.spec` takes `(Mr.encEntry e).length < 2 ^ 40` (`Save`'s premise for each of its
  entries, which `Save`'s proof passes); internal spec, no client-visible change.
- **Decision.** Adopted (minor, internal; W6 fifteenth session).
## 2026-11-14: `WalDecEnvSupply` and `decEnv`'s `isEofOk` (the part's WAL decoder, over `fsExt`) -- the readers' errors and `errors.Is`

- **Spec.** `WalDecEnvSupply` (`LinuxFs/Proof/.../wal/openAtIndex.lean`, a hypothesis of `openAtIndex.wp_proof`,
  hence of `Open`/`OpenForRead` through it) and the decoder's environment `decEnv`/`isEofOk` (`DecDefs.lean`).
- **Defect 1 (made, fixed).** The supply put every pointer error in the readers' errors `IoE`, while `isEofOk`
  needs `¬ IoE eof` and `io.EOF` is a pointer error (an `errors.New` `*errorString`, `io.eof_of_init`): the
  hypothesis proved `False` under `isPkgInit wal`, and `openAtIndex`/`Open`/`OpenForRead` were vacuous.
- **Change (made).** `IoE` holds of every `*PathError` (`∀ pe, IoE (mkOk *PathError #pe)`); `os.File.Stat.spec`'s
  error is the model's `*PathError` (was: some pointer error; its proof already knew it). Sanity check:
  `walDecEnv_eof_not` (`io`'s initialization: `io.EOF` is no `*PathError`), so the pure part `¬ IoE eof`,
  `∀ pe, IoE (PathError pe)` is met by `IoE` = the `*PathError`s.
- **Defect 2 (open, not mine to fix).** Even so the supply is not true of Go: `isEofOk` asks
  `errors.Is(e, io.EOF)` to answer `false` for every `IoE` error with no precondition, and `errors.Is` of a
  `*PathError` unwraps its `Err` field (heap), so it answers `true` for a `&PathError{Err: io.EOF}`. No pure `IoE`
  can hold of the `*PathError`s `os.File.Read`/`Stat` return (fresh allocations, `os.errnoPathErr`'s persistent
  fields) and of no other: the errors' evidence is a heap fact, and the decoder's readers pass errors through
  pure predicates only (`io.readerStream`'s `E`, `bufio.ownReader`, `decRdErr`, and the trust-boundary axiom
  `io.ReadFull.wp_proof`, `Spec/io/ReadFull.lean`).
- **Proposed change.** Carry the error's evidence with it: `io.readerStream ri S E` with `E` a persistent Iris
  predicate (`List w8 → GoInterface → IProp`), so `ReadFull`'s axiom, `bufio`, `readInt64` and the decoder pass
  it on; `decRdErr`'s I/O arm then `os.errnoPathErr e n` (`n ≠ 0`, which `Read.wp_eof`'s error arm gives with a
  small strengthening), and `isEofOk`'s I/O branch is provable from an `errors.Is` fact on `errnoPathErr`
  against an `*errorString` (as `errors.IsPathErrnoNotExist.spec`, `ExistCallees.lean`). Changing
  `io.ReadFull.wp_proof`'s statement is a trust-base change: **the user's decision**.
- **Decision.** Defect 1 fixed (2026-11-14, `wal-readall16`). Defect 2 pending the user.
## 2026-11-14: `wal.WAL.renameWAL.spec` (internal, the part's) -- the spine law cannot open the invariant

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__renameWAL.lean`, `RenameWALOk`'s third
  conjunct: `∀ x, Sp -∗ renDirOut … (some x) ={⊤}=∗ osPathS R dir dq J ∗ osPathS R dir dq J ∗ SpR x`.
- **Defect.** The caller (`Create`) can discharge it only with the invariant's post-commit split
  (`walInv_splitNew`, `CreateSplit.lean`), which opens `walInv` (needs `notCrashed`) and takes the lock token
  `walLockedTok` that the committed update's result `U (some x)` (`walCreateQ`) holds; the conjunct gives
  neither.
- **Evidence.** The W1 log, fourteenth session, "Not done" (1); `walInv_splitNew`'s statement.
- **Change (made).** The conjunct is `∀ x, Sp -∗ notCrashed -∗ U (some x) -∗ renDirOut … (some x) ={⊤}=∗
  notCrashed ∗ U (some x) ∗ osPathS R dir dq J ∗ osPathS R dir dq J ∗ SpR x`; `renameWAL` applies it at a
  program step after the rename (`wp_notCrashed_acc`). `dq` is fixed by `Create`.
- **Decision.** Adopted (the coordinator's decision, 2026-11-14, `wal-path15` task 3; internal spec, no client).

## 2026-11-14: `wal.Repair.spec` (the part's, over `fsExt`) -- the lock token taken (plan §6 Q7)

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Repair.lean` (`wal.Repair.spec`, new): the main
  tree's axiom (`Spec/go_etcd_io/etcd/server/v3/storage/wal/Repair.lean`) with plan §3's binders (`walAreaOk`, the
  area's spine and `walAreaRes`, `osCallPerm 1`, the update at `walAuMask`; `Open`'s premises, as `Repair` reads
  the same directory), and `walUnlockedTok` framed.
- **Defect (of the main axiom).** It promised that `Repair` blocks on the tail's lock while a handle holds it,
  then acts as with no handle. Over `fsExt` the file locks are bookkeeping (plan §6 Q1: no lock state), so
  `LockFile` waits for nothing and a concurrent appender would race the truncation: the axiom's statement
  without the token is not provable (and with Q1's model, not true of the model).
- **Evidence.** Plan §3 ("`Repair` takes `walUnlockedTok`") and §5/§6 Q7; both callers comply: the WAL tester
  calls `Repair` after a successful `Close` (examples/etcd/wal/wal.go:192-198), `openWALFromSnapshot` before
  any `Open`.
- **Change (made).** The token in the pre and the post (framed); the "blocks until the handle's `Close`"
  scenario dropped until the lock model. Otherwise the main tree's: committed as accessed, the boolean unconstrained.
- **Decision.** Adopted (the coordinator, plan §6 Q7, 2026-11-13; stated in the W7-W12 log's fifth session).
