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
