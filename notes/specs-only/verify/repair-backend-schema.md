# Repair: group `backend-schema` (2026-11-09)

Owned: `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/{backend,schema}/`, `SpecPlan/Spec/go_etcd_io/etcd/pkg/v3/
{traceutil,pbutil,ioutil,httputil}/`, `SpecPlan/Spec/github_com/`, `SpecPlan/Spec/golang_org/x/time/rate/`, snippets
`examples/specreq/{backend,schema,pkgleaves}`. Reports: A10-storage provability and completeness
(4a, 4b parts), A11-bbolt completeness (F1-F5 backend side, S4). Also the mvcc group's request
(A10-completeness F2), routed by the coordinator.

## Findings

### A10-provability B1 (`keyBackend_intro`'s lock rows): fixed, by a session turn

Taken neither of the reviewer's two shapes exactly; the smallest law that closes the rows is an
exclusive **turn** handed out with each session:

- `Api.lean`: new opaque `beTurn γ` (exclusive, timeless) with `beTurn_excl`, `beTurn_timeless`.
- Every `Lock*` (`batchTxBuffered.{Lock,LockInsideApply,LockOutsideApply}`, the embedded
  `batchTx.{Lock,LockInsideApply,LockOutsideApply}`) returns `beTurn γ` with the session.
- `batchTxBuffered.Unlock.spec`: the second update's atomic precondition is
  `∃∃ V, beVis γ F V ∗ beTurn γ` (the backend takes the turn back at its commit point and keeps it
  in the batch mutex's invariant until the next `Lock*`). True of the code: the second update fires
  in `Unlock` before `t.Mutex.Unlock()` (`batch_tx.go:328-361`, `batchTx.Unlock`).
- `MvccStorage.lean`'s realization: `kbData`'s parked case holds `lockTok γB ∗ beTurn γ`; at a lock
  row the new session's turn refutes it (`beTurn_excl`), so `beCur` is in `kbData`; the second
  update hands the parked turn over in the same step it puts `beCur` back. The way-back conjunct:
  `kbOpen B q := beOpen γ (q*q0) ∗ fracTok γB q`, `kbLocked` holding its `q`, so the whole
  `kbOpen B 1` excludes an outstanding `kbLocked` (inside the bridge, as the reviewer said).
- `SchemaTx.lean`: `btLockIn`/`btLockOut` give the turn, `btUnlock`'s second update takes it,
  `btSectOut` carries it in the frame.

Why not (a) parking or (b) generations + `beEnded`: parking needs the backend to hold
client-chosen state per footprint; `beEnded γ n` persistent cannot be tied to the bridge's ghost
state (nothing makes "ended" incompatible with a still-parked case unless something exclusive is
handed over at the update). The turn is exactly that exclusive thing, and needs no numbering.

### A10-provability B2 (`beCrash` at the crashed heap): fixed

`Durable.lean`: `beCrash` concludes `@beFile _ _ _ GF ⟨hG.goose_globalGS, L'⟩ p (some I)`, as
`Bbolt.boltCrash`; the stale header (heap binders "missing") rewritten: the binders landed, the I6
item-2 gap is closed.

### A10-provability B3 (`ReqDeleteVisible`): fixed

`examples/specreq/backend/parts.go`: reads through `be.ReadTx()` with `RLock`/`RUnlock` (`rdRange`'s
single key is exact); the header says why not a `ConcurrentReadTx` (the stale buffer copy,
`nonissues/etcd-backend-read-buffer-cache-stale-after-commit.md`; the reviewer cited it under
`issues/`, it is in `nonissues/`).

### A10-provability S1 (`readTx`/`baseReadTx.UnsafeRange` duplicate entry): fixed

The hook clause is waived for `es = slice.nil` instead of `e = []` (a nil end sets `limit = 1`, a
non-nil empty end does not, `read_tx.go:78-121`). Both files. Users pass `nil` for single keys
(mvcc's `rangeOk`, `SchemaTx`'s `rtRd`).

### A10-provability S3 (`ReqSeqRange`): fixed (Assumes `a < b < end`). S4 (stale names): fixed
(`leaseHookRun_intro`; "`hookRun_mvcc`" is now "the hook conversion", a conjunct of the law).

### A10-provability S5 (`writeOk` of a `*bytes.Buffer`): not fixed

Needs Perennial's `bytes.Buffer` spec to be checked against `writeOk`; no backend file can say it
without restating Perennial. Left as is (second-tier).

### A10-completeness F1 (`Snapshot`'s post too weak): fixed

- `Api.lean`: new persistent `beHistLb γ L` (the history has prefix `L`), laws `beHist_lb`,
  `beHist_lb_prefix`, `beHistLb_persistent`, `beHistLb_mono`, `beHistLb_nil`.
- `backend.Snapshot.spec` takes `beHistLb γ L0`, returns `∃ s I n L1, ⌜(L0 ++ L1).getLast? = some
  I⌝ ∗ beHistLb γ (L0 ++ L1) ∗ beCommitted γ I ∗ beSnapN γ s I n`. True: `Snapshot`'s own
  `Commit()` takes the batch lock, which waits for every commit of `L0` to finish its meta write, so
  `Begin(false)` reads `L0`'s last or a later completed commit (a later *attempted* image in the
  history is dropped from the extension, `beHistLb_mono`). The reviewer's "`I = last`" form of the
  whole current history would be false (the commit step fires before bbolt's meta write).
- New snippet `ReqSnapshotFresh` (`snapshot.go`): put, `ForceCommit`, `Snapshot`, `WriteTo` a
  buffer, write it to a file, open a backend over it, panic if the key is missing. It needs a new law
  `Durable.lean`'s `beFile_bytes` (a durable file of an image's bytes is `beFile p (some I)`;
  realization `imgBytes I bs := ∃ D, boltImage bs D ∧ imgOf D = I`, 4c's `fileHolds_image`), also
  what 2e's received-snapshot path wants; `os.WriteFile` is assumed (no OsFs spec of it here).
- S4 (the docstring/margin): the margin now says what the post leaves out.

### A10-completeness F2 (mvcc over a backend without `meta`; the mvcc group's request): fixed

`MvccStorage.lean`: `keyBackend_intro` takes `m : Bool`: `m = true` is the server's case (premise
`beMade γ metaBkt`, footprint `mvccFp`); `m = false` drops that premise and puts `meta`'s existence
cell in mvcc's footprint (`mvccFpM m := mvccFp ∪ Fp.bkt metaBkt`); `kbData B (keyDataOfM m V)` with
`metaMade := m || V.made metaBkt` (`keyDataOf V = keyDataOfM true V`, unchanged for `smImage`); the
post's `kbMade B .metaB` under `⌜m = true ∨ C.made metaBkt = true⌝`. The lent-lock conjunct, the way
back and `mvccOn_held` are over `mvccFpM m` (`mvccOn_held` existentially in `m`; the lessor's write
of `lease` is disjoint from either). Differs from the request's wording only in keeping the frozen
case's `metaMade := true` (via `m`), so the server's case is unchanged. No backend snippet added:
the mvcc group's `examples/specreq/mvcc/boot.go` `ReqBootNoMeta` covers it.

### A11-completeness F4 (`Stats` after `Begin(true)`): fixed on the backend side, needs bbolt

`backend.begin.spec`/`unsafeBegin.spec` are now one spec for both modes (`w : Bool`): `true` as
before; `false` (`batch_tx.go:405`, `unsafeCommit`'s new read transaction) under `rtHeld` with the
new write transaction `btPhys γ I 0 d` (fixing `I` as the last commit) and the caller's `threadTok`
(the read transaction's reader slot), returning `rtNew γ tx I` (new internal opaque in
`Internal.lean`). The sketch pays `db.Stats()` with `statSlot (some (tx, T))`, which for the write
transaction needs bbolt's **`statSlot_wtx`** (request below). Observed, not fixed (second-tier,
internal): the write case's pre `beCommitted γ I` does not pin `I` to the last commit; the
realization's `btHeld` does.

### A11-completeness F5 (`beSnap` fixes the bytes): fixed

`Api.lean`: opaque `beSnapN γ s I (n : Nat)` (the size only); `snapshot.WriteTo` writes some `bs`
with `imgBytes I bs ∧ bs.length = n` on each call; `snapshot.Size` returns `n`; `Close` over
`beSnapN`. `beSnap γ s I bs` stays as a transitional transparent def `:= beSnapN γ s I bs.length`,
because server-core's `ApiApply.lean:418-421` names it with `(bys : List w8)` (request below; delete
the alias once switched).

### A11-completeness F1, F2, F3 (defragmentation, backend side): fixed as named assumptions

`backend__Defrag.lean` (trusted) now names what its "why it is true" rests on in bbolt, each
requested of the bbolt group: the entry-size law on transaction data (the copy's `Put`/
`CreateBucketIfNotExists` premises; otherwise the error path is stuck on the deferred rollbacks'
order), the one-shot `openFileOk` with `Open`'s error giving the file back (`createDefragTmpDB`),
the release of a closed database's file from `boltFile` plus OsFs `rename` (`finishDefrag`,
`cleanupTmpDB`).

### A11-completeness S4 (deferred `tmptx.Rollback()` on a nil transaction): filed

`nonissues/etcd-backend-defrag-rollback-nil-tx.md` (`blocks-proof: no`): `defragdb` and also
`catchUpDefrag` (`:969-977`, `:1004`), not only the two the reviewer named
(`defragdbAndTrackLastKeys` guards it). Indexes regenerated (`etc/issues-status.py --index`).

### Not first-tier, left

- A10-completeness S3 (4b): `schema.ReadStorageVersion`, `UnsafeMigrate` have no spec (names only,
  trusted callers); O2 (`GracefulClose`, open question 3.15) stays an open decision.
- Sentinel errors (brief item 3): none of my packages' specs name a sentinel (`ioutil`'s
  `ErrShortRead`/`ErrExpectEOF` are not stated in any post); nothing to change.

## Requests to bbolt

1. `Api.lean`'s `statSlot`: accept a write transaction's whole `boltTx` (`statSlot_wtx`: one spare
   `statlock` reader slot in `isBolt` for the writer, which holds `rwlock`), for `backend.begin(true)`'s
   `db.Stats()` (`backend.go:1086-1098`, every batch commit). Add `d.Stats()` after `Begin(true)` to
   `ReqBackendBatch`. (A11 F4.)
2. A size law on the data a transaction holds (`boltTx_wf`/`boltImage_wf`, or `Ent.wf`): every key
   `≤ maxKeySize`, every entry `key.length + value.length ≤ bboltEntryMax`, recursively. Cited by
   `backend__Defrag.lean`. (A11 F1.)
3. `openFileOk` one-shot (drop `□`), and `Open`'s error disjunct giving back the lent file. Cited
   by `backend__Defrag.lean`. (A11 F2.)
4. A law releasing a closed database's file from `boltFile γ` (with `boltClosed γ`, `boltState γ 1 σ`,
   `σ.dur = some []`) as `fileHolds γ.path σ.data` or the raw OsFs resources. Cited by
   `backend__Defrag.lean`. (A11 F3.)

## Requests to server-core

1. `etcdserver/ApiApply.lean:418-421` (`beSnap`): replace `(bys : List w8)` and
   `Backend.beSnap γb s I bys` by `(n : Nat)` and `Backend.beSnapN γb s I n` (4a's snapshot now
   carries only its size, A11 F5); then tell 4a to delete the transitional `Backend.beSnap`.
2. `EtcdServer__createMergedSnapshotMessage.lean`'s sketch: after `s.KV().Commit()`, take
   `Backend.beHistLb γb L0` from the invariant's history (`beHist_lb`) and pass it to
   `backend.Snapshot.spec`; the image is the last of an extension of `L0`, so its point is `≥` the
   commit's (A10 F1).
3. `NewServer.lean`'s sketch cites `keyBackend_intro`: it now takes `m`; the server's case is
   `m = true` (with `beMade γ metaBkt`), otherwise unchanged.

## Requests to lease-auth

1. `lease/Api.lean:340-345` (`beTxHeld`'s realization text): `mvccOn_held` now gives
   `∃ m, beSess γ q' (mvccFpM m) S` and `Sess.sameOn (mvccFpM m)`; the lease bucket is disjoint from
   either footprint. Text only.
2. Auth's store over the schema's `callOk`s: `authBatchTx.Lock` now returns `Backend.beTurn γ`, and
   `Unlock`'s second update takes it back (`SchemaTx.lean`'s `btLockIn`/`btLockOut`/`btUnlock`); a
   realization that holds the lock across calls carries the turn with the session.

## Requests to mvcc

None: `ReqBootNoMeta` can cite `keyBackend_intro` at `m = false`; note the post gives `kbMade B
.metaB` only once `meta` exists (`m = true ∨ C.made metaBkt = true`), so `NewStore`'s
`UnsafeCreateBucket(Meta)` row is the `some` case there.

## New decisions

**The batch lock's turn (`beTurn`).** Every `Lock*` now returns an exclusive token that `Unlock`'s
second visible-image update takes back atomically. It is the cheapest statement of "no session
begins before the previous session's second update has fired", which a client that parks state
between sessions (mvcc's bridge) cannot otherwise derive. It changes the shape of `Unlock`'s
second atomic update for every client (each must put the turn in the update's precondition); all
current direct users are in this group's files.

**Snapshot lower bound by history prefix.** `backend.Snapshot` takes a caller-chosen prefix of the
history and returns an image that is the last of an extension of it, rather than "the last commit"
(false: the history's commit step fires before bbolt's meta write) or "some committed image" (too
weak for the merged snapshot).

## Build

`etc/specs-build.sh --dir` over all owned directories (backend, schema, traceutil, pbutil, ioutil,
httputil, rate, probing, semver/v3): **OK (219 modules)**. Snippets: `go vet ./specreq/backend/`
clean, `gofmt -l` empty for backend, schema, pkgleaves. Importers in other groups
(`etcdserver/ApiApply`, `NewServer`, `lease/Api`) could not be checked: their build stops at
`SpecPlan.Spec.go_etcd_io.etcd.client.v3.Api`, failing in client-core's work in progress at the time; the
changes they see are signature-compatible (`Backend.beSnap` kept as an alias with its old type;
`keyBackend_intro`/`mvccOn_held` are cited only in comments there).

## Second pass (coordinator's list, `second-pass.md`)

- **`AuthBackend.lean` (lease-auth's request): added.** `authFp` (the three auth buckets), the opaque
  `authImg C a` (the buckets decode to `a`; opaque until 3d states the record decodings, as
  `smRest`, with `smRest_auth` tying them), `authShare` (a fixed 1/4 share of the open token),
  `authBackendAt_intro` (from `abe ↦□ authBackend.mk (beIface b) lg`, `isBackend`, `bktsAre`, the
  share and the opener's agreeing `beCur`/`beVis` of `authFp` holding `a`), `authBackendAt_elim`
  (back, at the state last written), `authBeHook_intro` (as requested). Reader slots are not in it:
  the store's read sections take them from its own stock (`NewAuthStore`'s premise); say so if 3d's
  realization wants them inside.
- **`beCrash` and an unsynced rename (server-boot's request): done, with a recorded realization
  gap.** New exclusive `beRevert p o0` (a rename onto `p` awaits a directory sync; the previous file
  held `o0`) and `beNoRevert p`, with exclusivity laws and `beRev p rv`. `beFile_of`, `beFile_bytes`,
  `beFile_none` also give `beNoRevert p`. `beCrash` takes `beRev p rv` and concludes some `o` with
  `beFile' p o ∗ beNoRevert' p`, where `o` is a committed image in `L`, or no file with
  `Image.empty ∈ L` (bbolt's new `named = false` case), or `rv = some o` (the reverted file).
  **Request to server-boot:** `Snap.dbFile_rename` should consume the destination's
  `beFile p o0 ∗ beNoRevert p` and give `beFile p (some img) ∗ beRevert p o0`, and `SaveDBFrom`'s
  directory fsync should turn `beRevert p o0` into `beNoRevert p`. **Gap:** realizing the revert case
  needs OsFs's crash relation to bring back an unsynced rename's old entry, which neither OsFs nor
  4c's `boltCrash` states (`named = false` says only "may be gone").
- **`beSnap` alias: deleted** (grep: nothing uses it; server-core uses `beSnapN`). `Snapshot`'s
  sketch is now over `n`.
- **bbolt's items:**
  - `beFile_none` takes an absent path or an empty file with nothing past its end, as 4c's
    `boltFresh_alloc` does. `New`'s sketch starts it through `boltFresh_alloc` (`BoltSt.fresh`).
  - `boltCrash`'s new no-file case is in `beCrash`, above.
  - The `Tx.Commit` citations (`batchTx.commit`, `batchTxBuffered.Unlock`, `unsafeCommit`) now use
    the nested `commitAU` (built by `boltState_commit_au`): the commit step and the published
    updates fire in the outer update; the settling update comes when the commit ends.
  - `backend__Defrag.lean` cites `Ent.wf` (entry sizes), the one-shot `openFileOk`,
    `boltFresh_alloc` (`os.CreateTemp`) and `boltRelease`. The one remaining gap is OsFs's `rename`.
    A rename that is not yet synced is covered by `beRevert`.
  - `boltOpenOptions`: the new law `Durable.lean`'s `boltOpenOptions_init.spec`, assumed as this
    package's own `PkgInit` fact: a pointer, read-only, to `OptsM.dflt` with `mmapFlags :=
    MAP_POPULATE` (`NoFreelistSync` is not tracked by `OptsM`). `New`'s sketch cites it.
- **`Proto.norm` survival:** new law `schema_norm.spec` in `schema/Api.lean`. `leaseModel`,
  `userName` and `roleName` are unchanged by `norm`, and `alarmMemberIs` is invariant under it (all
  proto3 scalars, strings and bytes). pbutil has no relation of its own.
- **`pbutil.MustUnmarshalMessage` (rafthttp's request): done.** The post is `Proto.mergeDst t p c`
  with `Proto.encodes t c bs ∧ Proto.norm c = c`, as `Proto.Unmarshal` gives it.

Build (second pass): `etc/specs-build.sh --dir` on backend, schema and pbutil: OK (178 modules).
traceutil, ioutil, httputil, rate, probing and semver: OK (42). Importers in other groups
(`ApiApply`, `NewServer`, `OpenSnapshotBackend`, `msgAppV2Decoder.decode`, `apply/Apply`): OK (5).
`go vet` and `gofmt` are clean on `specreq/{backend,schema,pkgleaves}`.

## Last item (server-core's request for server-boot)

`backend/SchemaTx.lean` (not `schema/`, which never imports the backend's `Fp`): `confStateCells :=
Fp.key (Schema.Bkt.name .metaB) Schema.confStateKey`. `confStateSave_hook.spec` is the analogue of
cindex's `txStoredCI_sess`. It is `MustUnsafeSaveConfStateToBackend`'s triple at `btIface γ`, from a
hook session `beSess γ q Fp.none S` with `beLive γ (btLoc γ) 1`, the cell's batch part `beCur γ
confStateCells C`, `bktsAre γ` and `beMade γ meta`. It returns `beSess γ q confStateCells S'` with
`hookWrites confStateCells S S'`, with the saved bytes at the key in `S'.cur` and in the part.

Unlike cindex's law, it takes the cell's `beCur`, because the backend's `UnsafePut` needs it. So the
server's `Pk`, or the hook, must hold `beCur γ confStateCells _`, and server-boot's hook footprint is
`Fp.union Cindex.ciCells confStateCells`. The same point may apply to cindex's `txStoredCI_sess`,
which reads and writes from the session alone: server-core should check that it has a `beCur` for
`ciCells`.

Build: `etc/specs-build.sh --dir SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend`: OK (105 modules).

## Final relay (server-boot's gap (a))

`confStateSave_hook.spec` now takes the session at any footprint `F` (`beSess γ q F S`), not
only the unpublished hook session. It no longer takes `beLive`, because the save is a single
`UnsafePut`, which needs none, and `hookOk` lends the hook only the session. It returns
`beSess γ q (Fp.union F confStateCells) S'` with `hookWrites confStateCells S S'`. So it composes
after cindex's `txStoredCI_sess` (`F = ciCells`). `hookWrites` chains, so the hook's whole write is
`hookWrites (Fp.union ciCells confStateCells) S0 S''`. `hookOk` is unchanged. Build: backend dir
OK (105 modules).

## Re-review

- **A8 N3 (server-boot's request; revert state as a list): done.**
  - The opaque is now `beRevertL p (os : List (Option Image))`.
  - `beRevs p os` is the list form of the state: `[]` is `beNoRevert p`, anything else is
    `beRevertL p os`.
  - `beRevert_excl` and `beRevert_noRevert` are now over `beRevertL`.
  - `beCrash` takes `beRevs p os` and its revert case is `o ∈ os`: any previous file may come back,
    since a journaling file system keeps a prefix of the unsynced renames.
  - The header says the rename turns `beRevs p os` into `beRevs p (o0 :: os)`, and the directory
    fsync gives back `beNoRevert`.
  - `beRevert p o := beRevertL p [o]` and `beRev p rv := beRevs p rv.toList` stay as transitional
    defs. They keep server-boot's `snap/Api.lean` (`revertSt`) and rafthttp's `saveOk` building
    unchanged. Server-boot can now set `revertSt p os := Backend.beRevs p os`, and rafthttp can move
    to `beRevs`; after that the two defs can be deleted.
- **A10 re-review N1: fixed.** `MvccStorage.lean`'s realization text is now stated at `Fm`/`keyDataOfM m`:
  - `kbRead`;
  - the `KeyData.mid`/`fin` identities;
  - the `Unlock`, puts' `writable` and `ConcurrentReadTx` rows.

  There is also a one-line note before the rows. The law's statement is unchanged.
- **N2: fixed.** `backend__begin.lean` now cites 4c's `statSlot_wtx.spec` (it exists) in place of
  the "requested" text.
- **N3: fixed.** `ReqSnapshotFresh` now writes the snapshot through `writeDurable`, which does
  `O_CREATE|O_EXCL`, `Write`, `Sync`, `Close`, then fsyncs the directory; that is what
  `beFile_bytes`' premise needs (named, clean, `lo = hi = size`). The file and directory syncs
  over OsFs are assumed, as stated in `Assumes:`. The snippet now reopens through `openBackend`
  (`DefaultBackendConfig.spec`, `New.spec`) instead of `NewDefaultBackend`, so no new spec is
  needed. The snippet takes the directory as an extra argument.
- **N4: fixed.** `confStateSave_hook`'s docstring now has a margin line: the saved bytes are
  existential, not stated to be `c`'s JSON encoding.

Build: backend dir OK (105 modules). Importers OK (4 modules): `snap/Api`, `rafthttp/Api`,
`EtcdServer__applySnapshot`, `bootstrap`. `go vet` and `gofmt` are clean on `specreq/backend`.
