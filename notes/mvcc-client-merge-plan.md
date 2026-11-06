# Merging the mvcc API into `lean`: the clients' plan (2026-11-06, branch `mvcc-api`)

The user (2026-11-06): reprove every client of mvcc over the new API, adjusting a client's spec only
when it exposes an mvcc internal that changed (a badly written spec is reproved as it is, for now);
find the highest-risk packages first; settle the specs, then prove. Then: **merge into `lean` as soon
as possible.**

## The situation

- mvcc's API is proved on this branch (`notes/mvcc-api-invariants.md`, "Hand-off: M4, the mvcc API
  proved"); its clients were partly migrated (`notes/mvcc-migration/*.md`), the build beyond mvcc is
  red.
- The branch forked from `lean` at `5eea04e0d6` (2026-11-03). `lean` has since moved 2003 commits
  (6353 files), **including mvcc's own internals and old specs**: F2's compaction tracking (`CmpTrack`,
  `CmpCut`, `CmpJob`, `CmpVocab`, `kbTie*`, `backend.Snapshot` over `pvHalf`/`ckHalf`), R-D1's
  one-shot `Close` (`store.Close`/`watchableStore.Close` give back the job's budget and the loops'
  readers, `ReaderRetire`), lease-expiry's `lease.rdAt`, errorf-wrap's `ctxErrorf`, revoke-open's
  `rdStockN` cut (`authRdN`), bbolt-v2 and the backend's stop (R2b-3c/3d: `backend.Close` with
  `commitReq`, `bStopView`, `bFile`), and the examples moved (`examples/{etcd,k8s,lib}/`).
- The Go code is the same: `Code/.../storage/mvcc.lean` differs only by the translator's constant
  inlining (`NoLease` → `#(W64 0)`, ...), local repairs in mvcc's proofs.
- `git merge-tree HEAD origin/lean`: about 200 conflicting files (40 in mvcc, 80 in etcdserver and
  apply, the backend's specs, txn, lease, client/v3, notes); more of `lean`'s files merge silently as
  `lean`'s text and then fail against this branch's mvcc (`InvRestart`, `NewServer`, `InvBoot`,
  `StopShutdown`, `StopImage`, `CindexBackend`, `BuildLemmas`, `InvOpen`, `OpenBackend`, ...).

**Hence the order: merge `lean` first, then migrate the clients as they are on `lean`.** Migrating
this branch's 3-day-old copies of the clients and then merging would do the work twice.

## Risk: where a client may force a change to the API

Four read-only investigations (2026-11-06), each against `lean`'s clients and the API's text.

1. **Shutdown (certain; decided 2026-11-06, the user: option (A), reader tokens; `notes/decisions.md`, "mvcc's API: the store's readers as client-held tokens").** `lean`'s server rebuilds the backend's whole open
   token `bOpen γB 1` for `backend.Close` by a census of every store reader (`NewServer`'s error path
   after `Transport.Start` fails, `NewServer.lean:1137-1185`; `EtcdServer.Cleanup.spec`'s `wsCloseRes
   st γ ={⊤}=∗ bOpen d.γB 1`, built by `StopShutdown.lean`'s `stop_census`; restart's `bFile`/`fileHolds`).
   R-D1 made this honest (the old `#Hclose` triple was false: a second `close(stopc)` panics), and
   since R2c-4 every server result goes through `run`'s single proof via `Cleanup`. The API's
   `KV.Close.contract` posts `True` (the user, 2026-11-03: shutdown out of scope), and the store's
   readers live in a persistent thread pool inside `isMvcc` (`Api/RdSupply.lean`) that nothing drains.
   Returning `storageRest B` from `Close` is unsound (an in-flight read may hold a share:
   `issues/etcd-read-after-backend-close-panic.md`). Options:
   - **(A) The readers as client-held tokens** (recommended): `New`/`NewStore` post `mvccReaderN`
     copies of `mvccReader γ` (a share of the storage's reader slots); the contracts that read take one
     where they take a `threadTok` today, and give it back; `KV.Close.contract` gives back what `Close`
     regains (the loops' readers after `wg.Wait`, the job's after `sched.Stop`, the open token's); a law
     `mvccClosed γ B ∗ [∗] mvccReaderN readers ⊢ storageRest B`. Sound without a lock in `Close`: only
     readers no one uses can be counted. Every reading contract's precondition changes (a token in
     place of a `threadTok`), so every client proof that reads changes; mechanical. It is `lean`'s model
     (the server owns its readers), so `lean`'s census carries over.
   - (B) Keep the API's `Close`, and give up `lean`'s honest error path and shutdown: `NewServer`'s
     error path back to an assumed close, `Cleanup` without the backend's token, restart's `bFile`
     lost. Loses closed results; not a merge.
2. **errorf-wrap (certain, small, already decided on `lean`).** `rangeOutcome`'s error disjunct is
   `mvcc.ctxErrorf` (a wrap chain to a context error) on `lean`; the API's `rangeOutcomeC` is defined
   through it, so `KV.Range`/`Txn.Range` change, and the API's results rest on `fmt.ErrorfWrap.spec`
   (+1 axiom in mvcc's collection, already in `lean`'s trust base). Adopt `lean`'s.
3. **F2 vs this branch's compaction tracking (medium; no API change expected).** Same idea, different
   ghosts: `lean`'s `pvHalf`/`ckHalf` (a resource at every non-hook write) vs this branch's
   `viewAtD`/`dlsOwn`/`fkdOwn` (a premise at safe-range puts, a resource at safe-range deletes).
   Equivalent at the server's parameters. Keep this branch's (the API's snapshot laws are built on
   it); delete `lean`'s F2 mvcc modules (they redeclare `CutDefs`' names: `Bucket`, `KvEnt`,
   `entsCutAt`, `recsOk`, ...); port `lean`'s non-F2 backend work onto this branch's backend
   (bbolt-v2, `InvStop`'s `bStopView` redefined over `fkdOwn`/`dlsOwn`/`viewAtD`, `commitReq`, `RdPool`'s
   `authRdN`); `EtcdBackend.lean` to `isStopChans γ P W Pk b` and `lean`'s `newPostKP`.
4. **The lessor's deleter (low; no API change).** `lean`'s `lease.rdAt γl st` (the deleter at any
   names) fixed `kvWriter_open` handing out the store's names existentially; the API's
   `mvccDeleter rd γ` is keyed on `γ : MvccName` alone, which `KV.Restore` keeps. Drop `rdAt`;
   after `lessor.Recover` the snapshot walk rebuilds `mvccDeleter` for the new closure (an additive
   law `mvccDeleter_of_write` over `KV.Write.contract`, or inline). `lessorBackend`'s give-back of
   `le.b`'s half was fixed two ways (`lean`'s `Ln` parameter, this branch's lens in `R`): take
   `lean`'s, re-plumb the server.
5. **Restart (low for the merge).** `lean`'s `NewStore` also starts from an empty bucket
   (`kbView kb γb 1 ∅`, `idxFresh`); no `lean` proof reopens mvcc over a non-empty history yet. When
   R2d's successor does, the API needs `New` over `mvccStorageFor B Pk L c u` at any `(L, c, u)`
   (the store's `restore()` is already proved for `Restore`): later, not for this merge.
6. **`examples/k8s/compactor/KeyHist`** (low-medium): `oneChangePerKey` of `mvcc.CompactNoDup`;
   from `reach_logWf.law` if `LogWf'` gives it, else a pure vocabulary lemma.
7. Re-plumbing only (low): v3compactor (`revLb` over `srvApi.kvLogLb`, `errVars.law`), the auth
   example (SyncModel's pure lemmas into a vocabulary module), txnlin, schedule (an unused import),
   `lessor.initAndRecover` (an import), `txn/KeyObs` (this branch's, `writerPin_keyObs` users to
   `mvccImage_snapshot.law`), `InvRequest` (large textual merge; `idxCert` → `kvLogLb`, `certOk` →
   `srvLogCert`), revoke-open's `rdStockN` (536870783 now: re-check `mvccReaderN`'s arithmetic, and
   `threadBound ≤ mvccReaderN`).

Packages by risk of an API change: the server's stop and boot (1) ≫ txn/v3rpc's Range errors (2) >
backend bridge (3) > lease (4) > compactor examples (6) > the rest (7).

## The plan

**Status (2026-11-06).** M0 and M1 done (merge `5bb0d2ba97`; per-track reports `notes/mvcc-merge/`); mvcc builds without `sorry`; txn, lease, auth repaired (R1, `notes/mvcc-merge/r1.md`); next: the reader tokens in mvcc's API, then the apply chain, the server, v3rpc, client/v3, the examples.

**M0. Set aside what is not this work** (done first): the tracing cluster and `mvccrand`'s
`runChecks` drafts left uncommitted in the worktree by stopped agents, committed to
`wip/mvcc-api-stray` (not merged).

**M1. Merge `origin/lean`** (one commit, red build allowed inside the branch):
- mvcc: this branch's side for every conflict; `lean`'s F2 modules deleted; `lean`'s non-F2 mvcc
  changes (R-D1's `ReaderRetire` and `Close` posts, `ctxErrorf`, `authRdN`) reapplied as part of M3.
- backend: per risk 3's recipe (this branch's `Snapshot` and puts; `lean`'s `Close`, `New` minus
  `pvckInit`, `CommitAndStop`, bbolt-v2).
- clients (etcdserver, apply, txn, lease, v3rpc, client/v3, auth, examples): `lean`'s text where
  `lean` changed what this branch did not touch; where both changed, `lean`'s text with this branch's
  mvcc-facing restatement re-applied (the hand-offs in `notes/mvcc-migration/` list each one).
- notes: both sides' entries kept (the STATUS header: one copy of each entry).

**M2. Settle the specs.** The API changes (risk 1's choice, risk 2) and every client spec that
names an mvcc internal, each restated over the API; `spec-reviewer` on the changed API statements;
the user's approval of the `Close` change. No client spec changes otherwise.

**M3. Prove, by risk**: mvcc itself (the merged internals, the API changes, `ApiResults`);
backend + bridge; txn; lease; the server's KV invariant, apply chain, snapshot send/receive, boot
(`NewServer`), stop (`StopShutdown`, `Cleanup`); v3rpc; client/v3; examples (`lib/etcdstart`,
then `etcd/*`, `k8s/*`); the tester (`examples/mvccrand`). Parallel tracks, one `lake build` at a time.

**M4. Gates**: `lake build` green; `etc/gates.sh` (links regenerated, `etc/tcb-report.py --check`:
only the intended axiom changes, then `--update`, and every collection's; interfaces; `api-check`;
`bounds-check`; `goose.py --check`); closed theorems' text unchanged against `lean` except the
approved changes (list them); then the merge into `lean` by its workflow.
