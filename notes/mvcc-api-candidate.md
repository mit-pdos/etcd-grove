# mvcc's API: candidate specs (2026-11-01, branch `worktree-mvcc-rand-tester`)

The user asked for new candidate specs of etcd's mvcc package, written in the Lean spec files,
designed with the `spec` skill, good enough for etcd's proof and for the randomized tester
(`examples/mvccrand`, `notes/mvccrand.md`). **Status: candidates for review.** They typecheck;
nothing proves them, and no proof uses them; today's specs and proofs are untouched.

- The vocabulary: `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean` (new).
- The specs: `<F>.specC`, appended to each function's spec file next to today's `<F>.spec`
  (43 functions, mvcc's client-facing API: `New`, `NewStore`, `store.Read`/`Write`/`Rev`/
  `Commit`/`Compact`/`Close`/`Restore`/`HashStorage`, `watchableStore.Write`/`Close`/`Restore`/
  `NewWatchStream`, `readView.Range`/`Rev`/`FirstRev`, `writeView.Put`/`DeleteRange`,
  `metricsTxnWrite.Range`/`Put`/`DeleteRange`/`Rev`/`FirstRev`/`Changes`/`End`,
  `watchableStoreTxnWrite.End`, `NewReadOnlyTxnWrite`, `txnReadWrite.Range`/`Rev`/`Changes`/`End`,
  `watchStream.Watch`/`Chan`/`Rev`/`RequestProgress`/`RequestProgressAll`/`Cancel`/`Close`,
  `hashStorage.Store`/`HashByRev`/`Hash`/`Hashes`; the last three in new spec files of their own).
  Side by side rather than in place so that the build stays green while they are reviewed:
  adopting them replaces each `<F>.spec` (and its proof).
- Rounds: 1 (`8bd75f7cc2`), 2 (`3f39b7e79d`), 3 (`a4cc4f33b8`), 4 (`e8bad5269e`), each after a
  `spec-reviewer` review of the previous; 5 (below), after the user's critique.
- Out of scope: mvcc's internal functions (the key index, the tree index, the revision encoding,
  the compaction job, the sync loops): the `spec` skill's scope, an internal spec may mirror its
  code.

## The design

Today's specs are written in the implementation's terms: reader slots (`storeReaderC`), revision
tokens (`ownToks γ.revs`), the index's certificates (`idxCert`, `crevLb`), the caller's
certificate map (`certOk`, `certOkNext`), the writer's fragments (`writerFrag`, `watchWriter`,
`logQ`), the reader's tag `Z`, the internal ghost names (`StoreNames`, `WsNames`, `WatchParams`).
A client reasons about the log it read through a floor (its certificate), an upper bound (the
tokens) and the pin these give the sole writer (`txn/SoleWriter.lean`).

The candidates follow the reviewed examples (`.claude/skills/spec/examples/put.md`, `range.md`):
the API's abstract state, owned by the client, and linearizability as the caller's atomic update.

- **The state** `mvccState γ σ`, `σ : MvccState = {log, crev}`: mvcc's own history (every
  revision's changes, `stateAt σ.log r` the state at `r`; compacted revisions stay in the model
  and read as `ErrCompacted`) and the compaction revision. The server's `KVState` (base store at
  the compaction revision, later changes) is a function of it.
- **Reads** (`Read`, `Rev`, `Watch`'s registration) fire the caller's update at the state they
  read, unchanged. A reader that knows a revision was written (it is in its invariant's state)
  reads at least it: the floor is the state, not a certificate.
- **A write transaction** (`Write` ... `End`) is pinned to the state `σ` it began at
  (`mvccTxn_write_agree`: it holds the batch lock and `s.mu`, so no write and no compaction can
  change the state before its `End`); its operations extend its pending changes `pend`; `End`
  commits them by the caller's update (`σ' ↦ σ'.commit pend`). The sole writer's exactness is the
  law, not a token budget.
- **Watches**: the watchable store sends a revision's events before it bumps the revision (a read
  that starts after an event was received may still see the revision before it). So reads stay
  exact, linearized at the bump, and watch events may be ahead by the revision being committed:
  they come from a log the client **announced** (`mvccAnn γ r L`, the client's own map from a
  revision to a log; `watchableStoreTxnWrite.End` takes the announcement of the log it commits),
  so the client relates them to its records. Laws: the events received for a watcher are its
  range's events, filtered, of the revisions `[lo, hi)` of an announced log (`wsRecv_events`); a
  progress response (per watcher, or `-1` for the watchers registered before it was sent and not
  cancelled) comes after every event up to its revision (`wsRecv_progress`); each response's
  revision is at or above its events' (`wsRecv_resp`). The registration (`Watch`) fires the
  caller's update, so a watcher from revision `0` knows its first revision (`σ.rev + 1`).
- **The lessor**: any implementation meeting the store's need (`isMvccLessor le γl R`: the four
  triples of today's `isLessor`, over any interface value; `R` the real lessor's reader slot).
- **Resources**: the caller's `threadTok` (lent to a transaction until its `End`) instead of
  reader slots; no write token: `New` takes the receipt-paid write-back supply once.
- **Hook**: the batch lock's invariant `P` and the post-lock hook `f`, frozen on the backend
  (`mvccHook γ P f`; `nil` allowed: `hookRun` is then the caller's update); `Write` runs it from
  the caller's `Pre` to `Q`, `End` takes `P` back.

## Round 2 (the review of round 1)

The reviewer found four statements false of the Go code; all repaired:

- `metricsTxnWrite.FirstRev`: a write transaction's is `0` (`store.Write` sets none), not the
  compaction revision.
- `metricsTxnWrite.Changes`: it returned the change records' points-tos, which a second call
  duplicates and which the watchable store's `End` writes; now only their number (what etcd's
  `txn` and the tester inspect).
- **A commit that skips the watchers**: round 1 gave a committing `End` to the store's own write
  transactions (`store.Write`, `metricsTxnWrite.End`), so a client of the watchable store could
  commit a revision no watcher sees, falsifying the watch laws. Now the store's own `Write` has no
  candidate spec and `metricsTxnWrite.End` ends read transactions only: every write goes through
  `watchableStore.Write`/`watchableStoreTxnWrite.End`.
- `Compact` after `Close` panics (the stopped scheduler's `Schedule`): the store's open token
  (`mvccOpen γ q`, fractional) replaces the closer; `Compact` takes a share, `Close` the whole.

And the gaps for callers: `Commit` and `Compact` take the backend's commit request
(`mvccCommitReq`, from `backend.commitReq` by `mvccCommitReq_of`, with `mvccBackendIs` from
`New`); `Watch` no longer takes a share of the stream's open token (v3rpc closes the stream while
its receive loop may still register: the closed stream's arm, `wsClosed`); a live token per
watcher (`wsLive`, taken by `Cancel` when the caller has it) makes the progress law say something
(round 1's `wsCanceled` could be read as `True`); the registrar's view of the watchers
(`wsWatchers`, for "a response of a watcher the client registered"); specs of
`txnReadWrite.Changes` and `watchStream.Rev`; laws for the trace while a transaction is open
(`mvccTxn_trace`), the receive in Perennial's `recvAu` form (a plain receive or a `select`), the
range deleter's triple (`mvccDeleter_spec`), every response's revision (`wsRecv_rev`), a compaction
response's positive revision, `mvccAnn` and `mvccHook` agreement; the reachability law states the
length bound, not the receipts. `Put`'s key bound found: it is the lessor's `Attach`'s (each item's
key shorter than `2 ^ 63 - 1`, which round 1's `isMvccLessor` had dropped: restored), so `Put` takes
it only with a lease.

Not repaired (open, below): `New`'s backend internals (E1); the field laws rather than WP-transfer
laws for the promoted methods (E2: they are enough to call the methods, and no longer reach an
unsound path); the module not sealed (E4); `isMvccLessor`'s generality nominal (E6); `Revoke`'s
write of the lease bucket inside the transaction (B7, the lease package's spec); whether v3rpc's
send loop needs registration facts beyond `wsWatcher`'s `k` (B6, unchecked).

## Round 3 (the review of round 2)

Every round-1 finding in scope repaired, but round 2's `Cancel` without the live token (`!own`)
took nothing, so a goroutine could cancel a watcher whose live token another kept, and the next
stream-wide progress response falsified the progress law. Now `!own` takes a proof that the id is
not live: an id the registrar's view does not have (ids are never reused) or one already
cancelled. Two docstrings corrected: `Watch` does not clamp a negative start revision (it replays
the history, or answers with a compaction response at `-1`: the premise `0 ≤ startRev` is needed;
mvcc's documentation says otherwise: `issues/etcd-mvcc-watch-negative-start-rev.md`, found by the
review, reproduced); `Attach`'s key bound is the real lessor's proof's invariant (`itemKeysShort`),
not a need of its Go code.

## Round 4 (the review of round 3)

Round 3's `Cancel` was sound but merged the caller's two cases in its post, so a caller that lent
its registrar's view could get back only `wsCanceled` and lose the view (v3rpc's receive loop then
could not register again). `Cancel` now takes the caller's case (`CancelBy`: `live`, `unknown`,
`dead`), each with its own post. Not reviewed again (a split of an arm the review checked).

## Round 5 (the user: every function of the API, `store.Write` included)

The user's critique of round 2: removing `store.Write`'s candidate because one candidate was
unsound left the function without a spec; an unsound candidate means a better one is needed
(now a principle of the `spec` skill, "An unsound candidate is replaced by a sound one, not
dropped"). Round 5 states every function of mvcc's client-facing API (the `KV`, `WatchableKV`,
`TxnRead`/`TxnWrite`, `WatchStream` and `HashStorage` interfaces, the constructors); the internal
helpers (the key index, the tree index, the revision encoding) keep today's specs (the skill's
scope: an internal spec may mirror its code).

- **`store.Write`** is back, on any store. What was unsound was the commit, not the opening: the
  write transaction's own `End` (`metricsTxnWrite.End`, both kinds again) takes `mvccNotified γ σ
  pend` ("the watchers were notified of this commit, or the store has none"), free for a store
  without watchers (`mvccNotified_unwatched`, the store's mode `mvccWatched γ`, fixed at its
  creation) and made for a watched store only by the watchable store's `End`, which notifies. One
  spec of `End`, true in both modes.
- **The announcement is inside the commit's update** (`watchableStoreTxnWrite.End`, the views):
  the update's atomic precondition gives, with the state, the announcement of the log after the
  commit, which the store reads when it notifies (opening the update and closing it unchanged).
  So a caller that does not know the state beforehand (the store's own `Put` and `DeleteRange`) can
  commit on a watched store; a sole writer still announces beforehand and gives it.
- **New candidates**: `NewStore` (the mode `wq` its caller chooses; with watchers, the right to
  wrap it, `mvccWrapRight`), `store.Close` (the whole open token), the store's views
  (`readView.Range`/`Rev`/`FirstRev`, `writeView.Put`/`DeleteRange`: a transaction each, through
  the watchable store when the store has watchers, `isMvcc_views`), `store.Restore` and
  `watchableStore.Restore` (the whole open token: `Restore` stops and replaces the scheduler a
  concurrent `Compact` reads after releasing `s.mu`; the new state from the backend,
  `mvccRestorable`; on a watched store it extends the history and is announced; the leases
  re-attached), `store.HashStorage`, `hashStorage.Store`/`HashByRev`/`Hash`/`Hashes` (a hash of
  the store, `mvccHashOk`, is of the revisions `(CompactRevision, Revision]` of its history,
  `mvccHashOf`; `Store` takes one, so `HashByRev`'s stored results are too; `Hash`'s result is not
  stated: the backend's pages and an unsynchronized read).
- Found: `issues/etcd-mvcc-hash-currentrev-race.md` (`store.hash` reads `currentRev` without
  `revMu`; the race detector reports it against every write).

Open after round 5: the backend's identity is fixed in the vocabulary (`mvccBackend`,
`mvccBackendIs`, the hook), but `Restore` replaces the backend; `mvccRestorable` stands for the new
backend's creator's resources; `mvccHashOf` stands for crc32 over the kept revisions (its proof
needs the `kvHasher` axioms to say the hash is a function of its input); the backend's `Hash` has
no spec.

## Round 6 (the review of round 5)

The design held (`mvccNotified` and the announcement inside the update are true of the code in
both modes); four new statements were false, repaired:

- `HashByRev` concurrent with `Restore`: its stored-hash path reads the current revision under
  `revMu` alone, which `Restore` sets to `1` for a while; it now takes a share of the open token
  (`Restore` takes it whole). Go behaviour: `issues/etcd-mvcc-hashbyrev-restore-rev1.md`
  (reproduced).
- `HashByRev(0)` may return a hash stored for revision `0` (a compaction at `0`), not the current
  revision's: the post says either. Go behaviour: `issues/etcd-mvcc-hashbyrev-zero-stored.md`
  (reproduced).
- `Restore` (both): the history extended and the compaction revision not lowered, in both modes
  (the stored hashes survive a restore: `mvccHashOk_state`; the watchers' compaction responses:
  `wsRecv_compact`); the announcement only with watchers.

And: the views law for a store without watchers, and for a watchable store's store through the
watchable store (`NewStore` at the watched mode leaves the fields to `mvccWrapRight`, which the
watchable store overwrites); `Restore` bounds the re-attached keys (`Attach`'s premise);
`mvccRestorable_reachable`; `mvccNotified_nil` (a commit of nothing); `Hash` is not provable while
its read races (the candidate holds once the issue's fix is in, or a trust-boundary axiom until
then). Open (noted): a compaction the new backend left unfinished is resumed by `restore`, with no
contract for its hook and commit yet (the backend boundary).

## Round 7 (the review of round 6)

Round 6's repairs sound, no new defect. Two laws added: `mvccHashOf_prefix` (a hash depends only
on the history up to its revision, which `mvccHashOk_state` needs of whatever defines
`mvccHashOf`), and the restored state's length bound in `mvccRestorable_reachable`. The review
showed `HashByRev`'s open-token share cuts three of etcd's callers off from concurrent restores:
decision 10 below. Not reviewed again (two laws and a docstring).

## Decisions for the user (new client-owned ghost state and premises)

The skill's policy: each new premise or client-owned ghost state on a spec with clients is the
user's decision. Today's statement beside the candidate's:

1. **The client owns the store's abstract state** (`mvccState γ σ`, from `New`). Today: the
   caller's certificates and tokens (`idxCert γ.idx log`, `ownToks γ.revs m`, `certOk γ log`)
   bound the log it reads. Alternative: keep today's, and add the abstract state as a layer above
   (which the certificate style cannot express without the implementation's ghost names).
2. **The client's announcements** (`mvccAnnAuth γ M`, `mvccAnn γ r L`; `watchableStoreTxnWrite.End`
   takes `⌜pend = []⌝ ∨ mvccAnn γ σ.log.length (σ.log ++ [pend])`). Today: the caller's certificate
   map (`ghostMapAuth γ.cok`, `certOkNext γ.st ilog pend`), the same mechanism under internal names.
   Alternative: commit at the notification (the state then runs ahead of the revision reads see,
   and reads must answer from a past state, `range.md`'s form); the candidate keeps reads exact.
3. **`New`'s premise `threadBound GF ≤ 2 ^ 30`** (the store's readers are the threads; Go's
   `RWMutex` allows `2 ^ 30` readers). Today: reader slots, one per reader, handed out by `New`. The
   examples' closed theorems take `n + 2 ≤ 2 ^ 31`: they would need `n + 2 ≤ 2 ^ 30`.
4. **`New`'s premise `□ (⧗ 1 ={⊤}=∗ backend.wbTok d.γB)`** (write-backs paid from time receipts,
   M2's `kbWTSupply`, given by the backend's creator). Today: two write tokens to `NewStore`, then
   one per `Write` (`storeWT`) and `Commit`. Alternative: keep the per-call token.
5. **The lessor's contract over any interface value** (`isMvccLessor`, with its resource `R`).
   Today: `isLessor` (the real `*lessor` only). The real lessor meets it with
   `R := lease.lessorRd lp γl`; the generality is nominal while the owner's predicate is the real
   lessor's `lease.leaseOwn` (a `FakeLessor` would need its own: open).
6. **The stream's registrar's view and a live token per watcher** (`wsWatchers ι S` from
   `NewWatchStream`, threaded through `Watch`; `wsLive ι id` from `Watch`, taken by `Cancel`, or
   in its place a proof that the id is not live).
   Today: the stream's id map and per-id tokens (`idsInv`, `idTok`), internal names.
7. **The store's open token** (`mvccOpen γ q`: `Compact` a share, `Close` and `Restore` the whole).
   Today: the closer (`storeCloser`, `wsCloser`) and the compaction right (`compactRight`).
8. **`hashStorage.Store`'s premise** `mvccHashOk γ h` (only hashes of the store are stored).
   Today: `Store` takes nothing (`hashStorageOk`), and no spec says what `HashByRev` returns.
   Alternative: no premise, and `HashByRev` promises a hash of the store only when none was stored
   for the revision.
9. **`Restore`'s atomic precondition**: the new state extends the history and keeps the
   compaction revision (both modes), and on a watched store is announced. Today:
   `store.Restore.spec` (D22) takes the server's snapshot machinery.
10. **`HashByRev` excludes a concurrent `Restore`** (a share of the open token, which `Restore`
    takes whole), because the Go code returns current revision `1` during a restore
    (`issues/etcd-mvcc-hashbyrev-restore-rev1.md`). Consequence for etcd's server: its periodic
    corruption check (`corrupt.go:180, 193`), its peers' `/members/hashkv` handler (`:550`) and the
    maintenance `HashKV` (`maintenance.go:243`) cannot hold a share while `applySnapshot` restores,
    so until the Go code is fixed its proof has restores or concurrent hash checks, not both.
    Alternative: no share, and `HashByRev`'s current revision stated only as "a revision the store
    had, or `1`" (a weaker spec true of today's code).

Dropped premises (each today's, none needed by the code under the candidate's ownership): the
reader tags `Z` (always `True`), `crevLb` floors, `NoDelPutAt` (already gone in M2 on `lean`),
`L.length + 4 ≤ 2 ^ 63` (a law: every state's changes are fewer than the receipts),
`writerFrag`/`writerOwn` on `Commit`, the compaction right (`Compact` is linearizable under
`s.mu`; concurrent compactions are serialized by it).

## Complete for etcd and for the tester (the argument; not proved)

- **The sole writer** (etcd's apply thread, the tester's writer) holds `mvccState` in its
  invariant; the agreement law gives it the state each write transaction began at, exactly (today:
  `pinned_sole`). Its reads (`Txn`'s compare) see that state.
- **A linearizable read** (etcd's request goroutines, the tester's readers): the client's
  invariant ties `mvccState`'s revision to what it published (etcd: the applied index the read
  index waited for; the tester: the writer's published revision); the read's update fires at the
  current state, whose revision is at least it (today: `store.Read`'s `log₀ <+: log`).
- **The read's revision is in the client's records**: the update fires at the state the client's
  invariant holds, so it is the client's (today: `certOk` and the client's map).
- **Watches** (etcd's `v3rpc` watch server, the tester's watch stream): events from announced logs
  (the client announces its own pending log before `End`: etcd's server already does, with
  `certOkNext`), progress per watcher and for the stream (the tester's checks), the registration's
  first revision (etcd's clients watch from `0`).
- **Leases**: puts with a lease keep the item map (as today); `Revoke` (the lease package's spec,
  not changed here) would take the announcement of its exact deletions (the keys the item map puts
  on the lease, sorted), which its caller can compute, in place of today's `∀ pend,
  certOkNext γ log pend` (unsatisfiable for a caller that uses its map: `notes/mvccrand.md`).

## Open

- **The backend boundary is unchanged**: `New` takes what today's `NewStore_backend` takes of the
  real backend (`isBackend` at `lateW`, `keySized`, `bkView`, `bkNoCmp`, `lateReg`, `bkRTx`), which
  names implementation ghost state (`lateW` registers the store's names); a design of its own.
- **Compaction over the real backend**: `Compact.specC` is stated unconditionally (true of the
  Go code); proving it needs M2's backend compaction model (`KBReal.cm`).
- **The watch id `0`** (`AutoWatchID`) on `Watch`: a scope restriction (etcd's client never
  chooses one); a caller's id adds the `ErrWatcherDuplicateID` arm.
- **Compaction responses** (`WResp.compactRev ≠ 0`): only that they carry no events and are at
  most the compaction revision; what follows them for the watcher is not stated.
- **The promoted methods**: the field laws (`isWatchableMvcc_store`, `mvccWatchTxnOf_field`) let a
  client call `kv.Read`/`Rev`/`Compact`/`Commit` and the transaction's `Put`/... through Go's
  promotion; WP-transfer laws over the abstract predicates (today's `kvOver_*`, `tw_wp*`) would hide
  the fields (review E2).
- **Sealing**: `Api.lean` publicly imports mvcc's proof modules; adopting it means non-public
  imports and `@[no_expose]` (CLAUDE.md, "Package APIs"), the specs' pure vocabulary (`rangeOutcomeC`,
  `delKeys`, `pendItems`, `writeRev`, `watchEvents`, ...) moved into the API module.
- **Lease `Revoke`** (the lease package's spec, not here): restated over `mvccDeleter_spec`, the
  announcement of its exact deletions, and a right to write the lease bucket inside the store's
  write transaction (today's `storeRb`), which the candidate does not give yet (review B7).
- **v3rpc's send loop**: whether it needs registration facts beyond `wsWatcher`'s `k` (today's
  `idAssigned`, `chanRegFact`, `streamRegAt`) is unchecked (review B6).
- **The laws are obligations**: an implementation proves each `<name>.law` over its definitions
  of the opaque predicates; until then nothing rests on them.
