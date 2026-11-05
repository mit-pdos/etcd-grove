# mvcc's API: candidate specs (2026-11-01, branch `worktree-mvcc-rand-tester`)

The user asked for new candidate specs of etcd's mvcc package, written in the Lean spec files,
designed with the `spec` skill, good enough for etcd's proof and for the randomized tester
(`examples/mvccrand`, `notes/mvccrand.md`). **Status: superseded by rounds 10-11 (below), the candidate for the user's review.** In rounds 1-9 they typecheck;
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
  `spec-reviewer` review of the previous; 5 (`78cde78acf`), after the user's critique; 6
  (`057d769423`), 7 (`b044f1c5b1`); 8 (`efa9b1e853`), the user's decisions applied; 9 (below), the
  review of 8.
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

- **The state** `mvccState γ σ`, `σ : MvccState = {log, crev, pending}`: mvcc's own history (every
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
  that starts after an event was received may still see the revision before it). So a commit is
  two steps of the state (round 8): `notify` (`pending := some pend`, the revision the watchers
  have) and `commitPending` (the bump); reads answer from `σ.log`, exact, and watch events from
  `σ.notifiedLog` (`σ.log ++ pending`). Laws: the events received for a watcher are its range's
  events, filtered, of the revisions `[lo, hi)` of the notified log (`wsRecv_events`); a
  progress response (per watcher, or `-1` for the watchers registered before it was sent and not
  cancelled) comes after every event up to its revision (`wsRecv_progress`); each response's
  revision is at or above its events' (`wsRecv_resp`). The registration (`Watch`) fires the
  caller's update, so a watcher from revision `0` knows its first revision (`σ.rev + 1`).
- **The lessor**: the real lessor (today's `isLessor`, with its reader `lease.lessorRdOf γl`).
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
mvcc's documentation says otherwise: `nonissues/etcd-mvcc-watch-negative-start-rev.md`, found by the
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

## The decisions by the user's criteria (2026-11-02; applied in round 8)

The user's criteria: future proofs over the API should succeed quickly, so (a) the specs are strong
enough for reasonable users, and (b) the API has as few abstractions (opaque predicates,
resources) as possible, one abstraction subsuming several where it can (`mvccState` subsumed the
log's certificates, the revision tokens and the reader's floor). Now a principle of the `spec`
skill ("Abstractions", under "Preferences: measures").

**Is the watch-ahead behavior real?** Yes, at mvcc's level, and narrow. `watchableStoreTxnWrite.End`
sends the events (`notify`) before `storeTxnWrite.End` takes `revMu` and bumps the revision; a read
takes `s.mu` shared (the writer holds it shared too) and `revMu`. A test (2026-11-02, not kept: a
writer putting one key 5000 times, a consumer reading with `Read`/`Rev` and `Range` as soon as an
event arrives, and 2000 other synced watchers of the key, which `notify` serves before the bump,
widening the window) saw a read below the event's revision 4573 times out of 5000 (`event at
revision 3, then Range read revision 2 with a's mod revision 2`); without the other watchers, 0 in
60000. Not reachable through etcd's linearizable reads: a linearizable `Range` waits for the
applied index, which advances after the entry's `End` returned; a serializable one may see it. No
issue filed: mvcc documents no order between watch events and reads.

The answers:

1. **The client-owned state**: yes (it subsumes three abstractions).
2. **The watch-ahead revision**: neither announcements nor linearizing at the notification, but a
   field of `mvccState`: `σ.pending : Option (List Change)`, the revision notified and not yet
   committed. A watchable commit is two atomic steps of the client's state (notify: `pending :=
   some pend`; bump: `log ++ [pend]`, `pending := none`), so its `End` takes two updates; reads
   answer from `σ.log` (exact); the watch laws relate events to `σ.log ++ pending` (no announcement).
   Removes `mvccAnnAuth`, `mvccAnn`, `mvccLogOk` and every announcement premise (End, the views,
   Restore). Strength: the tester relates `pending` to its history directly; etcd's floor is on
   `σ.log`.
3. **Thread tokens**: yes (an existing resource, no new one).
4. **Write-backs from receipts**: yes (removes a resource from every write).
5. **`HashByRev` and `Restore`**: no open-token share (it cuts three of etcd's callers); the weaker,
   true post (the current revision is the state's, or `1` during a restore), and the one-line Go
   fix proposed (`issues/etcd-mvcc-hashbyrev-restore-rev1.md`), which would strengthen it back.
6. **The lessor**: the real lessor only, today's `isLessor` reused (no new definition; a reasonable
   user, etcd or a tester, can use the real lessor; the nominal generality goes).

And the same criteria on the rest of the vocabulary (32 opaque predicates in round 7; about 19
after):

- `mvccHookInit` into `mvccBackendIs` (which already carries the lock's invariant `Pk`).
- `mvccRoTxn` and `mvccWatchTxnOf` into `mvccTxn` (one predicate at the location the client holds,
  with WP-transfer laws for the promoted methods in place of the field laws).
- `mvccNotified` and `mvccRestoreOk` into one (the watchers taken care of, for a commit or a
  restore).
- `isReadViewOf` and `isWriteViewOf` into one view predicate.
- `mvccCommitReq` dropped: the specs take the backend's `commitReq` at `mvccBackendIs`'s backend.
- The watch stream's nine into four: `wsChan` into the stream's handle; `wsClosed` into the closed
  arm's `wsOpen ι q -∗ False`; `wsWatcher`, `wsLive` and `wsCanceled` into the registrar's view
  `wsWatchers ι W` (each watcher's range, filters, first revision, registration stamp and
  liveness), which the laws take with the consumer's `wsRecv`.
- Kept: `mvccState`, `isMvcc`, `isWatchableMvcc`, `mvccOpen`, `mvccBackendIs`, `mvccHook`,
  `mvccTxn`, `mvccDeleter`, the watchers-taken-care-of token, `mvccWrapRight`, the view predicate,
  `mvccRestorable`, `isHashStorage`, `mvccHashOk`, `mvccCompactChan`, `isMvccWatchStream`,
  `wsOpen`, `wsWatchers`, `wsRecv`.

## Round 8 (the user's decisions and consolidations applied, 2026-11-02)

`Api.lean` rewritten and all 43 candidates restated over it (generated by a script, each
candidate block replaced). It builds. The vocabulary:

- **19 opaque Iris predicates** (32 in round 7): `mvccState`, `isMvcc`, `isWatchableMvcc`,
  `mvccOpen`, `mvccBackendIs`, `mvccHook`, `mvccTxn`, `mvccDeleter`, `mvccWatchersOk`,
  `mvccWrapRight`, `isMvccView`, `mvccRestorable`, `isHashStorage`, `mvccHashOk`,
  `mvccCompactChan`, `isMvccWatchStream`, `wsOpen`, `wsWatchers`, `wsRecv`; and 7 opaque pure
  names (`MvccName`, `WsName`, `mvccLeases`, `mvccBackend`, `mvccWatched`, `wsChanOf`,
  `mvccHashOf`).
- **The state** `MvccState = {log, crev, pending}`; `notify`, `commitPending`, `compactTo`,
  `mvccStart`, `MvccReachable` (the steps), `notifiedLog`. A commit's spec takes two nested
  atomic updates: the first's commit (`notify pend`) gives the second (`commitPending`). A plain
  store's `End` does both at the bump; the watchable store's notifies in between, and reads in
  between see the revision before.
- **One transaction predicate** `mvccTxn t γ trace k`, `t` the transaction's interface value
  (`metricsTxnWrite`, `watchableStoreTxnWrite`, `txnReadWrite`), `k : MTxn` (`read σ` or
  `write σ pend`); `mvccTxn_unwrap` gives the watchable transaction's inner store transaction,
  which serves the promoted `Put`/`DeleteRange`/`Range`/`Rev`/`Changes`, and takes it back.
- **One view predicate** `isMvccView v γ` (the read and write views as interface values;
  `isMvcc_views` per mode).
- **The watchers taken care of** `mvccWatchersOk γ (op : MvccOp)` (`commit σ pend`, `restore`):
  free on a store without watchers (`mvccWatchersOk_unwatched`) and for a commit of nothing
  (`mvccWatchersOk_nil`); only the watchable store's own `End` and `Restore` have it otherwise.
- **The backend's identity** `mvccBackendIs γ P Pk b` subsumes the hook's initialization
  (round 9: `mvccHook` defined over it); `Commit`, `Compact` and `Hash` take the backend's own
  `commitReq` at it.
- **The watch stream**: `wsChanOf ι` (pure; `Chan` returns it, `wsChan_recv` receives on it);
  closed is `□ ∀ q, wsOpen ι q -∗ False` (in `Watch`'s error arm); the registrar's view
  `wsWatchers ι W`, `W : List WInfo` (range, filters, first revision, registration stamp, live),
  the id a watcher's position: `Watch` and `Cancel` take atomic updates over it (`Watch` with the
  state, so the first revision of a watch from `0` is `σ.rev + 1`).
- Answers applied: the client owns `mvccState`; `threadTok` for readers (`New`'s
  `threadBound GF ≤ 2 ^ 30`); write-backs from receipts (`New`'s `□ (⧗ 1 ={⊤}=∗ wbTok)`); no
  open-token share on `HashByRev`, whose current revision is the state's or `1`; the real
  lessor (`isLessor`).

## Round 9 (the review of round 8, 2026-11-02)

The review (`spec-reviewer`) found round 8 sound against the Go code but for one law, and checked
that a client can use it: the watchable transaction's `Put`/`Range` reach `metricsTxnWrite`'s specs
through `mvccTxn_unwrap`; the server's apply loop commits with both steps (the first update records
the entry being applied as pending; its commit gives the second). Applied:

- **`mvccTxn_write_agree` contradicted `watchableStoreTxnWrite.End`'s proof**: that `End` notifies
  (its first update fires), then calls the store transaction's `End`, whose spec needs the
  transaction's `mvccTxn` at the state it began at while the state is notified: the law gave
  `False` there. Now the state is the transaction's or its notification of the transaction's
  changes (`notify` is idempotent: the inner `End`'s first update is no change); a sole writer
  refutes the second from its own invariant.
- **`Cancel` of a negative id** marked watcher `0` dead (`sint.nat` of a negative is `0`), which
  the code does not: the update is guarded by `0 ≤ sint.Z id` (a v3rpc `CancelRequest` of `-1`
  would have cost watcher `0` its progress guarantee).
- **`Restore`'s linearization point** stated (`store.Restore`, `HashByRev`): when it sets the new
  current revision (`kvstore.go:386`), before the leases are re-attached and an unfinished
  compaction resumed; `HashByRev`'s `cur = σ.rev ∨ cur = 1` holds with it.
- **`ws_excl.law`**: the registrar's view and the consumer's are exclusive (the `W` and `rs` the
  watch laws take are the current ones).
- **Two abstractions fewer** (17 opaque Iris predicates): `mvccHook γ P f` defined, `∃ BP b,
  mvccBackendIs γ BP P b ∗ backend.plHookRO (mvccBackend γ) f` (its only maker is the backend;
  `mvccHook_of_backend` gone, `mvccHook_agree` now a theorem from the hook's ghost variable);
  `isHashStorage hs γ` defined, `∃ s, isMvcc s γ ∗ s.hashes ↦□ hs` (the field `NewStore` sets for
  good).

## Rounds 10-11: the smallest API etcd's proofs and the tester need (2026-11-02)

The user (2026-11-02): specs for mvcc strong enough for etcd and for the tester, as simple as
possible (fewest new abstractions and Iris predicates); specs first, frozen, then the invariants
(informally, frozen), then the proof. **Status: candidate for the user's review, not frozen.** The
candidate, in full: a scratch Lean file outside the repository, typechecked against the build
(`lake env lean FILE` from the worktree): `~/mvcc-api-candidates/MvccApiR11.lean` (its header
lists every change). Rounds: 10, from round 9 by the user's criterion; 11, after a
`spec-reviewer` review of 10 (nothing unsound; two gaps, below), reviewed again (repairs sound;
`Write` now also says nothing is pending; the thread bound's `+ 2` dropped). The reviews:
`~/mvcc-api-candidates/review-r10.md`, `review-r11.md`.

**The scope: what etcd's linked proofs reach, and what the tester calls** (a survey of the clients,
2026-11-02). `New`; through the `KV` (`WatchableKV`) the store is: `Read`, `Write`, `Rev`, `Range`
(the apply's header after a compaction), `Compact` (the apply's compaction, `putgetc`'s
auto-compactor), `Commit` (the tester), `HashStorage` (etcd only hands it to its corruption
checker), `Close`, `NewWatchStream`; the transactions' `Rev`, `FirstRev`, `Range`, `Put`,
`DeleteRange`, `Changes`, `End`, and `NewReadOnlyTxnWrite`; the watch stream's `Watch` (from
start revision `0`, no filters, id `0`: v3rpc's `watchReqOk`), `Chan`, `RequestProgress`,
`RequestProgressAll` (client/v3's proof relies on a `-1` response covering every watcher registered
before it), `Cancel`, `Close`, `Rev`. Out: `NewStore` (a store without watchers), `Restore` (no
linked result reaches it: `applySnapshot` is linked for the nil snapshot only), the hash storage's
methods, the `KV`'s own `Put`/`DeleteRange`/`FirstRev`, watch filters, a caller-chosen watch id,
a store without a post-lock hook.

**The vocabulary: 8 opaque Iris predicates (round 9: 17), 5 opaque pure names (7).**
`mvccState γ σ` (the client's state, as before: `log`, `crev`, `pending`); `isMvcc kv γ` (the one
store handle, on the `KV` interface value); `mvccOpen γ q` (`Compact` a share, `Close` the whole);
`mvccBackendIs γ BP Pk b` (the backend's identity and batch-lock invariant, for the hook and the
commit requests); `mvccTxn t γ trace k` (any transaction interface value); `isMvccWatchStream ws γ ι`;
`wsState ι S` (the stream's state, the client's: its watchers, each with range, first revision,
registration stamp and liveness, and whether it is closed); `wsRecv ι rs` (the consumer's).
Definitions: `mvccHook`, `mvccDeleter` (the lessor's range deleter is `Write`'s triple),
`compactChanOk` (a receive's triple), `wrespIs`, and the watch guarantee `wsRecvOk σ S rs`, one pure
predicate. Laws: persistence/timelessness/fractions, exclusivity, reachability, the hook's
agreement, the channel's receive, and one watch law (`wsRecv_ok`: the guarantee holds of what was
received, at any time). Gone from round 9: `isWatchableMvcc`, `mvccWatched`, `mvccWatchersOk`,
`mvccWrapRight`, `isMvccView`, `mvccRestorable`, `isHashStorage`, `mvccHashOk`, `mvccHashOf`,
`mvccCompactChan` (now a definition), `wsOpen` (now `S.closed`), `wsWatchers` (now `wsState`),
`MvccOp`, and the laws `mvccTxn_trace`, `mvccTxn_unwrap`, `isWatchableMvcc_store`, `isMvcc_views`,
`mvccTxn_write_agree`, `mvccDeleter_spec`, the two `mvccWatchersOk` laws, the restore and hash laws,
and the three watch laws (one now).

How the count came down:

- **One store kind** (only `New`'s is in scope), so no watched mode and nothing that let a plain
  store's commit skip the watchers.
- **Each spec is on the call the client makes**: the method of the interface value it holds
  (`methods ty M v` of `interface.mkOk ty v`), whatever the dynamic type (`*watchableStore`'s
  promoted `Read`; `*metricsTxnWrite`, `*watchableStoreTxnWrite`, `*txnReadWrite`). No field laws
  for promoted methods, and none of today's dispatch lemmas (`kvOver_*`, `tw_wp*`) for clients.
- **The trace is lent per call** (`Range` and `Put` step it, and etcd's `txn` steps it while a
  transaction is open), not held by the transaction.
- **The stream's closed flag is a field of the client's stream state.** `Watch` on a closed stream
  fires the update unchanged, so the caller learns `S.closed`; `Close` takes an open stream (a second
  `Close` panics) and closes it.
- **Write transactions** (round 11, the review's F2): `Write` fires the caller's update where it
  reads its begin revision; `End`'s two updates (notify, then the bump) promise in their atomic
  postconditions that the state is the transaction's. The client learns its transaction's state
  from the API, with no agreement law.

Each spec's linearization point is in its docstring. The ones the proof must move from where round 9
put them: `Watch` fires at the registration, inside the store's `watch` (so the first revision of a
watch from `0` is `σ.rev + 1`, and every id a response carries is in the stream's state, the
tester's registrar check); `Cancel` fires at its first check of the stream's maps.

**Found on the way** (both reproduced with mvcc-level Go tests):
`nonissues/etcd-mvcc-watch-compact-rev-subrev-lost.md` (a watch from exactly the compaction revision
loses the earlier changes of a key changed twice in it), and
`nonissues/etcd-mvcc-progress-lock-order-deadlock.md` (found by the review: `progressIfSync` takes the
two store locks in the wrong order; a hang, which no spec here falsifies).

### Decisions for the user (before freezing)

Each is a scope restriction, or client-owned state or a premise on specs that have clients (the
skill's policy). Round 9's statement is given beside each, with the alternative.

1. **The scope above.** Out: `NewStore`, `Restore`, the hash methods, the `KV`'s own writes,
   filters, caller-chosen ids, a nil hook. Round 9 specified all 43 functions. Alternative: add any
   of them back; each adds vocabulary (`Restore`: `mvccRestorable`; hashes: `mvccHashOk`,
   `mvccHashOf`; filters: a predicate list in `WInfo`, `filtersImpl`; `NewStore`: the watched mode
   and `mvccWatchersOk`).
2. **Specs of interface-method calls.** The API's specs are of `KV.Read`, `TxnWrite.Put`,
   `WatchStream.Watch`, ... as the client calls them, and the concrete methods' specs
   (`store.Read`, `metricsTxnWrite.Put`, ...) become internal lemmas. This departs from CLAUDE.md's
   layout (one spec file per Go function); the files would be named by interface method
   (`Spec/.../mvcc/KV__Read.lean`). Round 9: specs of the concrete functions, plus field laws.
3. **The stream's closed flag in the client's stream state**, which replaces the fractional open
   token `wsOpen`. Consequence: v3rpc, whose closer runs beside its receive loop, keeps `wsState` in
   an invariant the two share. Alternative: keep `wsOpen` (one more predicate; v3rpc's receive loop
   then holds `wsWatchers` alone and handles a closed arm).
4. **The watch guarantee only for watchers whose first revision is above the compaction revision.**
   The code does not deliver their events exactly otherwise (the issue above). It is enough for both
   clients: the tester never compacts, and etcd's watch proof excludes compaction (`noCompactor`).
5. **The registration stamp** `WInfo.k` (the responses sent when the watcher registered), and a `-1`
   response at index `j` covering the live watchers with `k ≤ j`, as the old proof's `regsAt`/
   `respCompl`. A client relating its own progress request to the response does the matching, as
   today.
6. **The backend boundary is a placeholder** (`mvccBackendFresh d Pk`): round 9's ten conjuncts of
   internal backend views; to be designed with the backend. It must admit a compacting backend (the
   review's F1: `Compact`'s job deletes keys and commits after `Compact` returns, which needs M2's
   backend compaction model). Round 9 excluded one (`d.cm = false`).
7. **`New`'s premises** `receiptBound GF ≤ 2 ^ 48` (round 9's) and `threadBound GF < 2 ^ 30` (Go's
   `RWMutex` reader limit, each reader a thread holding a token; round 9 had `+ 2 ≤`, which the
   re-review found no reason for in the code).

## Decisions for the user (round 7's list; answered above, kept for the record)

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
- **Watches** (etcd's `v3rpc` watch server, the tester's watch stream): events from the notified
  log (the client's state, whose `pending` its own `End` sets: no announcement), progress per
  watcher and for the stream (the tester's checks), the registration's first revision (etcd's
  clients watch from `0`).
- **Leases**: puts with a lease keep the item map (as today); `Revoke` (the lease package's spec,
  not changed here) would take the two commit updates of its exact deletions (the keys the item
  map puts on the lease, sorted), which its caller can compute, in place of today's `∀ pend,
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
- **The promoted methods**: the field laws (`isWatchableMvcc_store`, `mvccTxn_unwrap`) let a
  client call `kv.Read`/`Rev`/`Compact`/`Commit` and the transaction's `Put`/... through Go's
  promotion; WP-transfer laws over the abstract predicates (today's `kvOver_*`, `tw_wp*`) would hide
  the fields (review E2).
- **Sealing**: `Api.lean` publicly imports mvcc's proof modules; adopting it means non-public
  imports and `@[no_expose]` (CLAUDE.md, "Package APIs"), the specs' pure vocabulary (`rangeOutcomeC`,
  `delKeys`, `pendItems`, `writeRev`, `watchEvents`, ...) moved into the API module.
- **Lease `Revoke`** (the lease package's spec, not here): restated over `mvccDeleter_spec`, the
  commit updates of its exact deletions, and a right to write the lease bucket inside the store's
  write transaction (today's `storeRb`), which the candidate does not give yet (review B7).
- **v3rpc's send loop**: whether it needs registration facts beyond `WInfo`'s `k` (today's
  `idAssigned`, `chanRegFact`, `streamRegAt`) is unchecked (review B6).
- **The laws are obligations**: an implementation proves each `<name>.law` over its definitions
  of the opaque predicates; until then nothing rests on them.

### The user's answers to rounds 10-11 (2026-11-03)

1. **No verified method left out** (now a principle of the `spec` skill, "A smaller API is not a
   narrower scope"). Back in scope, each with a linked proof today: `NewStore`, `store.Restore`,
   `watchableStore.Restore`, the store's views (`readView.Range`/`Rev`/`FirstRev`,
   `writeView.Put`/`DeleteRange`), `txnReadWrite.Put`/`DeleteRange` (they panic), `hashStorage.Store`
   (an axiom today), `NewHashStorage`, and watch filters (today's `Watch` takes them). Still out, no
   proof today: `HashByRev`, `Hash`, `Hashes`, a caller-chosen watch id, a store without a hook.
2. Asked for an explanation (the layout problem of interface-method specs).
3. Asked why the stream's closed flag in its state affects v3rpc.
4. Asked what the lost-events bug is; **compaction must be supported** (with watches).
5. Asked what the question is (the registration stamp).
6. Asked why the backend boundary is a placeholder.
7. **`New`'s premises accepted.**

### The user's second answers (2026-11-03)

1. **A store without a hook is in scope** (the tester may run without one): `Write`'s and
   `Compact`'s hook contract gets back its `nil` row (`LockInsideApply` then runs nothing: the
   caller's view shift from `P ∗ Pre` to `Q`); `mvccHook γ P func.nil` from the backend's own frozen
   `nil` hook. Round 9's proof required a hook (`bkHookIs`): proof work, not a spec restriction.
2. Asked for options A and B in detail.
3. **The closed flag in the stream's state: accepted.**
4. Proposed instead of a fix: a precondition that a transaction does not change a key twice; asked
   whether to fix upstream, and its cost. Found while answering: on upstream `main` (without
   etcd-io/etcd#22395) the bug is likely reachable through gRPC (`nonissues/etcd-mvcc-watch-compact-rev-subrev-lost.md`).
6. **The backend precondition designed now, against M2's model: accepted.**

### The user's third answers (2026-11-03)

2. **Canonical specs are per (concrete type, method)**, a plain mapping from (type, method name) to
   spec; an interface value gets a separate predicate bundling its interface's contracts, as
   Perennial's `sync.isLocker` (now a principle of the `spec` skill).
4. **A condition is acceptable if it does not bifurcate the proof**: no disjunction whose sides a
   proof would establish by near-copies (now a principle). Round 12's single condition:
   `onceUpTo L w.lo σ.crev`, every revision from the watcher's first up to the compaction revision
   changes each key at most once (vacuous below the compaction revision). One proof path: a catch-up
   read after a compaction at `c` returns revision `c`'s last change per key, which is all of it
   under the condition.

## Round 12 (2026-11-03): every verified method, canonical (type, method) specs, the backend

The candidate: `~/mvcc-api-candidates/MvccApiR12.lean` (typechecked; its header lists the
changes). In short:

- **Contracts per interface method** at a receiver `(ty, v)` (`KV.Read.contract`, ...,
  `Txn.End.contract`, `WatchStream.Watch.contract`); each (concrete type, method)'s canonical spec
  is its contract at the type (`store.Read.spec := ∀ s, KV.Read.contract PS #s`;
  `watchableStore.Read.spec`, promoted, likewise). Pure bundles `isKV`, `isWatchableKV`, `isTxn`,
  `isWatchStream` (the contracts at a value's type) and the law `bundles.law` (a handle, a
  transaction, a stream meet them), as `Mutex_is_Locker`.
- **Back**: `NewStore` (no mode needed: clients only hold the stores the constructors return),
  `Restore` (both stores), the store's own `Range`/`Rev`/`FirstRev`/`Put`/`DeleteRange` (one-shot
  transactions), `txnReadWrite.Put`/`DeleteRange` (their contract needs a write view, which no
  read-only transaction has), filters (`WInfo.fs`, `filtersImpl`), a store without a hook
  (`hookRun`'s `nil` row; the hook fact the backend's `plHookRO`, freezable at `nil`).
- **The backend is a fractional token** `mvccBackend γ q B Pk` (`Restore` replaces the backend, so
  round 11's persistent `mvccBackendIs` could not stay).
- **The backend boundary** (`mvccW gx`, `mvccWReg gx`, `mvccBackendFor B Pk L c`, `backendRest`,
  sealed; laws `mvccW_alloc`, `mvccBackendFor_open`): `New`, `NewStore` and `Restore` take what
  `backend.New`'s post (or `storage.OpenSnapshotBackend`'s) gives at the store's write invariant,
  always the compacting form (every opened backend carries what compaction needs: no compaction
  mode in the API). From a survey of the server's boot and snapshot paths (`BootBackend.lean`,
  `BuildLemmas.lean`, `SnapApplyWalk.lean`).
- **This branch is far behind `lean`** (866 commits, 2026-11-03; 68 ahead): M2 (compaction over
  the real backend, a compaction-mode `Restore`) is merged there, so the boundary's body and the
  proof are to be built on `lean`.
- Found on the way: this worktree's Perennial checkout was at `c4a24e3` (not the manifest's pin
  `d62b13a`) from 2026-11-02 19:40; `lake env lean` (the scratch typecheck) checked out the pin,
  and the build's artifacts are `c4a24e3`'s. Left for the user.

## Round 13 (2026-11-03): the review of round 12

`~/mvcc-api-candidates/MvccApiR13.lean` (typechecked); the review: `~/mvcc-api-candidates/review-r12.md`.
Nothing unsound in the specs; two laws unprovable and three gaps, repaired:

- **The open law at `backend.newPost`** (the backend's payment rights kept): at `newPostK`'s
  arbitrary `K` the store's write-back tokens are not there. **The snapshot path cannot make a
  `mvccBackendFor` as it stands**: `storage.OpenSnapshotBackend` deposits the payment rights with
  the apply protocol (`K := snapOpenK`, `SnapApplyWalk.lean:270`). A server-side question for the
  user (give them back for the store, or a law at that `K`).
- **`Restore`'s length bound** `σ'.log.length + receiptBound GF + 3 ≤ 2 ^ 63` (today's carries it in
  its revision tokens).
- **The shape laws** (`shapes.law`): a handle, a transaction, a stream are an `interface.mkOk ty v`
  of a type meeting its contracts (a client can make its first call on what `Read` returned).
- **`Restore` gives back the store's half of the old backend's open token**
  (`backend.bOpen B.γB ½`): the client closes the old backend after a restore. **Not `Close`** (the
  re-review, `review-r13.md`): `store.Close` takes no lock, so a `Read`, `Range`, `Rev`, `FirstRev`
  or progress request may still hold a reader's part of that half. `Close` gives nothing, so a
  client cannot close the backend after the store (the tester's `be.Close()`, etcd's shutdown):
  the user's decision whether every read and write entry point takes a share of `mvccOpen`, as
  `Compact` does (a new premise on specs with clients; etcd's request goroutines would draw shares).
- **`Restore` from a compacted image** (`imageOf L c D`, with two obligations: a scheduled
  compaction above the finished one is `c`; `L`'s last revision is the largest of the Key bucket's and
  the compaction revisions), resuming an unfinished compaction under the new backend's `nil` hook,
  lent (a marked scope restriction: etcd sets that hook after `Restore`). The re-review found the
  commit request lent for it vacuous; dropped.
- Open, from the review: where the server gets `Restore`'s length bound for a snapshot another
  member made (bounded by that member's writes, not this process's receipts).

### Decision 1, settled (the user, 2026-11-03): closing and shutdown out of scope

Asked whether etcd is buggy when it shuts down concurrently with reads: yes, a read still running
when the server stops crashes the process (`issues/etcd-read-after-backend-close-panic.md`,
reproduced on an embedded server). The user: do the proof without verifying closing and shutdown,
out of scope for now, since the code is buggy. So `Close` keeps round 13's minimal contract (the
whole open token in; nothing about the backend out; kept because etcd's linked `NewServer` calls
`kv.Close()` on its error path), no proof closes the backend after the store, and the tester's
adequacy stops before its final `kv.Close()`, `le.Stop()`, `be.Close()` (to be shaped when the
tester's proof is planned: proved up to them, or `Main` without them).

### Decision 2, settled (the user, 2026-11-03): the backend law over the store's needs

`Restore`'s contract frozen as round 13 has it. The law making the store's backend resources
(`mvccBackendFor_open`) takes what any opener returns (`backend.newPostK` at the caller's `K`:
`bFresh` at boot, `snapOpenK` when applying a snapshot), plus the store's part of the backend's
payment rights in the backend's own terms: write-back tokens (two for `NewStore`'s own writes and
the receipt-paid supply's stock; the count to settle on adoption) and half the clients' open token.
Correction to round 12's review (H1): the snapshot proof does hold the new backend's write-back
tokens (`SnapApplyWalk.lean:352`); `snapOpenK` deposits the open token's close half and a futures
entry. Wiring the snapshot path to the law, and its proof of `Restore`'s length bound (today from
the old store's revision tokens and `restoreLogOk`; under the API from the model of raft's applied
log), wait for etcd's snapshot proof to be linked.

### Decision 3, settled (the user, 2026-11-03): `Restore` at any share of the new backend's hook

Three candidate statements were compared (the user asked for the specs side by side): (L) the loan
of the new backend's unset hook (`plHook B'.γB nil`, given back); (G) a hook contract as
`Compact`'s over a frozen hook (`hookIs B' f`); neither implies the other (freezing is permanent;
a frozen hook's holder has no owned `nil`). (U), chosen: the hook at any share `dq`
(`backend.plHookAt B'.γB dq f`, given back) with `Compact`'s hook contract and commit request
(`backend.commitReq`, the backend's existing contract for a commit, `X` to `Y`, which the backend's
pre-commit hooks may serve: etcd's consistent-index save), the post split on whether the image
recorded an unfinished compaction (`if u then Post ∗ Y else Pre ∗ X`): (L) is (U) at the owned half
and `nil` with trivial `Pre`/`Post`/`X`/`Y`, (G) at the discarded fraction. So `mvccBackendFor` and
`imageOf` carry `u` (`New`, `NewStore`: `false`). New principle of the `spec` skill (look for the
common generalization of incomparable specs) and a memory (show specs, not prose).

## The freeze (2026-11-03)

The user delegated the decision to freeze, by the `spec` skill's criteria: every decision of the
user applied; the `spec-reviewer`'s passes after the last repairs (`review-r13b.md`,
`review-r13c.md` in `~/mvcc-api-candidates/`) with nothing unsound or incomplete left but its own
proposed repair (the thread bound `threadBound GF ≤ backend.rdStockN`: the store has the backend's
counted reader slots only) and one restriction found by the survey of `lean`'s internals (the open
token exclusive: a compaction schedules its job after releasing `s.mu`, so concurrent compactions
could queue their jobs out of order; out of scope, marked); and the statements built against `lean`.
Frozen as `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean` and `ApiState.lean`, namespace
`mvcc.api` (the stream's record renamed `StreamState`: `lean` has a `mvcc.WsState`; the names
`MvccName`, `WsName`, `mvccLeases`, `wsChanOf` opaque until the invariants define them).

## Reopened before the proof: what the clients need (2026-11-03)

The user: every spec and invariant first. The assessments of etcd's proofs over the frozen API
(`~/mvcc-api-candidates/assess-{watch,txn,server}.md`) find API changes; they are applied together
once all three are in.

From the watch path (`assess-watch.md`):
- **G1** a persistent `wsSentLb ι n` (the stream has sent at least `n` responses), given by `Watch`
  at the watcher's stamp `k`: else no client can establish `w.k ≤ j` for a `-1` response, and
  `wsRecvOk`'s stream-wide progress is unusable (the tester's too). Today: the drain before a
  created response (`v3rpc/serverWatchStream__sendLoop.lean:1464`, `watch_tryrecv_au_alt`).
- **G2** a non-blocking receive law (the drain is a `select` with a default), whose empty case gives
  `n ≤ rs.length` for every `wsSentLb ι n`.
- **G3** a compaction response's revision is `0` (true of the code; client/v3 relies on it).

From `txn` (`assess-txn.md`): rebuildable, its specs simpler (logically atomic, passing the API's
updates through; the sole writer's pin becomes apply's own ghost variable); one gap:
- **T1** a size law: every state readable at a revision at or above the compaction revision has
  fewer than `2 ^ 62` keys, with non-negative versions and revisions (from the backend's existing
  `keySized` assumption): `sortRangeResults`'s premise (the heapsort fallback's), which today's
  write path takes from `isTxnWrite_small` (`TxnLemmas.lean:281`) and the read side from mvcc's
  receipts (`InvRead.lean:93`), and which no whole-log bound gives after a compacted `Restore`.

**Round 14** (`d3a8e46433`, its review `review-r14.md`, repaired): A1 `wsSentLb ι n`, given by
`Watch` at the stamp, and `wsSentLb_zero` (a refused create's drain); A2 the non-blocking receive,
in one channel law with the blocking one (one channel name); A3 a compaction response's revision `0`;
A4 **a read transaction's** states have fewer than `2 ^ 62` keys (`mvccTxn_small`; the review: a law
on `mvccState` alone was false, `keySized` holds of a read-locked view only, and versions can wrap
after a compacted image, so versions are the client model's fact and a write path's size its
client's premise); A5 the Lease bucket's delete inside a write transaction, giving back `End`'s
triple, not `mvccTxn` (the backend's batch session admits only `Unlock` after an `UnsafeDelete`).
Found while checking the watch path's gap W1: the gRPC handler contract's per-run resource `S` is
the server's choice (`InvGrpc.lean:151`), and the lease read already passes `threadTok` through it
(`InvLeaseRead.lean:17`): the KV and watch handlers do the same, no trust-base change.

**The client drafts** (`~/mvcc-api-candidates/clients-{txn,server,watch}.md`, Lean in
`clients/{txn,server,watch}/*.lean`, each typechecked): `txn` keeps no invariant (its entry specs
pass the API's updates through, the sole writer's pin the caller's); the server's `kvStoreInv`
holds `mvccState` with the committed and notified logs' monotone lists, raft witnesses and the
compaction permit, and states the update builders apply uses; v3rpc's `wsInv` holds `wsState`, the
registry, the cancel requests and the close token, and its send loop applies `wsRecv_ok` after each
receive. API changes from them: `shapes.law` restored (deleted by accident with round 14's channel
law); the range deleter not `nil` (S2); the names inhabited (S3, `names_nonempty`). Open, for the
user: the size bounds the hidden time receipts gave (the write path's sort margin, `Revoke`'s sort,
non-negative versions, the watch path's `LogSmall`).

**Round 15 (the user's (D), 2026-11-03).** The user asked why a client would need a size bound from
the state: it does not. The only need is etcd's sort of a range's results (`txn/range.go:125`): at
most `2 ^ 62` entries (the sort's premise) with non-negative revisions and version (Go's comparators
subtract, `range.go:214-226`). So the `Range` contracts (`KV.Range`, `Txn.Range`) say it of every state
they could read (`stateOk`, `kvSortOk`, `ApiState.lean`), round 14's state-level law `mvccTxn_small`
is gone, and `Restore` takes the restored history's receipt `⧖ (logCh σ'.log)` (the server's snapshot
image certificate carries it), so the store keeps today's whole-history receipt (no relative budget,
`notes/mvcc-api-invariants.md` §4.3 superseded). Not chosen: strengthening the backend's `keySized`
(a trust-base change) or a workload premise on etcd's results; nor (C), the same receipt exported as
a law on `mvccState`.

**Round 16 (the user, 2026-11-03: hide the receipt in an existing abstract predicate traced from
the sender's mvcc to the receiver's `Restore`).** The cross-review found round 15's `⧖ (logCh σ'.log)`
premise on `Restore` circular for its callers (the server's certificate got it from mvcc's internals)
and client/v3's and the watch path's models still needing `LogSmall`. So: the pure `imageOf` becomes
`mvccImage D L c u`, opaque and persistent, the image *with* its receipt; `mvccBackendFor_open` takes
it, `Restore` no longer takes a receipt (it is inside the `mvccBackendFor` it is given), and
`mvccImage_fresh.law` makes one for an empty backend (no change, no receipt: `New`, `NewStore`). The
sender's law making an `mvccImage` of a snapshot of a store's backend (G3) is designed with the
server's draft, over `backend.Snapshot`'s spec. The value facts move to the results: `kvSortOk` is
now positivity (creation and modification revision, version: what the comparators and client/v3's
`0 < version` need), and `wsRecvOk` says each event's revision positive, a put's creation revision
and version too. No state-level size law is exported; but client/v3's exported results state
`LogSmall` of the whole history (`kvLogOk`, `etcdserver/KVLogOk.lean`), which the server must keep
of its model's log, so (the cross-review's §1, by "a fact the caller needs of a result belongs at the
call that returns it"; decided by me, the user: "fix specs in minor ways on your own" when the skill
is clear) every step that changes the history gives its update the receipt of the history it makes:
the notify step of `Txn.End`, `Put`, `DeleteRange` (`⧖ (logCh (σ.log ++ [pend]))`) and `Restore`'s
step (`⧖ (logCh σ'.log)`). `Restore`'s length premise is dropped: a committed revision is never
empty (`commitLog`), so the receipt inside `mvccBackendFor` bounds the length.

**Round 16, the clients' updates (2026-11-03).** The three drafts are updated (txn needs nothing
more; watch and server need the laws below). Added: `reach_logWf.law` (pure: a reachable state's
history and notified history are `LogWf'`, which the read path and the watch path need for their
clients' `LogWf'`), and `mvccImage_snapshot.law` (G3: the sender's image, from `backend.Snapshot`'s
triple, with the whole backend share held through the call and the caller's update at the state).
The server draft proposed instead a pin predicate (`mvccPinned`, with pin and unpin laws: one more
predicate and two laws); the update at the state is the API's existing shape for reading the state
and needs neither (the law's proof commits it before the call, and the whole share keeps every
step that changes the history out until the share comes back). The lease-delete law's `End` triple
gets the notify receipt as `Txn.End`'s.

**Round 16, the review (`~/mvcc-api-candidates/review-r16.md`, 2026-11-03).** F1 (blocking):
`mvccImage_snapshot.law` is unprovable for a store that compacted on its backend:
`backend.Snapshot`'s axiom (`Spec/.../backend/backend__Snapshot.lean`) reports nothing of the two
compaction keys once a write after the open has put them (they are in no part of its observation,
and `fkRd` gives their values only before the first such write). Decided by me for now: the law is
stated for a store that never compacted (`σ.crev = -1` in the update's access), today's sender
coverage (`txn/KeyObs.lean`'s no-compaction token; the compacting sender is G3's deferred `sorry`),
the premise local to the law, and dropping it later breaks no client. **For the user** (a
trust-base change): to cover a compacting sender, strengthen `backend.Snapshot`'s axiom in place,
its observation also given the compaction keys' committed values, tracked by the backend as the
hook's own keys are (a new `fkdAt γ v` half, `UnsafePut`'s proved `fkPut` updating it); the
review's alternative, a second stronger `Snapshot` spec only this law takes, is against one spec
per function. F2: `isMvcc` added to the law's precondition; the exclusion it needs is internal
(the invariants note, §2: a share token of total 1 behind `mvccBackend`, a frozen writer state).
F3: `mvccImage_fresh.law` under `|==>` (`⧖ 0` is allocated). F4 (`keySized` derivable) kept as
today. F5: the invariants note completed. F6: `kvSortOk`'s docstring names its real consumers. F7:
the receipt rewrites go into the vocabulary at stage 1; `reach_logWf` a theorem there.

**Round 16, F1 decided (the user, 2026-11-04): "Strengthen the axiom."** `backend.Snapshot`'s
axiom is strengthened in place: the observation is also handed the batch lock's half of the
compaction keys' committed values (`fkdOwn γ v`, ghost name `γ.fkd`, half the batch lock's in
`fkHalf` at the writer's contents' `fkVals`, half the client's inside `fkOwn`, which mvcc's
compaction holds), and `Q` is applied to `fkVals D` too. `UnsafePut` of a compaction key updates
both halves (`fkHalf_raise`); every other operation keeps the values (`fkVals_put`/`_del`/
`_create`/`_delBucket`); `batchLocked_fkd` is the client's agreement. Every caller's statement is
unchanged (the server's `srvBeSnapOk_of_backend` instantiates the new argument away).
`mvccImage_snapshot.law` drops its never-compacted premise (`σ.crev = -1`): a compacting sender is
covered. The axiom is to be re-attacked with the `axiom` skill.

**The probes (2026-11-04, `notes/mvcc-api-probes/`, `notes/mvcc-api-risk.md`).** M1
(`WsRecvOkProbe.lean`): `wsRecvOk` follows from pure facts each response records at its send, with
monotone agreement (no later, credit or fancy update); its obligations on the implementation are in
its header. C1 (`WatchClientProbe.lean`): v3rpc's `drain_empty`, `snap_after_recv` (a `|={⊤}=>`
with no credit) and `progressCov`'s core are provable over the API's laws; it found
`wsChan_recv.law`'s `∃ γch` unnameable by a client's definitions, so the channel's ghost names are
an opaque `wsChanNames ι` (decided by me: a strengthening, clear by the skill), and asks that
`persistent.law`'s instances be real `instance`s once the predicates are defined (stage 2).

**Probe M2's two obstructions, decided (the user, 2026-11-04).** (1) `Compact(0)`: ruled out,
`KV.Compact.contract` takes `1 ≤ rev` and `MvccReachable.compact` `1 ≤ r` (a `Compact(0)` mid-job
restores to compaction revision -1: `issues/etcd-restore-scheduled-compact-zero.md`; etcd's
`EtcdServer.Compact.spec` requires it too; the tester never compacts). (2) The Key bucket's cut:
the `Snapshot` axiom gives the bucket only thin of the logical view (`thinV`: each missing entry
`KeyDel`), which does not exclude a gap (a tombstone deleted before the put it kills, which restore
resurrects: `SnapImageProbe.lean`'s `thin_not_cut`). The user: "the snapshot axiom should imply
that the snapshot when restored from will give a correct view of the abstract etcd state
associated with that snapshot": the axiom is strengthened so that the snapshot's Key bucket is
known exactly (the safe-range bucket's physical deletes tracked by the backend, as the compaction
keys' values are), and the criterion of done is the image (what `restore()` reads) proved from it
with no gap.

**The `Snapshot` axiom sees the `Key` bucket exactly (the user's criterion, 2026-11-04).** Done as
`notes/decisions.md`, "The backend's `Snapshot` axiom sees the safe-range bucket exactly": the
observation gets the batch lock's half of the safe-range deleted entries and the physical view
exactly the logical one but them (`viewAtD`, `dlVd`). The acceptance check is proved
(`SnapImageProbe.lean`'s `key_of_obs_exact`, `image_of_obs_exact`): with the store's facts (its
logical bucket its log's, the deleted entries what its jobs deleted, its records), the snapshot's
data is the image `restore()` reads. What the store must keep (stage 2): the client's half (inside
`fkOwn`, in the compaction's resources) at what its jobs deleted, with the jobs' cursors. No API
statement changes: `mvccImage_snapshot.law` keeps its statement over the strengthened axiom.

**`mvccW_alloc.law` strengthened (2026-11-05, stage 2).** The snapshot law's proof found it gave only
the registration `mvccWReg gx`, while a client's boot opens the backend at `W := mvccW gx`
(`backend.New`'s precondition needs the client to produce it) and no law gave it. Now
`⊢ |==> ∃ gx, mvccWReg gx ∗ mvccW gx`: a strengthening, decided by me (clear by the skill).


**txn's migration, 2026-11-05: decided by the coordinator.** Two strengthened posts, facts txn
needs at the call that returns them (applied to `Api.lean` by the mvcc track; the contracts' proofs
come with the contracts):
- **A.** `KV.Range.contract`'s post gains `⌜LogWf' σ.log ∧ ∀ cs ∈ σ.log, cs.length < 2 ^ 63⌝`, and
  `Txn.Range.contract`'s `⌜LogWf' k.readLog ∧ ∀ cs ∈ k.readLog, cs.length < 2 ^ 63⌝`: the read log
  well formed (every delete of a present key) and each revision of fewer than `2 ^ 63` changes.
  `LogWf'` is `LogLemmas`' (importable).
- **C.** `Txn.Changes.contract`'s post gains `⌜0 ≤ sint.Z chs.len⌝` (Go's `len(...) > 0` is a signed
  comparison).
- **F.** `Txn.DeleteRange.contract`'s post gains `⌜LogWf' (σ.log ++ [pend ++ ds]) ∧ ∀ cs ∈ σ.log ++
  [pend ++ ds], cs.length < 2 ^ 63⌝`: the transaction's state after the delete (its pending revision
  `pend ++ ds`) well formed and each revision of fewer than `2 ^ 63` changes, as A for `Txn.Range`'s
  read log.

**The server's migration, 2026-11-05: decided by the coordinator.** A law for the server track's
`lessor.Revoke` (CLAUDE.md's Package APIs: a client needing a fact of a sealed predicate gets a law,
the predicate stays sealed): `mvccBackend_isBackend.law : mvccBackend γ q B Pk ⊢ ∃ gx, □
backend.isBackend B.γB B.P (mvccW gx) Pk B.b` (the backend share's backend open at the store's
write invariant). Immediate from `mvccBackend`'s body (`isBackend d.γB d.P (mvccW d.gx) Pk d.be`,
`B = ⟨d.γB, d.P, d.be⟩`); its proof, `mvccBackend_isBackend.law_holds` (`Api/SnapLaws.lean`), lands
with the mvcc track's next commit (the snapshot image's tracking).
