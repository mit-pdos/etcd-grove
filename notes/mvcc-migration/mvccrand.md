# mvcc's randomized tester (`examples/mvccrand`) over mvcc's frozen API: hand-off

Branch `mvcc-api`. The task (the coordinator, 2026-11-05): specs and proofs of the tester's
functions over the frozen API (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`,
`ApiState.lean`), its top-level result, and every API statement too weak for a check it makes.
The tester's design: `notes/mvccrand.md`. Files: `Spec/github_com/mit_pdos/etcd_grove/examples/
mvccrand/`, `Proof/github_com/mit_pdos/etcd_grove/examples/mvccrand/`.

## Done

- `Base.lean`: the package fact (`mvccrandInit`: `keys` and `extraEnds` hold read-only slices of
  `keyList`, `extraEndList`) and its `isPkgInit` instance. **For the coordinator**: the package's
  `Init.lean` (`wp_initialize'`) is `etc/gen-init.py`'s, which has no entry for `mvccrand` (its two
  variables are composite literals: a `SPECIAL` entry giving `mvccrandInit`); outside this track's
  paths.
- `check` (spec, proof), `inRange` (spec over `inRangeM`, the tester's model of a range, which is
  mvcc's `inRange` off the single-key case; proof), `rng.next` (some number), `rng.intn` (in
  `[0, n)` for `n > 0`), `checkKV` (returns when the key-value is the model's record, `kvMatches`;
  the struct's points-to kept by the call, the slices given back). All proved, no `sorry`.
- `Model.lean` (pure): the tester's maps against mvcc's states (`stMatch`, `kvOfRec`), and the
  probe of the read contract, **`answers_keys_eq_match`** (proved): for a log with `txn.LogOk`
  (which `Txn.Range.contract`'s `LogWf'` and change-count facts give, `txn.LogOk.of_cert`), the
  keys `rangeAnswers` answers at a revision, through which `rangeOutcomeC` gives the count, the
  limit's cut and the key-values in order, are exactly `checkRange`'s `match` (the tester's keys in
  its order, in its map and in the range). Imports txn's `Lemmas` (`rangeAnswers_keys`), which
  imports only mvcc's `ApiState`. And `covers_eq_inRangeM` (proved): the range `Watch`
  registers (`watchRangeOf`, its affine `covers`, through which `wsRecvOk` selects a watcher's
  events) is the tester's `inRange` for non-empty keys.
- `rng.genRange` (the request: a key of `keyList`, `genEnd`'s end, revision in `[-1, cur + 1]`,
  limit in `[0, 4)`): spec and proof (2026-11-06).
- `rng.genKey` (a fresh byte slice of a key of `keyList`) and `rng.genEnd` (`nil`, `[]byte{}`, an
  extra end or a key; its contents `[]` when `nil`): specs and proofs (2026-11-06).
- `checkRange` (2026-11-06): spec and proof, no `sorry`. **Every check of a range read is proved
  from `Txn.Range.contract`'s outcome** (at compaction revision `-1`, `res ≠ null`), the
  `errVars.law` (G2's fix) for `err == ErrFutureRev`, and `txn.LogOk` of the read log: the future
  arm; `err == nil`, `Rev == cur`; the match loop (`matchKeys`, `answers_keys_eq_match`); the
  count-only count; `taken`/`total` against `rangeTaken`/`rangeTotal` (`takenOf`, `totalOfT`,
  `takeLimit_length_takenOf`, `totalOf_eq`, through txn's `rangeTotal_stateAt`,
  `rangeAnswers_length`, `rangeTaken_eq`); and each key-value through `checkKV` (`rangeKvs`'
  elements, `kvPtrIs` and `stMatch`, `kv_of_find`, `taken_keys`). Callee hypotheses: `check`,
  `inRange`, `checkKV`'s specs, `errVars.law`.

- 2026-11-06 (second session): `copyState` (a fresh map with the state's contents), `pending.put`,
  `pending.del` (over `Pending.lean`: the pending transaction as one record `PendM` and its
  ownership `ownPending`; `PendM.put` by `putRec`, `PendM.del` deleting `matchKeys` in key order,
  `delAll`), `itoa` (`itoaM`: the decimal digits, `decDigits`), `watcher.advance` (`watcher.adv`),
  `noCluster.Version` (`nil`; for `lease.clusterOk`): specs and proofs, no `sorry`.
- **The history** (`History.lean`): what `h.mu` guards (`histR h γ q`, fractional: the two slice
  fields, half of the ghost cells `γ.g` at the slices and their contents, half of the revisions'
  monotone list `γ.l`, and persistently every map and change slice, `statesP`, `changesP`); the
  writer's other halves and the slices' capacities (`histW γ Hs`); a thread's handle (`histRd`:
  `isHistory`, the guard and `aboveFloor`'s invariant, with one of the lock's reader slots, its own:
  not a thread pool, because a reader calls `snapshot` inside an mvcc transaction, which holds its
  thread token). `history.snapshot` (the maps of revisions `Hs ⊒ Hlb`, any lower bound the caller
  held, and `Hs`'s lower bound; the writer gets `Hs` exactly from `histW_lb` and its half),
  `history.appendRev` (the writer's append, the map and changes persistent), `history.changesAt`
  (a revision of a lower bound: its changes), `history.seen` (both checks from a lower bound
  past `cur`): specs and proofs, no `sorry`. `newHistory`: spec only (the raw fields and the
  writer's part; `Run`/`runChecks` makes the guarded lock). Its proof needs a WP of the slice
  literal of map literals `[]map[string]kvRec{{}, {}}` (Perennial has `composite_literal_map`'s
  semantics but no WP lemma for a map literal inside an array literal): not attempted.
- `WriteModel.lean` (pure, the probe of the write contracts): `stMatch_put` (`putRec` is
  `putKv`'s key-value), `stMatch_del`, `delKeys_eq_match` (`Txn.DeleteRange.contract`'s `delKeys`
  are `pending.del`'s `matchKeys`, for `txn.LogOk` of the pending log): proved.
- `World.lean`: the tester's invariant (`worldInv`) and the writer's idle state (`writerIdle`), as
  designed below (`Change`, `MvccState` countable, for the ghost variable of the state).
- `writer.cur` (the published revision, the writer's exactly: `γ.pv`), `writer.checkHook` (over the
  writer's own `saved`), `writer.newVal`, `writer.begin` (the snapshot is the writer's revisions
  exactly; the pending model `⟨len, lastSt Hs, []⟩`): specs and proofs, no `sorry`. The writer's
  struct is taken at a fraction (`w ↦{dq} wv`, its fields split and recombined in the proofs,
  `iStructNamedSuffix`): `runChecks`' register goroutine reads `w.ticks` concurrently; a writer
  method that writes a field (`newVal`'s `vals`, `grant`'s `nextID`) takes it whole today
  (`newVal.spec`), which `runChecks` must reconcile (split the struct: `ticks` read-only).

## The checks against the API (2026-11-05, by reading; each to be proved)

Every check the tester makes of mvcc, the API statement that justifies it, and the client-side
argument (all over one invariant holding `mvccState γ σ`, the stream's `wsState ι S`, the history's
ghost copy and the published revision; `σ.crev = -1` throughout: the tester never compacts, and
only `Compact`/`Restore` move it).

| Check (Go) | Justified by |
|---|---|
| `kv.Rev() == 1` after `New` | `New.spec` (`mvccState γ mvccStart`), `KV.Rev.contract` |
| writer: `tw.Rev() == p.rev-1`, `tw.Rev() == cur` (txn) | `KV.Write.contract` (the update at `σ`, nothing pending), `Txn.Rev.contract`; the writer is the only one stepping `σ` (the invariant's half of the log) |
| writer: `checkHook(i)` after `Write` | `hookRun P f Pre Q` with the tester's closure's triple (`Pre`: `applying ↦ i`, `saved ↦ s ≤ i`), `Q` back in `Write`'s post |
| `tw.Put(...) == p.rev` | `Txn.Put.contract` (`W64 σ.log.length`) |
| `tw.DeleteRange`: count, revision | `Txn.DeleteRange.contract` (`ds`, `writeRev`); `delKeys` in key order = the tester's `keys` order |
| `len(tw.Changes()) > 0` iff the model's | `Txn.Changes.contract` (`k.pend.length`, `0 ≤ sint.Z`) |
| `kv.Rev() == want` after `End`, then publish | `Txn.End.contract`'s two updates (`σ.notify pend`, `commitPending`), `KV.Rev.contract` |
| readers: `floor <= cur`, `cur < len(history)` (`seen`) | `KV.Read.contract`/`KV.Rev.contract`: the update fires at the invariant's `σ`, `published ≤ σ.rev < σ.log.length ≤ len(states)` (the writer appends before `End`, publishes after) |
| `tr.FirstRev() == -1` | `Txn.FirstRev.contract` (`W64 σ.crev`), `σ.crev = -1` |
| `checkRange`: `ErrFutureRev`, `Count == -1`, `Rev`, no key-values | `Txn.Range.contract`'s `rangeOutcomeC` at `c = -1` (`rangeOutcomeC_neg`): the future arm |
| `checkRange`: `err == nil`, `Rev == cur` | the third arm; the context-error arm is excluded by `todo = true → r ≠ null` (`rangeCtx true` of `context.TODO()`) |
| `checkRange`: `Count` (count-only, limit, total) | `rangeAnswers`/`rangeTotal` at `stateAt`, through txn's `rangeAnswers_stateAt`, `rangeTotal_stateAt` (need `LogOk`: the contract's `LogWf'` and change-count facts, gap A of txn's track) |
| `checkKV`: key, create/mod revision, version, value, lease; keys-only: no value | `rangeKvs`/`kvPtrIs` (full: every field; keys-only: `Value' := slice.nil`) at `stateAt`, the tester's `kvRec` the client model's `putKv` |
| read-only txn: `tw.Rev() == cur && len(tw.Changes()) == 0` | `NewReadOnlyTxnWrite.spec`, `Txn.Rev`, `Txn.Changes` (`.read`: no pending) |
| `GetLease(k) == lease` | `isLessor`'s/`lessor.GetLease.spec` over `leaseOwn γl L (pendItems σ.log [])` = `leaseItemsOf (stateAfter σ.log)` (`pendItems_nil`) |
| `Watch`: empty range fails with `ErrEmptyWatcherRange`, `-1`; else no error | `WatchStream.Watch.contract`: its first arm exactly the empty range (`e ≠ [] ∧ ¬ GoStringLt kk e`), the second at an open stream `nil` (the tester's stream is open until the end: `S.closed = false` in the invariant). (`notes/mvccrand.md`'s first obstruction is gone.) |
| `receive`: `CompactRevision == 0` | `wsRecvOk` part 1 (`compactRev ≠ 0 → 0 < compactRev ≤ σ.crev = -1`) through `wsRecv_ok.law` |
| `receive`: a progress response's revision written | part 1 (`compactRev = 0 → rev < σ.notifiedLog.length ≤ len(states)`) |
| `receive`: a watcher's progress after its changes up to `P` | part 3 (`r.id = id`), `onceUpTo` vacuous at `σ.crev = -1` |
| `receive`: an event's watcher known, `r <= resp.Revision`, the next expected change, its type and fields | part 1 (a `-1` response has no events; an id the stream has, `c.watchers` = `S.ws`'s domain under `c.mu`), part 2 (`recvEvs = watchEvents …`: the events exactly the range's changes from `lo`, in order), `evIs`/`kvPtrFixed` (all fields), `evOfKv` (a delete: `zeroKv` at the revision) |
| `kv.Close() == nil` | `KV.Close.contract` (`RET nil`) |

So for every check of mvcc itself the frozen contracts are exact enough. What blocks is below.

## Found: API statements too weak for the tester

**G1 (blocking every write; found 2026-11-05). `backendRest` is opaque (`iprop(True)`) with no
law.** `Api.lean`:

```
opaque backendRest (γB : backend.BNames) (P : backend.BParams) (K : backend.BNames → IProp GF)
  (b : Loc) (D : backend.Data) : IProp GF := iprop(True)
```

`mvccBackendFor_open.law` consumes the whole `backend.newPostKP γB P (fun _ => mvccW gx) Pk K b D`
(which holds `plHook γB func.nil`, `rbOwn γB (rbData P D)`, `K γB`, `isStopChans γB b`,
`rdPool γB P b`) and gives back only `mvccBackendFor … ∗ backendRest γB P K b D`, from which no law
gets anything. So after the law:

- the client has no `plHook γB f`, so it can neither call `SetTxPostLockInsideApplyHook` (its spec
  takes `plHook γ f`) nor freeze the hook (`plHookRO`): **no `hookIs B f` for any `f`, so no
  `KV.Write.contract` (hence no `Put`, `DeleteRange`, `Txn` write, `checkHook`), no lease
  `Revoke`/`Grant` (they take `hookIs B f`)**. The tester sets its hook after `mvcc.New`, as the
  server does (`getTxPostLockInsideApplyHook`);
- it has no `rbOwn`, so no `rbPart γB S r` for `lease.NewLessor.spec` (the tester and the server
  call `NewLessor` between `backend.New` and `mvcc.New`; the law cannot be applied after
  `NewLessor` either: `NewLessor` gives back `rbOwnIn γB S (r.insert "lease" ∅)`, not the
  `rbOwn γB (rbData P D)` `newPostKP` needs), nor the lease bucket's part for `Grant`/`Revoke`;
- `K γB` (the client's write-back tokens and open token, which `NewLessor`'s `wbTok`/`bOpen`, the
  hook's `wbTok` need) is lost too, unless split off before (it is inside `newPostKP` as well).

The docstring already says what `backendRest` holds ("its stop channels, its hook's exclusive half
at `nil` (to set, or to freeze at `nil`), its other buckets' rights …, the reader pool, and `K`").
**Minimal strengthening**: define it (transparent, `@[expose]`) as what `newPostKP` has beyond the
store's part, or add the law

```
abbrev backendRest_open.law : Prop :=
  ∀ γB P K b D, backendRest (GF := GF) γB P K b D ⊢
    backend.isStopChans γB b ∗ K γB ∗ backend.plHook γB func.nil ∗
    backend.rbOwn γB (backend.rbData P D) ∗ backend.rdPool γB P b
```

(the tester needs the first four. The server's boot, which also sets the hook and makes the lessor
after `backend.New`, would need the same of its `bootBackend.law`'s `backendRest`; not checked.)

**G2 (latent: holds today only through mvcc's internals; found 2026-11-05). The API states no fact
of mvcc's error variables' values, which a client's `==` on them needs.** The contracts give an error
as `globalAddr ErrFutureRev ↦□ err` (`rangeOutcome`'s future arm), `globalAddr ErrEmptyWatcherRange
↦□ err` (`WatchStream.Watch.contract`), `ErrCompacted`, `ErrWatcherNotExist`. The tester compares
(`err == mvcc.ErrFutureRev` in `checkRange`, `err == mvcc.ErrEmptyWatcherRange` in `register`), and
Go's interface `==` panics on a non-comparable dynamic type (Perennial's `go_eq_interface`:
`CheckComparable i1.ty`), so the proof needs the variables' dynamic type. Today it unfolds
`isPkgInit mvcc` to `mvccInit` (`isPkgInit_access`; `errorsNewVar`: an `*errors.errorString`), as
the migrated server does (`applierV3backend__Compaction.lean`, `DispatchKVL.lean`): `mvccInit` is in
mvcc's `Base.lean`, in `etc/api/mvcc.txt`'s debt group, so sealing `isPkgInit mvcc` breaks every
such client. **Minimal strengthening**: a law in `Api.lean`, e.g.
`errVars.law : isPkgInit mvcc ⊢ errorsNewVar ErrCompacted "…" ∗ errorsNewVar ErrFutureRev "…" ∗
errorsNewVar ErrEmptyWatcherRange "…"` (or a weaker `∃ x, globalAddr X ↦□ interface.mkOk
(PointerType errorString.ty) #x` per variable; `ErrWatcherNotExist`, which `Cancel` returns, has
no such fact even in `mvccInit`, only `∃ e, globalAddr … ↦□ ok e`).

**G1 and G2: fixed** (the coordinator, `87873f7d8f`, 2026-11-06): `backendRest_open.law` (the stop
channels, `K`, `plHook γB nil`, `rbOwn`, `rdPool`), `errVars.law` (`errorsNewVar` of `ErrCompacted`,
`ErrFutureRev`, `ErrEmptyWatcherRange`). `checkRange`'s proof takes `errVars.law` as a hypothesis.

## The three blockers: decided (the user, 2026-11-06, `3b3d1cd92b`)

- **`NewLessor`'s cluster**: the tester passes `noCluster{}`, whose `Version()` returns `nil`
  (`noCluster.Version.spec`, proved): `lease.clusterOk (interface.mkOk noCluster.ty #noCluster.mk)`
  follows from it (its `□` triple), so `lease.NewLessor.spec` applies unchanged.
- **`backend.New`'s panic**: the result is "every check passes, unless `backend.New` panics", its
  panic disjunct carried through `runChecks`' post; no extra premise.
- **`be.Close()`/`le.Stop()`**: `Run` is now `r, le, be := runChecks(cfg); le.Stop();
  check(be.Close() == nil, …); return r`; `runChecks` is the old body up to `check(kv.Close() ==
  nil, …)`, returning `(Report, lease.Lessor, backend.Backend)`. The theorem is about `runChecks`;
  `Run`'s tail is unverified.

So `runChecks`, its spec and the top-level result are unblocked, with the configuration bounds as
premises (`0 ≤ Watchers`, `0 ≤ Readers`, `Ops < 2 ^ 62`, and the readers' count against the
history's reader slots: `runChecks` deals one `histRd` to each of its `Readers + 2` history users,
the writer, the receiver and each reader, from `init_RWMutex`'s `actualMaxReaders` slots, so
`Readers + 2 ≤ actualMaxReaders` is needed, implied by the thread bound when `threadBound ≤
actualMaxReaders`; to state without `actualMaxReaders` in a Spec file, `etc/bounds-check.py`'s
`spec-readers`), and the closed theorem's Iris premises (`fileHolds "mvccrand.db" D` fresh,
`keySized`, `ckptEffectsOk`). `etc/gen-init.py`'s entry for `mvccrand` (below) is needed then.

The earlier analysis of what each blocker cost (before the decision) is superseded; in short: no
result past `NewLessor` without the stub; the panic only in `backend.New`'s arm; no triple reached
`Run`'s end without the split.

## The invariants (designed; `World.lean`, `History.lean`)

- **The world** (`worldInv h γ`, invariant `worldN`): `mvccState γ.kv σ` with half of a ghost
  variable `γ.σ` at `σ` (the writer holds the other half: only its updates change `σ`; the
  readers' `Read`/`Rev`/`Range` updates and the registrar's `Watch` update commit it unchanged),
  `wsState γ.ws S` with half of the registry `γ.reg` (a ghost map id ↦ `*watcher`, the other half
  in `c.mu`'s lock; its domain is `S.ws`'s), `h.published`'s cell `p` with half of `γ.pv` (the
  writer's other half) and the monotone `γ.pub`, a lower bound `Hl` of the history's revisions;
  pure: `σ.crev = -1`, `1 ≤ p ≤ σ.rev`, `histOkM σ Hl` (the notified history's revisions are in
  `Hl`, each state matched by `stMatch`). (`StreamState` holds filter functions, so it cannot be a
  ghost variable: the registry ghost map is what `c.mu` shares of it.)
- **The writer between transactions** (`writerIdle γ σ Hs`): its halves, `histW γ.h Hs`, `σ`
  with nothing pending, `Hs.length = σ.log.length`, every revision's state matched, `p = σ.rev`.
  Still to add: its mvcc backend share and `hookIs`, the lessor's `leaseOwn (mvccLeases γ) L I`
  with `I = pendItems σ.log []` and the model's live leases `L`, `applying`/`saved` (owned by the
  writer: the hook's triple, `hookRun P f Pre Q` with `Pre := applying ↦ i ∗ saved ↦ s ∗ ⌜s ≤ i⌝`,
  `Q := P ∗ applying ↦ i ∗ saved ↦ i`, is proved in `runChecks` for its closure), its `rng`, its
  struct, the ticks channel's sender.
- **Inside a write transaction**: `mvccTxn tw γ trace (.write σ pend)` and the writer's
  `ownPending p P` with `P.rev = W64 σ.log.length`, `stMatch P.st (applyChanges (W64
  σ.log.length) (stateAfter σ.log) pend)` (by `stMatch_put`/`stMatch_del` at each op), the
  changes `P.chs` the tester's view of `pend`, and `txn.LogOk (σ.log ++ [pend])` (puts keep it;
  `Txn.DeleteRange.contract` gives it); `writer.end` appends `(P.st, P.chs)` (made persistent) and
  then runs `End`, whose notify step is where `histOkM` needs the appended revision.
- **`c.mu`'s lock**: `c.watchers ↦$ W'` with the registry's other half at the same domain, each
  watcher's struct and its position against what the receiver got (a ghost copy of the received
  responses, half here, half with the receiver's `wsRecv`); `c.events`.
- **The ticks**: the channel's values `≥ 1` (published revisions), for `register`'s `intn(pub+1)`.

## Left

**Proved, no `sorry`** (2026-11-06/07, third session; the writer's shared definitions in
`Writer.lean`: `writerRO` (the struct's fields written once, persistent; `vals`, `nextID` the
writer's), `writerCtx` (persistent context), `writerOwn` (between operations), `hookPre`/`hookPost`/
`hookOk` (the tester's hook's triple), `pendOk` over `pendOf` (`Pending.lean`: the tester's model of a
revision's changes, which `World.lean`'s `revOk` requires of every revision of the history, so the
watch path can read a revision's changes as mvcc's events), `endCb` (`end`'s callback), `histAfter`,
`commitSt`, `viewSt`/`viewDq`/`viewRev`; `TxnEnd.lean`'s `endCb_txnEnd`, `tw.End` as the callback, both
of `End`'s updates at the tester's invariant; `WriteLemmas.lean`; `WriterLease.lean`'s `writerLe`;
`WriterRun.lean`'s ticks channel, Perennial's single-producer channel `isSpsc` with `tickP`: a
published revision `≥ 1` with a lower bound of `γ.pub`): every `writer.*` (`cur`, `begin`, `view`,
`end`, `checkHook`, `newVal`, `genLease`, `put`, `deleteRange`, `writeOp`, `read`, `grant`,
`checkLeases`, `txn`, `revoke`, `run`), `reader` (`reader_au`: `Rev`'s and `Read`'s update at the
invariant gives the floor at most the revision and the history's lower bound covering it),
`watchCheck.expect` (`WatchModel.lean`: the correspondence of mvcc's `watchEvents` with the history's
changes in range), `newHistory` (over a local `wp_slice_literal_ex`). `history.snapshot`'s post now
also gives the snapshot's capacity (its length), which `view`'s `append` needs.

**Found: a lessor spec too weak for the tester (blocks `runChecks` with more than one `Grant`;
not mvcc's API).** `lease.NewLessor.spec` gives the lessor's backend contract as `lessorApplyOk lp`
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/SnapRO.lean`):
```
def lessorApplyOk (lp : Loc) : IProp GF :=
  iprop(□ ∀ (d : mvcc.KBReal) (W Pk : IProp GF) (f : GoFunc) (RW : IProp GF),
    backend.isBackend d.γB d.P W Pk d.be -∗ backend.plHookRO d.γB f -∗ ⌜f ≠ func.nil⌝ -∗
    rwLens RW (lease.lessorBeOn lp d.be) -∗
    lease.lessorBackend lp Pk #f iprop(backend.wbTok d.γB ∗ RW) (apply.bkRT d)
      (backend.rbPart d.γB (· = go!"lease")))
```
and `lease.lessor.Grant.spec` consumes the write token `T` (`wbTok ∗ RW`) and gives back only `R`.
`RW` must lend the user's half of `le.b` (`lessorBeOn`, exclusive), so a client holding it once (the
tester: `NewLessor`'s post) can make one `T`: one `Grant`, and no `Revoke` (which takes `lessorBeOn`)
after it. The server makes a fresh `RW` per apply from its write right (`srvRestRWH`), so it is not
hit. The Go check: `grant`'s `err == nil` (and every later `revoke`'s), run up to `Ops` times.
**Minimal strengthening**: `lessorBackend`'s write gives the lens's `lessorBeOn` back with `R` (the
write lends it, `Grant`'s post returns it), so `T := wbTok` (one write-back token per write) suffices.
`writer.run.spec` takes `ops ≤ k` tokens `T` abstractly (`writerLe`), so only `runChecks` meets it.

**Found: `WatchStream.Watch.contract` too weak for the tester's `Watch(context.TODO(), …)`
(2026-11-07; mvcc's API).** The contract's precondition takes `context.isContext ctx cd`:
```
  isPkgInit mvcc ∗ isMvccWatchStream (interface.mkOk ty v) γ ι ∗ threadTok ∗
    context.isContext ctx cd ∗ ownSlice key kk DFrac.discard ∗ … ∗ au -∗ …
```
and `register` calls `ws.Watch(context.TODO(), 0, w.key, w.end, start)` (as etcd's `v3rpc` watch
server does with its stream's context); `context.TODO()`'s value (`todoCtxVal`) is no `isContext`
(its `Done()` is `nil`). `watchStream.Watch` uses `ctx` only for `trace.SpanFromContext(ctx)` (a
`Value` lookup, which `todoCtx` answers `nil`). **Minimal strengthening**, as `KV.Compact`'s internal
`InvCompact.lean` already does: `(⌜ctx = todoCtxVal⌝ ∨ context.isContext ctx cd)` in place of
`context.isContext ctx cd` (or `KV.Range`'s `rangeCtx`). The tester's proof of `register` has the two
side goals `context.isContext todoCtxVal cd` as the only placeholders:
`watchCheck__register.lean`, two `sorry -- M1-REPLACE: WatchStream.Watch.contract's isContext excludes
context.TODO()`; each becomes `ileft; ipureintro; rfl` after the fix.

`watchCheck.register` (2026-11-07): spec and proof over those two placeholders: the ticks loop (the
`isSpsc` consumer end), the start revision in `[1, pub + 1]`, the empty range's
`ErrEmptyWatcherRange` and `-1`, a non-empty range's `nil` (the stream open: `γ.cl`, `World.lean`, the
invariant's half of the stream's closed flag, `register`'s half at `false`; `runChecks` sets both to
`true` before `ws.Close()`), the watcher in the registry and `c.watchers`, its position at 0 events
(`recvEvs_fresh`). `regOk` now lets an id outside the registry be a watcher covering no key (the empty
range's update, handed back unconsumed, must be committable with no resources); `receive` over it
(`recvEvs_uncovered`).

**Still to do**:
- `watchCheck.receive`, `complete`: proved (`6c1e217111`; `WatchLock.lean`, `c.mu`'s invariant
  `cmuInv` with `rcvKnown`; `World.lean`'s registry `regOk`, the registration `RegInfo`, `γ.rcv`).
- `runChecks` (spec: the configuration bounds; post: the report, or `backend.New`'s panic): blocked for
  more than one grant by the lessor finding above. Then `Main`, `Link.lean`, `Results.lean`.
- **For the coordinator, `etc/gen-init.py`'s entry for `mvccrand`**: needed only for the closed
  theorem (`Init.lean`'s `wp_initialize'`, then `PkgTable.lean`). The fact is `Base.lean`'s
  `mvccrandInit`: `keys` and `extraEnds` each hold a read-only slice of their literal (`keyList`,
  `extraEndList`), so the initializer's two composite-literal stores must be persisted
  (`ownSlice_persist`) into it; imports: context, sort, sync, sync/atomic, time, zap, mvccpb,
  traceutil, lease, backend, mvcc, semver.
- Perennial (for the coordinator's `notes/perennial-changes.md`): `isSpsc` keeps its invariant at
  `nroot` (a caller with another invariant open cannot send); no `chan.wp_len` wrapper (as
  `chan.wp_cap`); the slice literal of map literals needed a local `wp_slice_literal_ex`.
- Placeholders (`M1-REPLACE`): the two in `watchCheck__register.lean` above, nothing else.
