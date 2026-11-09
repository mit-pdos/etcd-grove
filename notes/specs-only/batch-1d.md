# Batch 1d: `client/v3/concurrency` (Session, Mutex, Election, STM)

Author's report (2026-11-09). Builds: `etc/specs-build.sh --dir Spec/go_etcd_io/etcd/client/v3/concurrency`
(63 modules, OK, against W0's round-1 names: `ctxPrin`, the context specs, `OpResp.range rev`).
Snippets: `cd examples && go vet ./specreq/concurrency/` (clean, gofmt-clean).

## Files

- `Spec/go_etcd_io/etcd/client/v3/concurrency/Api.lean`: the vocabulary (namespace `Concurrency`).
- 62 spec files, one per function of `session.go`, `key.go`, `mutex.go`, `election.go`, `stm.go`
  (every function with an old spec; none left out): `NewSession`, `Session__{Client,Lease,Ctx,Done,
  Orphan,Close}`, `With{TTL,Lease,Context}`; `waitDelete`, `waitDeletes`; `NewMutex`, `NewLocker`,
  `Mutex__{Lock,TryLock,Unlock,IsOwner,Key,Header,tryAcquire}`, `lockerMutex__{Lock,Unlock}`;
  `NewElection`, `ResumeElection`, `Election__{Campaign,Proclaim,Resign,Leader,Observe,observe,
  Key,Rev,Header}`; `NewSTM`, `NewSTM{Repeatable,Serializable,ReadCommitted}`,
  `With{Isolation,AbortContext,Prefetch}`, `mkSTM`, `runSTM`, `stm__{Get,Put,Del,Rev,fetch,commit,
  reset}`, `stmSerializable__{Get,Rev,gets,commit}`, `readSet__{add,first,cmps}`,
  `writeSet__{get,cmps,puts}`, `isKeyCurrent`, `respToValue`.
- `examples/specreq/concurrency/{session,mutex,election,stm}.go`: 20 snippets (`ReqSessionLease`,
  `ReqSessionResumeLease`, `ReqSessionDone`, `ReqSessionClose`, `ReqSessionTTL`; `ReqFencedWrite`,
  `ReqV3LockPattern`, `ReqTryLock`, `ReqLockUnlock`, `ReqLocker`; `ReqCampaignProclaim`,
  `ReqResumedProclaim`, `ReqLeader`, `ReqLeaderFenced`, `ReqObserve`; `ReqSTMTransfer`,
  `ReqSTMLevels`, `ReqSTMRepeatable`, `ReqSTMPrefetch`, `ReqSTMAbort`).

## Users found

`server/etcdserver/api/v3lock` (Mutex over a resumed, orphaned session; key and header returned),
`v3election` (Campaign/Proclaim/Resign/Leader/Observe, resumed elections, lease `-1` sessions),
`client/leasing` (a session per monitor round, `Done` in selects, `Lease`), `server/proxy/grpcproxy`
(`WithTTL`, `Lease` on an endpoint key, `Done`, `Close`), recipes (`Client`, `Lease`), etcd's
integration tests (`tests/integration/clientv3/concurrency/*`). Kubernetes does not use the package
(its leader election is over its own API); `examples/` neither. etcdctl's `lock`/`elect` commands
are not in the pinned sources.

## The design (what the user should know)

**No time model, so revisions.** A session promises a lease that was granted (or the one named),
never that it is alive. The mutex's guarantee is the **fence**: `Lock` returns `lockedSince pfx k c
σ` (at a reached state `σ`, nothing under the prefix is older than `c`, the key present with create
revision `≥ c`), and the pure law `fence` turns it into `holdsAt` (the key is the oldest under the
prefix) at **every later state where the key still has create revision `c`** — exactly the states
where a `Txn(If(m.IsOwner()))` succeeds. This holds even with `Lock`'s known gap
(`issues/mutex-lock-recreated.md`): the old `lockedAt ∨ keyRecreated` disjunction is gone. Election:
the same fact from `Campaign` (`waitedFor`, without presence: `nonissues/election-campaign-key-check.md`),
fenced `Proclaim`/`Resign` saying whether the fence held, `Leader` a linearized `holdsAt`, `Observe`
values each written by the oldest key at its revision (`ObservedAt`), in header order. STM:
`stmCommitted` — the committed attempt's writes applied in one revision at `σ`, and (all levels but
`ReadCommitted`) every read is `σ`'s key-value (serializability), except a `RepeatableReads` attempt
that wrote nothing, checked by a serializable (stale) transaction: its reads agree with a past
revision; `SerializableSnapshot` adds that no written key changed after any read's header.

**The permission `etcdPerm γ T`.** The package makes many requests per call; the caller hands each
function a persistent atomic update performing any transition in its own relation `T`, and each spec
requires the transitions it may cause, stated in the model (`keysEff`: a key under the prefix put
with the session's lease or deleted; `grantEff`, `revokeEff`; `stmEff`: a committed attempt
satisfying the closure's relation; `readEff`), to be in `T`. Facts come back as `etcdLb` of states
with pure predicates. W0's `envUpd` shape, for the package's own requests.

**The STM's closure** (`applyOk apply γ who F Rel`): on any STM (`stmAt`, whose methods are the law
`stmAt_methods`), the closure returns an error or `nil` with an attempt satisfying `Rel`, or aborts
through a method; it keeps a caller's frame `F` indexed by the attempt (captured variables reflect
what the attempt read), given back on every outcome.

## Exported vocabulary (one line each)

Pure: `recOf`; `noOlder pfx c s` (no key under `pfx` older than `c`); `holdsAt pfx k c s` (`k`,
created at `c`, the oldest); `firstCreate` (a `WithFirstCreate` get's answer); `waitedFor` (the
wait's fact at a state); `lockedSince` (the lock fact); `ObservedAt` (an observed leader value);
`putKey`, `delKey`, `readEff`, `keysEff`, `grantEff`, `revokeEff`, `effIn`; `SessOpts` and its
options' models; `STMOpts` and its options' models, `isoSS/S/RR/RC`, `isoValid`; `ReadM`, `WriteM`,
`Attempt`, `readOf`, `readsAgree`, `readsSeen`, `applied`, `stmCommitted`, `stmEff`, `GetPost`,
`RevPost`; `MutexSt` (`init`, `released`), `ElectionSt`, `ownerCmp`; `ConcErr`, `concErrVal`.
Internal pure: `curCmp`, `writeCmp`, `addReads`, `respReads`, `keysOf`.

Resources: `etcdPerm γ T` (def, persistent); `isSession s γ who id` (persistent); `sessOptAt`/
`sessOptsAt`, `stmOptAt`/`stmOptsAt`; `optCtxOk o who` (def); `isMutex m s pfx` (persistent),
`mutexSt m st`; `isElection e s pfx` (persistent), `electionSt e st`; `observeAt ch γ pfx R` (the
observer's consumer); `stmAt iv γ who iso a`, `stmStale iv γ who iso`; `stmRet` (def: a return or the
STM's abort); `applyOk` (def); `stmResult` (def: `NewSTM`'s outcome). Internal: `observeProd`,
`stmCoreAt`, `stmCoreStale`, `stmSerAt`, `stmSerStale`, `readSetAt`, `writeSetAt`, `readRespAt`.

Laws: `fence` (pure: the fencing guarantee); `concErrVal_ok` (non-nil, injective, not `errVal`);
`init.spec` (the five error globals); `handles_persistent`; `isSession_client` (non-null, the client
`isClient`, the lease field); `sessOptAt_call`, `stmOptAt_call`; `electionSt_session` (the leader
session is `nil` or the election's); `observeAt_recv`; `stmAt_methods` (`Get`, `Put`, `Rev`, `Del`,
`commit`, `reset` as `STM.*Triple`); `applyOk_persistent`.

## Main changes from the old specs

- Every spec over W0's cluster model (`etcdLb`, `State`, `Step` through `etcdPerm`) instead of the
  old `etcdReached`, `lockedAt`, `acquireResp`, `proclaimedAt`, `stmOutcome` and the
  `isEtcd*Client` contracts.
- Relaxed: any context (`ctxOk`, `ctxPrin`), not only Perennial's cancelable ones; any client
  (`isClient`), auth on or off, leases expiring any time, compaction (watch and read errors are
  errors); constructors (`NewMutex`, `NewElection`, `NewLocker`) take no client premise and no
  prefix-length bound; no STM size bounds (`stmKeyMax`/`stmCallMax`: a too-large request is a
  refusal in W0's model).
- Restated: `Lock`'s `lockedAt ∨ keyRecreated` and `Campaign`'s `leaderAt ∨ campaignLost` as one fact
  each with the `fence` law; `Observe`'s three cases as `ObservedAt`; the STM's closure keeps a
  frame `F` (the old one lost the caller's resources); `Session.Close` (an unfinished proof) states
  the revoke's outcome.
- Strengthened: `TryLock`'s `ErrLocked` says another key held and the mutex's key is gone.
- Thread tokens: `NewSession`, `Election.Observe`, `NewSTM*` and `runSTM` take one `threadTok` for
  the goroutine they fork (the old specs forked without).

## Functions left out

None.

## Open questions for the user

1. **Permission versus an exclusive update per operation.** The specs take a persistent permission
   (`etcdPerm`) for the package's own writes and return facts. A caller cannot then do ghost work at
   the commit of a particular request: e.g. a linearizability log of STM transactions, or of
   `Proclaim`s served by `v3election` to remote clients. An exclusive TaDa update is possible for
   `Proclaim`, `Resign`, `Unlock` and `Session.Close` (one write each), and for the STM's commit
   except for a read-only attempt (its commit is a read: W0 requires a persistent update there).
   Adding them would be a second shape beside the permission; I kept one. Your call.
2. **A client call's error versus `ErrLocked`** (`req/go_etcd_io_etcd_client_v3.md`, "from 1d", item 5):
   no law says a gRPC/etcd error is not one of `concurrency`'s `errors.New` values, so a caller
   testing `err == ErrLocked` (or `ErrSessionExpired`, `ErrElectionNoLeader`) cannot exclude a
   transport error with that value. True of the code; `ReqTryLock` assumes it.
3. **Thread tokens per session.** `NewSession`, `NewSTM`, `Observe` consume a `threadTok` for good
   (their goroutines still run after the call that could return it: `NewSession`'s keep-alive
   drainer cancels after closing `donec`). Leasing's monitor and `v3election` make a session per
   round/RPC, so a run makes at most `threadBound` of them. The bounds plan's answer would be a
   pool owned by the client; out of 1d's reach. Accept for now?
4. **`issues/mutex-lock-recreated.md`**: the spec states what the fork's code does (`lockedSince`:
   create revision `≥ c`). With the upstream fix (PR #22617) on the fork, `Lock`'s post would be
   `holdsAt` at the header's state. The fence makes the difference invisible to fenced writers.
5. **`Session.Done` carries nothing** (`Q := True`): without time, a session's end says nothing
   about its lease. Leasing's use (drop its cache when the session ends) is safe only through
   revisions, which is 1e's concern.

## `req/` sections written

- `req/go_etcd_io_etcd_client_v3.md`, "from 1d": `Client.Ctx` with `ctxPrin` and `GetLogger` (1c);
  `KeepAlive` without a thread token (1c, as written); non-decreasing watch headers along a channel
  (1b; else `observeAt_recv` drops the order); put events' `Kv` non-nil, headers owned with events
  (1b, as written); a client error never equal to `concurrency`'s values (W0/2a, open question 2).
- `req/go_etcd_io_etcd_api_v3.md`, "from 1d": `etcdLb_init` (the same as 1f's item 2): present keys
  have positive create and mod revisions.

## Answers to the requests on 1d (`req/go_etcd_io_etcd_client_v3_concurrency.md`)

- **1f**: `Session.Client.spec` (returns `isClient c γ who`) and `Session.Lease.spec` (returns `id`),
  persistent `isSession s γ who id` (the same signature as 1f's `sessionAt`): as asked.
- **1e**: `NewSession.spec` takes `sessOptsAt sl gs` (1e's `sessOptsOk osl cl` realizes as it; with
  no options, `sessOptsAt slice.nil []`), `optCtxOk` of the options' context, a `threadTok`, and
  `etcdPerm γ T` with `readEff ∨ grantEff ⊆ T` (1e's `protoUpd` must yield it: a transition-level
  permission, not a request-level one; a grant's effect is `grantEff`, the keep-alives need none).
  `Session.Lease.spec`; `Session.Done.spec` returns Perennial's `ownBroadcastChan ch γc True .Unknown`
  (persistent; blocking, `select` and non-blocking receives: `broadcast_chan_receive`,
  `ownBroadcastChan_nonblocking_receive`). The `threadTok` per `NewSession` is open question 3.

## Round 1 repairs (2026-11-09)

Reviews: `reviews/1d-provability-1.md` (F1–F8, S1–S5), `reviews/1d-completeness-1.md` (C1–C6,
S1–S8); the coordinator's decisions (the permission lent per call; drop the thread tokens). Rebuilt
(63 modules OK, against W0's round 2: its `etcdPerm`/`etcdPeek` in `State.lean`, `etcdLb_init`,
`callErr_errorsNew`); snippets re-vetted.

**Changed names (for 1e, 1f, 2e and the integration):**

| name | change |
|---|---|
| `Concurrency.etcdPerm` | **removed**: W0's `EtcdModel.etcdPerm`/`etcdPeek` (State.lean) |
| `Concurrency.etcdLent γ T P` | **new** (transparent): `etcdPeek γ` and an update performing `T` fired only by giving up the caller's token `P`, back at its commit |
| `isSession s c γ id` | **was** `isSession s γ who id`: names its client, no principal (F7, C5) |
| `Session.Client.spec` | returns the session's client `c` |
| `keysEff` | **removed**; `putEff ks vs lease`, `delEff ks`, `mutexEff pfx lease`, `campaignEff pfx val lease` |
| `observeAt ch γ pfx σ0`, `observeProd` | **was** indexed by the last header revision `R`; no order between headers (F5) |
| `observeAt_recvAu` | **new law** (C4) |
| `stmAt_reads` | **new law** (F6, S1): an attempt's reads are some reached revision's |
| `applyOk` | over attempts with no writes (F2) |
| `stmResult γ iso F Rel P σ0 resp err` | gains the token `P` (back on success) and `σ0` |
| `STM.CommitTriple` | takes `etcdLent γ T P ∗ P ∗ etcdLb γ σ0`, gives `P` back |
| `isSession_client` | the client and lease fields, `s ≠ null` (no `isClient`) |
| `concErrVal_ok` | also: each value is an `*errors.errorString`; **new** `concErrVal_notCanceled` |

**Fixes, by finding.**
- **F1/C1 (thread tokens)**: dropped from `NewSession`, `Election.Observe`, `NewSTM*`, `runSTM`
  (Perennial's `wp_fork` takes none). Open question 3 withdrawn. New snippet `ReqSessionLoop`.
- **F2 (applyOk)**: quantified over attempts without writes.
- **F3/C2 (Proclaim at revision 0)**: success is `(ownerCmp leaderKey leaderRev).holds σ.kv.store`
  (W0's `Compare.holds`), failure its negation. `nonissues/etcd-v3election-proclaim-rev-zero.md`.
- **F4/C6 (Resign's effect)**: delete only (`delEff (· = leaderKey)`); Proclaim's put only
  (`putEff (· = leaderKey) (· = val) id`); Unlock's the delete of its key; Campaign's
  `campaignEff` contains both its cleanups'.
- **F5 (Observe's order)**: dropped; `v.modRev ≤ header ≤ σ.rev` and `ObservedAt` kept. `ReqObserve`
  is now v3election's `select` loop (C4, `observeAt_recvAu`).
- **F6/S1 (the reads during an attempt)**: `stmAt_reads`; with `etcdLb_init`, `ReqSTMRepeatable` is
  provable.
- **F7 (the session's client)**: `isSession s c γ id`; `ReqSessionLease`'s check provable.
- **F8 (the permission never ends)**: the coordinator's option (a): KV writes of mutexes, elections
  and STMs take `etcdLent γ T P ∗ P` and give `P` back on every outcome whose writes were all
  answered (success, `ErrLocked`, `ErrSessionExpired`, `ErrLockReleased`, `ErrElectionNotLeader`, a
  nil leader session); the generic error disjuncts (an indefinite error may leave a write pending)
  keep it. The session's grant and revoke keep W0's persistent `etcdPerm` (repeatable calls: an
  earlier attempt may still apply after the answer). `ReqCampaignProclaim`'s assumption restated
  over the token.
- **C3 (results after the call began)**: every state-returning spec takes `etcdLb γ σ0` and returns
  `Reach σ0 σ` (`Lock`, `TryLock`, `Unlock`, `tryAcquire`, `waitDeletes`, `Campaign`, `Proclaim`,
  `Resign`, `Leader`, `Observe` through `observeAt`, `NewSession`'s grant, `Close`, `NewSTM*`,
  `runSTM`, the commits). New snippet `ReqLockAfterUnlock` (v3lock's test's header order).
- **C5 (the in-process client's principal)**: the principal is per call: mutex and election
  methods take `isClient c γ who ∗ ctxPrin ctx who`; cleanups on `client.Ctx()` run as the client's
  own principal (`Client.Ctx.spec`, 1c). Needs written in `req/go_etcd_io_etcd_client_v3.md` ("from
  1d (round 1)") and `req/go_etcd_io_etcd_server_v3_etcdserver.md` ("from 1d"). The suspected
  leftover waiter key: `nonissues/etcd-v3lock-auth-cleanup-unauthenticated.md` (unconfirmed, a test
  sketched).
- **Error identity** (open question 2 of round 0): settled by W0's `callErr_errorsNew` and
  `concErrVal_notCanceled`; `TryLock`'s and `Proclaim`'s other errors are stated distinct from the
  package's values; `ReqTryLock`'s assumption dropped.
- **Second tier**: S2 (the header and `IsOwner`'s margin: a serializable read-only fence proves
  nothing); S3 (`ReqLocker` no longer asserts `error`); S4 (Proclaim's relation, above); C-S2 (lease
  `0` never live: from `etcdLb_init`, grants never choose `0`). Not done: C-S3 (a snippet of what a
  v3lock remote client can rely on from `(Key, Header)`: 2e's contract).

**Open questions now** (replacing the round-0 list):
1. **The permission's shape** (coordinator chose lent-per-call): the alternative is one persistent
   permission for everything (round 0), simpler to give but callers then know nothing of their keys'
   contents or lease ids after a call. With `P := True` the lent one is that, so the choice only
   restricts nothing; recorded for the user.
2. **`issues/mutex-lock-recreated.md`**: unchanged (`lockedSince`: create revision `≥ c`).
3. **`Session.Done` carries nothing** (`Q := True`): unchanged.
4. **The in-process client** (C5): 1d's statements are ready for a per-call principal; W0 and 2e
   must model the in-process client (above).

## Round 3 follow-up (W0's per-call principal, 2026-11-09)

W0's round 3 renamed `ctxPrin ctx who` to `ctxPrin dflt ctx p` (`isClient c γ dflt`: the client's
default principal; the call's principal `p` from its context). 1d follows: every spec that sends
requests binds `(dflt who : Principal)`, takes `isClient c γ dflt ∗ Context.ctxOk ctx ∗ ctxPrin
dflt ctx who`, and its requests (and `stmAt iv γ who ...`) are `who`'s; `optCtxOk o dflt who` (the
options' context's principal, or `who = dflt` for the client's own context). 1c's renames
(`tokenOf`, `clientBase`, `clientRest_core`) do not occur in 1d. Rebuilt (63 modules OK), snippets
re-vetted.
