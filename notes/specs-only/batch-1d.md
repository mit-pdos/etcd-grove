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
