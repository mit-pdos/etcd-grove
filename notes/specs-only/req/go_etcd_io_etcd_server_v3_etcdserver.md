# Requirements on `go.etcd.io/etcd/server/v3/etcdserver` (2c request path, 2d apply thread and raft node, 2e bootstrap, storage, stop)

## from W0: the cluster contract

The top of the specs (`notes/specs-only/top.md`) is a client program that owns etcd's abstract state
`etcdState γ σ` (`Spec/go_etcd_io/etcd/api/v3/State.lean`) and fires it through its calls
(`client/v3/Api.lean`). Everything the server does must keep the model's promise: **every change
of the cluster's observable state is either the step of a client's request whose update the
cluster fired (`Step`) or an environment step (`EnvStep cfg`, through `envUpd γ cfg`)**. In plain
terms, what the server batches must give (statements in `top.md`, "The cluster contract"):

1. **Allocation and start (2e)**. A program that starts a new cluster of members `ms` gets
   `etcdState γ (State.init ms)` in full and one start resource per member (a ghost update the
   program runs before starting them: `|==> ∃ γ, etcdState γ (State.init ms) ∗ [∗ list] m ∈ ms,
   memberBoot γ m cfg`, 2e's vocabulary). `NewServer` of a member takes its start resource (a new
   member), or its durable state (a restart: the client-owned durable half, as raft's durable node
   API, so a restart is a fresh volatile half over it), or the persistent fact that a `MemberAdd`
   of it was answered (`etcdLb γ σ` with the member in `σ.members`: a joining member), and the
   environment's permission `envUpd γ cfg` (persistent; `cfg.autoCompact` exactly when the member's
   configuration runs an auto-compactor). No restriction to a first start, one member, auth off or
   no compaction.
   ```go
   s, err := etcdstart.StartServer(name, peerAddr, clientAddr, lg)   // examples/lib/etcdstart
   err = etcdstart.Serve(s, clientAddr)                               // servesAt γ clientAddr
   ```
   Used by: `top.md`'s story; 1c's `New` (`servesAt`).

2. **Serving (2e with 2a)**: `servesAt γ ep` once the member's gRPC server answers at `ep`
   (`req/go_etcd_io_etcd_server_v3_etcdserver_api_v3rpc.md`).

3. **The request path (2c)**: `EtcdServer.Put/Range/DeleteRange/Txn/Compact` (and the lease, auth,
   member RPCs) take the caller's update in the client's shape and fire it by `Step` with the
   discipline of `req/..._api_v3rpc.md` item 3: a write fired at most once, at its entry's commit,
   with the answer its apply computes; a request refused for a stale auth revision not fired; a
   read fired at the state it reads (the read index, then the applied state; serializable: the
   member's view). **At most once** is a cluster-level fact (2c/2d/2f): a proposal's entry is
   committed at most once (the server proposes once per call; raft forwards a proposal once;
   rafthttp never resends a message: its streams drop on failure).
   Used by: every `KV.*Triple` (the exclusive update of a write).

4. **The apply thread (2d)**: the state after the committed log is the model's: `Step` of each
   entry's request, `EnvStep` of each internal one (the lessor's `LeaseRevoke` of an expired lease:
   `EnvStep.leaseExpire`, fired through `envUpd` at its commit when the lease is live; the
   compactor's `Compact`: `EnvStep.compact`; an alarm's activation: `EnvStep.alarm`; a member's
   `publishV3`: `EnvStep.publish`); entries that change nothing observable (lease checkpoints,
   cluster version, downgrade) fire nothing. **Snapshots and restarts keep `σ`**: a member that
   restores a snapshot or replays its WAL continues the same model state (the ghost history is the
   committed log's, kept whole).
   Used by: `etcdLb_reach` (the history is one sequence of steps), the cluster contract.

5. **Durability (2d, 2e)**: an entry whose effect a client was answered is durable on a quorum
   (WAL synced before the answer's apply), so a crash of any minority, or of the whole cluster
   and a restart from disk, loses no answered step: the model has no crash transition.

6. **The laws of the anchor's resources** (2c/2d's realization of `etcdState`, `etcdLb`):
   `etcdState_timeless`, `etcdState_excl`, `etcdLb_persistent`, `etcdLb_timeless`, `etcdState_lb`,
   `etcdLb_reach`, `etcdLb_ord`, and **`etcdState_revFits`** (the current revision fits an
   `int64`: from the adequacy theorem's bound on steps, held by the cluster's invariant; no client
   spec carries a revision bound).

7. **Configuration scope** (2e's `NewServer` premises): `--max-txn-ops ≤ 4999`
   (`issues/etcd-txn-nested-depth-apply-panic.md`), `--max-request-bytes` below the bound of
   `issues/etcd-txn-keysonly-reply-alloc-panic.md`. And the client-side scope restriction W0's
   `KV.CompactTriple` takes (`rev ≠ 0`, `issues/etcd-restore-scheduled-compact-zero.md`): 2e's
   compactors never compact at `0`, which `EnvStep.compact` (`compacted < r`) already says.

8. **The model's lease, auth and membership steps** (`Model.lean`'s `leaseStep`, `authStep`,
   `clusterStep`) are W0's reading of `server/lease`, `server/auth`, `api/membership`: 3c, 3d and 2e
   check them against the code and report a mismatch to W0 (`req/` to W0) rather than proving a
   different model.

## from 1c

1. **Published members serve** (`memberServes`): `etcdLb γ σ ∗ ⌜m ∈ σ.members ∧ m.name ≠ [] ∧
   ¬ m.isLearner ∧ u ∈ m.clientURLs⌝ ⊢ servesAt γ u`: the client's auto-sync sets its endpoints to
   the published voters' client URLs. Used by: `Client.Sync.spec` (`autoSync`).
2. **`tlsPrincipal γ tls who`** (slot in `client/v3/ApiClient.lean`): with `--client-cert-auth`, a
   client certificate's common name is its principal (no token); without it, none. Introduced from
   the server's configuration and the certificate. Used by: `cfgPrincipal_tls`, `New.spec`
   (Kubernetes' TLS clients).
3. **`tokenOf γ tok u`** (3d's token providers through 2a's `Authenticate`): a token the server
   issued names the user it authenticated, for as long as the server accepts it (an expired token is
   `ErrInvalidAuthToken`, never another user). Used by: `cfgPrincipal_token`, `authReply`.

## from 1d

v3lock and v3election (2e owns their server side) call `client/v3/concurrency` over the
in-process client `v3client.New(s)`. What 1d's specs need there:

1. **A client handle valid for each RPC's principal**: `isClient c γ who` (W0's, or its
   `clientRest` with a per-call principal) for the principal `who` an RPC was authenticated as, and
   `ctxPrin rpcCtx who` for its context (the incoming metadata names `who`). 1d's
   `NewSession.spec`, `Mutex.Lock.spec`, `Election.{Campaign,Proclaim,Resign,Leader,Observe}.spec`
   take these per call (`req/go_etcd_io_etcd_client_v3.md`, "from 1d (round 1)", item 2).
2. **The handlers' permission**: 1d's mutex and election methods take a lent permission
   (`Concurrency.etcdLent γ T P` with the token `P`) whose `T` contains their effects (`mutexEff`,
   `campaignEff`, the leader key's put or delete) and the session's grant/revoke through
   `etcdPerm`. The server's invariant (or the program's, through the cluster contract) must supply
   it for every lock/election RPC: `T` the remote principal's lock and election writes, `P := True`
   (a server that serves concurrent RPCs cannot hand out an exclusive token per key).
3. **Cleanups run without a principal under auth**: `Mutex.Lock`'s and `Campaign`'s cleanups use
   `client.Ctx()` (`nonissues/etcd-v3lock-auth-cleanup-unauthenticated.md`): the handlers' specs
   cannot promise the waiter key is gone after a canceled RPC.
4. **A remote `Proclaim`/`Resign` with leader revision `0`** creates (resp. deletes nothing of) an
   absent key (`nonissues/etcd-v3election-proclaim-rev-zero.md`): 2e's handler specs inherit it
   from `Election.Proclaim.spec`'s fence, stated as the comparison.

## from 2b

Batch 2b (the gRPC watch service, `v3rpc/watch.go`) takes a started member as one slot,
**`watchMemberAt s γ`** (persistent; `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/ApiWatch.lean`):
"the `*EtcdServer` `s` is a member of the cluster `γ` whose watch path is ready". The server
batches (2c/2d/2e) produce it where a member starts (with `servesAt`'s other parts, so that 2a's
`Server` can call `NewWatchServer(s)`) and prove its laws. In plain terms:

1. **Configuration** (`watchMemberAt_cfg`, stated): `s.Cfg.Logger` (`nil` or a logger),
   `s.Cfg.MaxRequestBytes` and `s.Cfg.WatchProgressNotifyInterval` read-only (`↦□`: nothing writes
   `s.Cfg` after start; the fork's fix of `nonissues/etcd-cfg-watch-progress-interval-race.md`), the
   interval with **`watchIntervalCfgOk`** (`≤ 0`, or raised to 100ms at most about 265 years:
   `nonissues/etcd-watch-progress-interval-overflow.md`): a **configuration scope premise** of
   `NewServer` (as K8's). `(*ServerConfig).MaxRequestBytesWithOverhead()` (the config package):
   no panic.
2. **Ids**: `s.Cluster().ID()` (`api.Cluster` holding the member's `*RaftCluster`), `s.MemberID()`:
   no panic, no thread token.
3. **`s.Watchable()`**: the member's `mvcc.WatchableKV`, **whose watch streams and reads deliver the
   cluster's history** as the member applies it (`req/go_etcd_io_etcd_server_v3_storage_mvcc.md`,
   `## from 2b`, stated against `etcdLb γ σ`): the bridge from mvcc's state to `γ` (the store's
   history is the committed log's; its compaction at most the cluster's).
4. **`s` as `apply.RaftStatusGetter`**: `Term()`, `Leader()`: any values, no panic, no thread token.
5. **`s` as `v3rpc.AuthGetter`**: `AuthInfoFromCtx(ctx)` and `AuthStore()` as
   `req/go_etcd_io_etcd_server_v3_auth.md`, `## from 2b` (for a context with `srvCtxPrin ctx who`;
   the auth store's state the cluster's auth state at reached states).

Used by: `NewWatchServer.spec` (its precondition), and through `watchServerAt` every watch spec;
snippet `examples/specreq/v3rpcwatch/serve.go`.

## from 2f

Batch 2f (rafthttp: `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Api.lean`, namespace
`Rafthttp`; report `notes/specs-only/batch-2f.md`). What the transport's specs need from the server
(2d: the raft node and `Process`; 2e: `NewServer`'s transport literal, the peer listeners):

1. **A network per cluster** (`Rafthttp.net_alloc.spec`): allocated with the raft cluster `γ` and
   the meaning of a snapshot's database image (`Img i bs`, persistent: for etcd, "`bs` is a bbolt
   image of the backend holding the committed state through `i`"); `snapImg ν i bs ∗-∗ Img i bs`.
   The receiver of a `MsgSnap` gets `dbSaved ss i bs ∗ snapImg ν i bs` (`recvd`), the sender of a
   merged snapshot must give `Http.readerAt rc ... (snapImg ν i)` of its pipe's reader
   (`Rafthttp.outSnap`).
2. **The closed world of peer addresses**: every peer URL of a member (`AddPeer`, `AddRemote`,
   `UpdatePeer`, and the local `URLs` of the literal) has a host that is a `peerAddr ν a`: reserved
   once (`Rafthttp.peerAddr_reserve.spec`, or `Http.reserve` with a protocol agreeing with
   `raftProto ν` under `/raft` when the peer port also serves other endpoints) by the program
   before it starts the members; the membership invariant keeps the fact for each member's URLs
   (a `MemberAdd`/`MemberUpdate` of a URL outside the program is outside the closed world: a
   deployment premise). The member serving an address owns `Http.protoOwn a P`, which `Serve`
   takes with its listener.
3. **The server as `Raft`** (`Rafthttp.raftOk ν id ss (srv as Raft)`): `Process(ctx, m)` of a fresh
   message with `recvd ν ss m` (raft's `msgSent`, `msgCredit`; for a `MsgSnap`, its database saved)
   on a thread with its `threadTok` (etcd's reads `lgMu` and the membership under read locks),
   returning `procErr err` and the token: its `403`s (`httptypes.HTTPError`: a law `procErr` of
   such an error, whose `WriteTo` writes a status and a JSON body), else `node.Step`'s `nodeErr`
   (`Rafthttp.procErr_nodeErr.spec`); `Process` must check `To` itself (it does, `server.go:712`):
   rafthttp delivers to the member serving the URL, and `node.Step` needs `m.to = id`.
   `IsIDRemoved(x)` with a token, any boolean; `ReportUnreachable`, `ReportSnapshot` from nothing.
   ```go
   tr := &rafthttp.Transport{..., Raft: srv, Snapshotter: b.ss, ErrorC: srv.errorc} // server.go:412
   ```
4. **`Send`'s premise** (`Rafthttp.outMsg`, `sendable id m`): each message of `processMessages`'s
   output with its `msgSent`/`msgCredit` (raft's `readyEnter`/`readyCheck`), no `MsgSnap` (diverted
   to `msgSnapC`: it is), a `MsgApp` from the member's id with raft's shape (R1/R2's law requested
   in `req/go_etcd_io_raft_v3.md`, "from 2f"). Each message's memory is shared with the transport
   for good (any fraction: `readyDq`'s).
5. **The literal's fields** (`Rafthttp.trCfg`): the logger, the stats (`stats.NewServerStats`,
   `NewLeaderStats`: the transport takes the leader stats exclusively), the error channel
   (`errChanOk srv.errorc`: a `chan error` any goroutine may send on without blocking; `run`
   receives and stops on it, which is always safe), the snapshotter, an unlocked mutex. `Start`'s
   error is returned (`server.go:425`).
6. **`trRunning`**: `AddPeer` takes a share and panics after `Stop`; the server must not apply a
   conf change or a snapshot's members after `raftNode.onStop` stopped the transport (`Stop` takes
   the token whole).
7. **The merged snapshot** (`Transport.SendSnapshot.spec`): `snap.NewMessage`'s message whole
   (`snapMsgOwn`, with the right to close it, which rafthttp uses exactly once), its raft message a
   `MsgSnap` with `msgSent` (after `msgSent_replaceSnap`) and the credit.

## from 2c

Batch 2c (the request path: `v3_server.go`, `etcdserver/read/`, `pkg/{wait,idutil,notify}`) states
its specs over 2e's handle `isServer s γ` (`ApiBoot.lean`, `γ : EtcdModel.Cluster`) and its own
vocabulary (`ApiReq.lean`: `srvStep`, `srvErrOf`, `reqPrin`, `IrrBody`, `irrStep`, `applyResult`,
`SrvCallTriple`; `read/Api.lean`: `readEnv`, `readAt`; `pkg/v3/wait/Api.lean`; `idutil`, `notify`).
No shared `Api.lean` was written: 2d's `ApiApply.lean` and 2e's `ApiBoot.lean` already hold the
cluster-level and handle vocabulary, which 2c's sketches cite. What 2c's proof sketches need of the
apply thread (2d) and the lifecycle (2e), in plain terms:

1. **One name for the cluster** (2d with 2e): `isServer s γ` is over W0's `Cluster`, 2d's
   `histAt`/`answered`/`srvApplied` over `Names` (with `γ.raft`, `γ.etcd`, `γ.cfg`). 2c's sketches
   need, from `isServer s γ`, the server-level names `N` with `N.etcd = γ` (a law
   `isServer_names : isServer s γ ⊢ ∃ N id, ⌜N.etcd = γ⌝ ∗ srvNode s N id`, or `Cluster` holding
   the raft names, as 2e's header says). Used by: every sketch of `ApiReq.lean`'s specs.

2. **What `isServer s γ` holds for the request path** (2e builds it at `start`, 2d keeps the
   invariants): `Read.readAt s.read N.raft (srvApplied s N)` (from `Read.readNew_init`, with
   `readEnv` below); the wait registry `Wait.listAt s.w γw P` with the cluster's answer predicate
   `P` (item 4) and its `Wait.waitToks γw U` in the cluster's invariant beside the `IdUtil.idFresh`
   of every `id ∈ U`; the generator `IdUtil.idGen s.reqIDGen γi` (one `idPrefix` per run:
   `IdUtil.idPrefixes` in the member's durable resources, taken at each start); the apply-wait list
   `Wait.timeListAt s.applyWait (fun d => srvApplied s N (uint.nat d))` (`NewTimeList` at
   `srvApplied_zero`, `srvApplied_mono`); `s.done`, `s.stopping` channels any goroutine may
   receive on (`Read.recvAny`); `s.Cfg.MaxRequestBytes`, `ReqTimeout()` read-only; the auth store
   (3d), the lessor (3c), the KV store (3e) at the member's applied point (item 6); `s.bemu`'s
   read lock over the current backend (4a: `ForceCommit`). Used by: `processInternalRaftRequestOnce`,
   `Range`, `Compact`, `LinearizableReadNotify`.
   ```go
   ch := s.w.Register(id)            // v3_server.go:1107
   err := s.read.LinearizableReadNotify(ctx)
   ```

3. **`readEnv` at `start`** (2e, over 2d's): `Read.readEnv s (&s.r) N.raft γi (srvApplied s N)`:
   the server's methods of `read.server` (`interface.go`, `server.go`: `Done`, `Stopping`,
   `LeaderChanged`, `FirstCommitInTermNotify` as `recvAny` channels, `Logger`, `RequestTimeout`,
   `AppliedIndex` with `srvApplied`, `ApplyWait(d)` with `srvApplied s N d` on the receive,
   `NextRequestID` with `idFresh`), the raft wrapper's `ReadState()` (2d's `readStateC_recv`) and
   `ReadIndex` (R1's `node.ReadIndex.spec` through `raftNode`), `srvApplied s N i ⊢ committedLb`
   of length `≥ i` (2d's `srvApplied_hist` with `histAt_committed`), and **the registration of
   read contexts** (the cluster's invariant holds raft's `readCtxs`: a fresh id's `be64 id`
   registered with `readLbQ l` for a `committedLb l`, its update fired inside the invariant with
   `committedOps_lb`). Used by: `Read.readNew_init` at `start`, hence every linearizable read.

4. **The proposal's update** (2d's cluster invariant): for a request `ir : IrrBody` by `who` with a
   fresh id (`idFresh`) and the caller's update over `etcdState γ` by `irrStep who ir` (one-shot,
   or persistent), an update over R1's `committedOps N.raft` for `node.Propose.spec` that, **at the
   entry's commit**: appends the history (`histAt`, `answered`), fires the caller's update with the
   answer the apply will compute at the entry's state (outcome 1), **except a stale auth revision**
   (`ErrAuthOldRevision` at the auth applier, K4: not fired, kept), and deposits for `id` in the wait
   registry's `P id`: the `*apply.Result` (`applyResult γ x ir res`) with the update's `Q σ σ' res`,
   or with the update itself for the stale-revision refusal. Fired **at most once**: raft's
   cluster must be one-shot (`N.raft.dup = false`) or the invariant fires only an entry's first
   committed occurrence (by its id). An entry no one proposed with an update (the `.noop` and
   `.authToken` kinds: checkpoints, cluster version, downgrade, a token) is committed by the
   invariant alone, the state unchanged. Used by: `processInternalRaftRequestOnce.spec`.

5. **The read registry** (2d's cluster invariant; the realization of K4's read discipline): laws
   (names suggestions)
   ```
   readReg_register : □ AU<etcdState γ, srvStep who rq> (a read: rq.isRead or .authenticate) ={E}=∗
       ∃ t l0, readTicket N t who rq Q l0 ∗ Raft.committedLb N.raft l0
   readReg_get : readTicket N t who rq Q l0 ∗ Raft.committedLb N.raft l ∗ ⌜opsOf l0 <+: opsOf l⌝ ∗
       histAt N k σ ∗ ⌜l.length ≤ k⌝ ∗ ⌜srvStep who rq σ σ res⌝ ={E}=∗ Q σ σ res
   ```
   (`l0` the committed log at the registration; `readReg_get` for a serializable read also at a
   view: the cluster's current state with any answer `Step` allows at it). Realization: the
   invariant fires each registered persistent update at every history point from its registration
   on, once for each answer `srvStep` allows there (finitely many: a range's answers are the
   permutations of ties of a finite list, the views of a finite history, the finitely many errors),
   and keeps the results; or, if 3b exposes the implementation's answer as a function of the state,
   once with it. The state at a history point depends only on the operations (`opsOf`) of the log
   up to it. Used by: `Range.spec`, `Txn.spec` (read-only), `RangeStream.spec`, `Authenticate.spec`.

6. **The member's applied state** (2d with 3b, 3d, 3e): a read of the KV store (`txn.Range`,
   `txn.Txn` over `s.KV()`), of the auth store (`IsRangePermitted`, `CheckTxnAuth`, `CheckPassword`,
   `Revision`) or of the lessor (`Lookup`, `Leases`) is answered at the member's applied point `k`
   (`srvApplied s N k`, `histAt N k σ`), the answer one W0's step allows at `σ`; consecutive reads at
   non-decreasing points. Used by: `Range`, `Txn`, `doSerialize`, the lease reads, `Authenticate`.

7. **`EtcdServer.LinearizableReadNotify`** (`interface.go`, 2e's file): its spec is
   `Read.LinearizableReadNotify.spec` at `s.read`. Used by: `examples/specreq/etcdserverreq/read.go`,
   the corruption checker, the lease HTTP handler.

8. **The internal requesters' updates** (2d, 2e): the lessor's `LeaseRevoke` with
   `authStore.WithRoot(s.ctx)` (`reqPrin ... (some root)`, 3d) and an update built from `envUpd`
   (`EnvStep.leaseExpire`; every other answer of `Step` the identity, answered by aborting); the
   compactor's `Compact` (`EnvStep.compact`, `rev ≠ 0`); the alarms' `raftRequest`/`Alarm` at
   `.alarmActivate` and `publishV3` at `.publish` **with no update**: their entries' commit is an
   environment step **the cluster's invariant takes by the `envUpd` it holds** (`EnvStep.alarm`,
   `EnvStep.publish`; the identity when the member is gone), so `isServer`'s invariant must hold
   `envUpd γ cfg` (2a's need, "from 2a" item 5); the checkpoints, cluster version and downgrade at
   `.noop` (no update, the state unchanged). Their contexts need `reqPrin` (`none` for `s.ctx`).
   Used by: the `raftRequest.spec`, `Alarm.spec`, `LeaseRevoke.spec`, `Compact.spec` callers.

9. **`srvWatchable s γ w`** (provisional slot in `ApiReq.lean`, for `Watchable.spec`): 2b's item 3
   above (`s.Watchable()` delivers the cluster's history); 2d/3f realize it.

## from 2a

Batch 2a (the gRPC handlers, `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/`, and the grpc
boundary) uses 2c's `ApiReq.lean` as it stands (`isServer`, `reqPrin`, `srvErrOf`, `srvUnfired`,
`srvIndef`, `SrvCallTriple`, `txnChecked`, `IrrBody.depthOk`, `rsSink`) and needs, in plain terms:

1. **`srvStep` is `Step`** at the handlers: the handlers pass the client's update (over `Step`, W0's
   `callAU`) to `EtcdServer.Put/Range/...`, whose `SrvCallTriple` takes one over `srvStep` (`Step` or
   the `doSerialize` auth race). An update over `Step` cannot be fired by `srvStep`: every
   `kvServer.*.spec` sketch relies on the race being closed (the fork's fix) or on a scope premise
   that makes `srvStep` `Step`. The user's decision (2c's report); 2a has no way around it.
2. **The principal**: a law `reqPrin_of_md`: from 2a's run context `Grpc.rpcCtx ctx md` and the
   contract's `V3rpc.mdPrin γ md who` (the incoming metadata names `who`: its `token` a token of `who`,
   `tokenOf`, or none), `EtcdServer.reqPrin ctx who` (3d's `AuthInfoFromCtx` reads the `token` or
   `authorization` key; a TLS peer's common name when there is none). Used by every handler's
   sketch (`kvServer.*`, `LeaseServer.*`, `AuthServer.*`, `ClusterServer.*`, `AuthAdmin.*`).
3. **Unmapped errors**: an error a request-path method returns that `togRPCError` does not map
   (`¬ srvErrOf err e` for every `e`) has a message (`Grpc.errMsg err m`) that is no description of a
   definite etcd error the client maps (`V3rpc.indefMsg m`), and is not a context's error wrapped in
   another value (`togRPCError` tests `errors.Is` against the context's errors). `srvErrOf` should not
   name the context's own error values (`context.Canceled`): `togRPCError` passes them through, and
   grpc sends them as `Canceled` with grpc's own message, not `ErrGRPCCanceled`'s (`togRPCError.spec`
   treats them apart). Used by: `togRPCError.spec`, the handlers' third way.
4. **The configuration bound**: `isServer s γ` gives `s.Cfg.MaxTxnOps ≤ 4999` (K8; `V3rpc.maxTxnOpsMax`,
   read by `NewKVServer`): `kvServer.Txn`'s discharge of `txnChecked`/`IrrBody.depthOk` (law
   `V3rpc.txnCheck_checked`). The `--max-request-bytes` bound of K8 is subsumed by the program's
   workload premise `Grpc.msgsFit` (a reply that cannot be marshaled is outside the boundary's scope),
   taken by `Grpc.start`; 2e decides whether to keep both.
5. **`EtcdServer.Alarm` for `ACTIVATE`** (the quota wrappers' `quotaAlarmer.check`): callable with
   no update from the caller (the server's own environment step, built from the `envUpd` that
   `isServer` holds), any outcome; for `GET`/`DEACTIVATE` the `SrvCallTriple` of `.alarmList` /
   `.alarmDisarm` over `alarmReqOwn`.
6. **`RangeStream`**: 2c's `EtcdServer.RangeStream` over `rsSink`; 2a gives `V3rpc.rsSink_intro`
   (from grpc's send half of the run's stream, the wrapper `headerFillingRangeStream`, the stream's
   recorded request `rsReq g who r Q`) and `rsSink_out` (the sink's end to the run's `streamOut`).
   2c's send law for `rsSink` should record each chunk sent (`V3rpc.rsChunk g j m`: the j-th chunk is
   `m`, up to the header's ids) and require of the last its `Q` and `streamMatches`. Used by:
   `kvServer.RangeStream.spec`.
7. **2e (start and membership)**: `AddMember`, `RemoveMember`, `UpdateMember`, `PromoteMember`,
   `MemberList` (`ClusterServer.*`'s callees) in `SrvCallTriple`'s shape for the cluster requests;
   `GoAttach` (monitorLeader's goroutine); the getters `Term`, `Leader`, `MemberID`, `Cluster().ID()`,
   `KV().Rev()`, `Backend()`, `Logger()`, `Cfg` fields, `IsLearner`, `IsMemberExist`, `Alarms` over
   `isServer`, read-only. The member's start (`Serve`): binds its client address once to
   `V3rpc.etcdContract γ` (`Grpc.addrFree_bind`, from the program's `addrFree ep`; a restart reuses
   the persistent `addrAt`), builds the server (`V3rpc.Server.spec`), applies `Grpc.start.spec` with
   its listener (`Grpc.listenerAt`, 2e's `net.Listen`) and `Grpc.msgsFit`, then `Server.Serve.spec`;
   `servesAt γ ep` is then `V3rpc.servesAt_addr`. Used by: `Server.spec`'s users, K3.

## from 2d

Batch 2d (the apply thread and the raft node driver: `ApiApply.lean`, report
`notes/specs-only/batch-2d.md`). Answers to 2c's items (`## from 2c` above), and what 2d's sketches
need of 2c (the request path, `pkg/wait`) and 2e (the lifecycle).

**To 2c.**

1. (2c's item 1) `isServer_names` is stated in `ApiApply.lean` (`isServer s γ ⊢ ∃ N id, ⌜N.etcd = γ⌝
   ∗ srvNode s N id ∗ srvStarted s N id`); 2e proves it when `start` builds `isServer`.
2. (2c's item 4) `histPropose` (`ApiApply.lean`) is the proposal law: a proposer's update over
   `etcdState γ.etcd`, fired with `applyStep mc σ ⟨t, ty, bs⟩ σ' res` (the apply's model, 3a's,
   deterministic: `applyStep_fun`), becomes raft's proposal update. The update's commit step is where
   2c deposits its `Q` for the waiter (keyed by the request id: 2c's own ghost box), since raft's
   proposal update returns nothing to the proposer. At-most-once: 2d allocates raft's cluster with
   `dup = false` (2e's `cluster_alloc`; etcd's transport never resends a message: 2f).
3. **The wait registry's predicate `P`** (2c's `Wait.listAt s.w γw P`): the apply thread triggers
   `w.Trigger(id, ar)` for a normal entry at index `k` applied past the consistent index with
   `answered γ k id res` and 3a's ownership of `ar` holding `res` (`applyResult`), and
   `w.Trigger(cc.ID, &confChangeResponse{members, raftAdvancedC, err})` for a conf change with
   `advancedAt (&s.r) raftAdvancedC last` (its close gives `nodeAdvanced`: raft has applied the
   change). `P` must accept both (plus `nil` from the requester's own give-up). Used by:
   `applyEntryNormal.spec`, `apply.spec`.
   ```go
   s.w.Trigger(id, ar)                                                       // server.go:2009
   s.w.Trigger(cc.GetId(), &confChangeResponse{s.cluster.Members(), raftAdvancedC, err}) // 1957
   ```
4. **`applyWait`** is `Wait.timeListAt s.applyWait (fun d => srvApplied s γ (uint.nat d))`
   (downward closed: `srvApplied_mono`); the apply thread triggers it at each batch's applied index
   (`applyAll.spec`). The read loop's `A := srvApplied s N` (2c's `readEnv`) is 2d's.
5. (2c's item 6, the member's applied state) **open at integration**: a read of mvcc/auth/lessor at
   the member's applied point is a law over 3e's/3d's/3c's state predicates, which 2d's invariant
   ties to `histAt` (the apply thread's state machine is at `histAt γ (max appliedi ci)`; readers see
   the backend's state, which is at or past every `srvApplied`). 2d will state it once 3e's
   `mvccState` exists (`req/go_etcd_io_etcd_server_v3_storage_mvcc.md`, "from 2d").
6. (2c's item 8) the lessor's revocation: `revokeExpiredLeases.spec` builds the update for 2c's
   `LeaseRevoke` from `envUpd` (fired only for a live lease, `EnvStep.leaseExpire`; any other answer
   aborts) with `authStore.WithRoot(s.ctx)`; it needs `LeaseRevoke.spec` to take a caller's update in
   that shape and `reqPrin (WithRoot s.ctx) (some root)` (3d).
7. 2d's `applyEntryNormal` proposes the `NOSPACE` alarm through `raftRequest` (2c's) with an update
   from `envUpd` (`EnvStep.alarm`) and `s.ctx`.

**To 2e.**

8. **`srvRunTok s γ id`** (what `start` hands `run`): the apply thread at its start
   (`applyThread s γ ep₀ p₀`, `p₀` at the `MemoryStorage` snapshot's index, which is the node's
   delivered start: `Applied = 0` in `raftConfig`), the backend's state machine at `histAt γ ci₀`
   for its consistent index `ci₀ ≥ p₀.appliedi` (any: a crash may leave the backend ahead of the
   WAL's commit, R1's restart at the backend's configuration), the driver's `rnLoop`/`rnStopper`
   (`rnInit_place` after `NewServer`'s copy into `s.r`), the ready handler's writers, the expiry
   channel's receive right (3c), the stop channel's receive right, and the escrow of `done`'s close
   where `run` deposits `srvStopped s γ id`, which 2e's `srvRunning` claims and turns into
   `memberDisk γ id ds` (a law of 2e's: `srvStopped` holds the WAL's durable half with `raftState`,
   the backend's closed image at its consistent index, the node's vacancy).
9. **`srvNode s γ id`** from `NewServer` (`Process` may run from the transport's start on),
   **`srvStarted s γ id`** from `start`.
10. **`raftNodeBootCfg`** (ApiBoot's provisional slot for 2d): `newRaftNode` needs only `0 ≤
    heartbeat` (a zero heartbeat gives an empty ticker: no ticks, liveness only) and a logger;
    raft's `ConfigOk` is `StartNode`/`RestartNode`'s (R1), at bootstrap.
11. **`rnCfgOk cv γ id n`** (`newRaftNode`'s premise): the node of `StartNode`/`RestartNode`
    with its `nodeDriver`, `nodeRunning`, `nodeConf`; `raftStorage` its attached `MemoryStorage`;
    `storage` the WAL+snapshotter with the durable invariant (item 12); `transport` 2f's.
12. **The WAL storage** (`serverstorage.Storage`, `req/go_etcd_io_etcd_server_v3_storage.md`).
13. **Membership** (`req/go_etcd_io_etcd_server_v3_etcdserver_api_membership.md`).
14. **The 403 error** of `Process` (`httptypes.NewHTTPError`): `httpForbidden err` (provisional in
    `ApiApply.lean`), with 2f's `procErr` (`procErr_forbidden`).
15. **Names**: 2e's `isServer s γ` is over W0's `Cluster`; 2d's vocabulary over `Names` (a structure
    with `.etcd`, `.raft`, `.cfg`): `isServer_names` bridges them. If W0's `Cluster` becomes a
    structure with the raft names, `Names` can be replaced by it (a decision for integration).
