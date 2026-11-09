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

## from 2e

2e's lifecycle vocabulary is `Spec/go_etcd_io/etcd/server/v3/etcdserver/ApiBoot.lean` (namespace
`EtcdServer`): `srvMember s γ id` (persistent, from `NewServer`), `srvBuilt s γ id cfg` (exclusive,
from `NewServer`), `isServer s γ` (persistent, from `Start`), `srvRunning s γ id ds` (exclusive, from
`Start`, taken by `HardStop`/`Stop`), `memberDisk γ id ds` (the stopped member's durable state),
`srvClosers`/`srvClosed` (`Cleanup`'s). `γ` is W0's `EtcdModel.Cluster` (2d's `Names` joins it by
`isServer_names`: fine; at integration 2d's `Names.etcd` and the server's realization of `Cluster`
must be one record).

**To 2c (the request path).**
1. `isServer s γ` stays valid after the stop (it is persistent; gRPC may still deliver requests):
   every request-path spec over it must hold on a stopped server, answering an indefinite error
   (`ErrStopped`, a context error) and firing nothing. Used by `HardStop.spec`'s Margin, the
   snippets' `ReqStopAfterError`.
   ```go
   s.HardStop(); _, err := s.Put(ctx, req) // err != nil, indefinite
   ```
2. `EtcdServer.Compact.spec` is called by the auto-compactor (`V3compactor.compactable` of the
   server's interface value) with an update the server builds from `envUpd γ ecfg` (an
   `EnvStep.compact` on success, an abort on an answer that changes nothing): the spec's update must
   be the caller's (TaDa), with the principal the context names (none: the compactor's context has no
   token). Used by `NewServer`'s sketch, step 5.
3. `publishV3` proposes `ClusterMemberAttrSet` through `raftRequest` (2c's spec of an internal request,
   whose commit fires `envUpd`'s publication: 2d's apply). Used by `EtcdServer.publishV3.spec`.
4. Left to 2c (their only callers are the request path or the read loop): `interface.go`'s
   `ApplyWait`, `Done`, `LeaderChanged`, `NextRequestID`, `RequestTimeout`, `Stopping`,
   `FirstCommitInTermNotify`, `AppliedIndex`/`CommittedIndex` of the read loop, `LinearizableReadNotify`,
   and `FeatureEnabled` (2e specs `AppliedIndex` and `Term` as getters over `srvMember`, any value: if
   2c needs more of them, restate there). The `util.go`/`tracing.go` helpers 2c calls are 2e's
   (`quorum`, `isConnectedSince`, `numConnectedSince`, `isConnectedToQuorumSince`,
   `exceedsRequestLimit`, `isPriorityRequest`, `firstCompareKey`, `firstOpKey`, `firstOpType`,
   `firstOpLease`).

**To 2d (the apply thread and the raft node).**
1. `start` builds what `run` takes (2d's `srvRunTok s γ id`) from `srvBuilt` (its realization's
   apply-thread slot), and forks `run`; `run`'s stop closes `s.done` depositing `memberDisk γ id ds`
   (2d's `srvStopped` plus the files: the WAL's records `Wal.walRecs`, the snapshot dbs
   `Snap.snapDbs`, the backend file `Snap.beFile` from `Cleanup`'s `srvClosed`), which `srvRunning`
   reads (`HardStop.spec`). `run`'s stop must take the WAL purge's right back from `srvPurge`'s
   invariant before `storage.Close` (its premise), after `wg.Wait` (the purge goroutine, if attached,
   has deposited it).
   ```go
   s.HardStop() // run's defer: close(stopping); sched.Stop(); wg.Wait(); r.stop(); Cleanup(); close(done)
   ```
2. **The transport's entry points before `Start`** (2f's review F4): `tr.Start()` and `AddPeer` run
   inside `NewServer` (`server.go:412-436`), so peers may call `Process`, `IsIDRemoved`,
   `ReportUnreachable`, `ReportSnapshot` before `start`. State them over a predicate `NewServer` holds
   at `tr.Start()` (2e offers `srvMember s γ id`: every field they read is set by then; add a sealed
   part of `srvBuilt` if you need more), with `procErr err` in `Process`'s post (2f's `raftOk`), the
   removed sender's `403` (`httptypes.HTTPError`, `IsIDRemoved` of the sender: the membership view's
   `RaftCluster.IsIDRemoved.spec`). 2e did not write these files (they are 2d's).
3. `bootstrappedRaft.newRaftNode.spec` gives 2d's `newRaftNode` result as `raftNodeBuilt rn γ id st`
   (provisional in `ApiBoot`; replace by 2d's `rnInit`/`isRaftNode`), with the storage
   `ServerStorage.isStorage st wd sd ∗ storageOpen st 1`.
4. The raft loop's `Save` (`ServerStorage.storage.Save.spec`) takes an atomic update over the WAL's
   records `Wal.walRecs wd R` (to `R.save hs k es`), fired at the write: compose R1's `readyEnter`
   inside it (the cluster's invariant holds `walRecs` and `raftState` with `walHolds`). `Close` keeps
   `walRecs` with its owner and gives the purge right back; `Release` needs a saved snapshot record at
   its index (the update's premise: the old `walBaseLb`).
5. `RaftCluster.UpdateAttributes` panics on an id neither a member nor removed (`cluster.go:481`):
   the apply of `ClusterMemberAttrSet` needs it from the cluster's invariant (only a member
   publishes, itself). `ValidateConfigurationChange` needs `ccPanicFree` (2c's `configure` marshals
   the context) and reads the backend's view (`beView`), not the maps.
6. Members must share `--max-learners` for a learner add to be decided alike
   (`Membership.ccResult` allows `tooManyLearners` or not): a scope premise of the cluster, or 2d
   states it in its conf-change decision (open question Q5 of `batch-2e.md`).

## from 1c (round 1)

1. **The in-process client's adapters** (`server/etcdserver/api/v3client`: `adapter.KvServerToKvClient`,
   `LeaseServerToLeaseClient`, `AuthServerToAuthClient`, `ClusterServerToClusterClient`,
   `MaintenanceServerToMaintenanceClient`, the watch adapter): each meets its wire contract
   (`remoteKVAt`, `remoteLeaseAt`, `remoteAuthAt`, `remoteClusterAt`, `remoteMaintAt`, 1b's) with the
   default principal `none`, each call's principal its context's (the in-process caller's forwarded
   token). Used by: `clientBare_assemble`, snippet `clientv3client/inproc.go`, hence v3lock's and
   v3election's sessions (1d).

### from 2f, round 1

Restated after 2f's round 1 (the names are now those of `Rafthttp`'s `Api.lean`):

1. **`raftOk` is needed from `tr.Start()`** (`server.go:412-426`), before `s.start()`. `AddPeer`
   (`server.go:436`) starts the peers' `Process` loops and stream readers then, and the handlers
   may call `Process` once the peer listener serves. `EtcdServer.Process`, `IsIDRemoved`,
   `ReportUnreachable` and `ReportSnapshot` must be stated over a predicate `NewServer` holds at that
   point, not over `srvNode` (after `start`). In the Go code everything they read (`lgMu`/`lg`,
   `cluster`, `stats`, `memberID`, `r`'s node) is set before `tr.Start()`. Also:
   - `Process`'s post must give `Rafthttp.procErr err`, plus a law that `httptypes.HTTPError`s are
     `procErr` (their `WriteTo` writes a status and a body; `errors.As` on them returns);
   - `EtcdServer.IsIDRemoved` (`server.go:725`) needs a spec: any boolean, with a `threadTok` (the
     membership's read lock);
   - `Process` gets `Rafthttp.recvd ν m`: `msgSent`, `msgCredit`, and for a `MsgSnap` `ν.dbIn i`.
2. **The snapshot database** (completeness F3): the network's `ν.dbIn i` is the server's choice. For
   etcd: "a file of index `i` is in the snapshot directory (2e's `snapDbs sd F`, `F i = some img`
   with `ν.img i img`) until the apply thread installs an index `≥ i`". `trCfg` now takes
   `Snap.isSnapshotter ss sd ∗ Rafthttp.saveOk ν sd`: the server's persistent update over its
   `snapDbs` (held in its invariant) that saves an image certified for `i` (2e's `saveAt`, which
   keeps an existing file) and commits `ν.dbIn i`. Its proof: the invariant keeps every file's
   image certified (`ν.img`), whichever stream was kept first. `applySnapshot` then opens
   `<i>.snap.db` by `ν.dbIn i` (snippet `ReqInstallReceived`).
3. **`ν.img i img`** for etcd: `img` is the backend image of the committed state through `i`. The
   sender gives `Snap.dbReader rc img ∗ snapImg ν i img` of its merged message's pipe
   (`Rafthttp.outSnap`, with 2e's `isMessage`/`msgClose`).
4. **Thread tokens on the `Transporter` callers**: `ActiveSince`, `ActivePeers`, `CutPeer`,
   `MendPeer`, `Pause` and `Resume` take the caller's `threadTok` (the transport's read lock).
   `isConnectedSince` and the other `util.go` heuristics, `adjustTicks` and `EtcdServer.CutPeer`/
   `MendPeer` must take one. The interface value is `Rafthttp.transporterOk tp ν id`.
5. **Peer addresses**: `peerAddr ν a` for every member's URLs. A `MemberAdd`/`MemberUpdate` of a URL
   must carry it; it enters as a premise on the URLs a client supplies, kept by the membership
   invariant. Serving needs `Http.protoAt a P` (persistent) with `Rafthttp.raftCompat ν P`, the
   listener, and a pool of the caller's thread tokens (`Http.handlerPool`).
6. **The package variables**: `Rafthttp.vars_init.spec` gives `ConnReadTimeout`/`ConnWriteTimeout`
   read-only (at least `5s`) and `ErrClusterIDMismatch`'s error, for `adjustTicks`
   (`server.go:495`), etcdserver's init (`server.go:119`) and `corrupt.go:533,613`.

## from 3h, round 1 (the raft request moved down; v3lockpb/v3electionpb)

Coordinator's decision (review F4): the `InternalRaftRequest`'s model is now etcdserverpb's
(`Spec/go_etcd_io/etcd/api/v3/etcdserverpb/Api.lean`, namespace `EtcdServerPb`). Mapping for 2c, 2d
and 2e at integration (rename; 2c keeps the semantics `IrrBody.fires`, `irrStep`, `irrReply`,
`applyResult` over the moved type):

| 2c/2e provisional | replaced by |
|---|---|
| `IrrBody` (2c `ApiReq.lean`) | `EtcdServerPb.IrrBody` (same constructors) |
| `opMsgDepth`, `opsMsgDepth`, `txnMsgDepth`, `IrrBody.depthOk` (2c) | `EtcdServerPb.*` (same definitions) |
| `irrOwn p ir` (2c) | `EtcdServerPb.irrOwn p ir` = `irrOwnH p ir none` (header unset) |
| `alarmReqOwn p dq ir` (2c) | `EtcdServerPb.alarmReqOwn` |
| `irrIsRevoke r b` (2e `ApiBoot.lean`) | `EtcdServerPb.irrIsRevoke` (a definition: `nil`, or the `LeaseRevoke` field read-only; intro `irrIsRevoke_intro` from a persisted decoded request) |

Laws for the request path (2c) and the apply (2d): `irrOwnH_msgAt`, `alarmReqOwn_msgAt` (the
content relation `irrHolds`, `irrHeaderHolds`, `alarmReqHolds`, functional: `irr_holds_fun`),
`irrOwn_setHeader` (`r.Header = &pb.RequestHeader{...}`; `reqHeaderAt` is the header's fields, which
the code writes in place), `irrOwnH_header` (reading `r.Header.ID` back), `irr_content` (depth below
protobuf's limit under `depthOk`; `marshalOk` exactly for valid UTF-8 strings: `IrrBody.utf8Ok`).
So "`proto.Marshal` of an `irrOwn` message ... decodes back to `ir` with the header set" is
`irrOwnH_msgAt` + 2a's `Marshal.spec` (needs `Content.fits`: the encoded size is not bounded by the
model; 2c's premise, e.g. from the request having fit gRPC, `Grpc.msgsFit`) + `Unmarshal.spec` +
`Proto.encodes_fun` + `irr_holds_fun`. Open for 2c: the size bound (`fits`), which 3h cannot state
from the model alone.

For 2e (request 2): `v3lockpb` and `v3electionpb`'s messages are 3h's, same signatures as 2e's
provisional ones: `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3lock/v3lockpb/Api.lean`
(`V3lockpb.lockReq`, `unlockReq`, `lockResp`, `unlockResp`; `fields`, `resp_fold`) and
`.../v3election/v3electionpb/Api.lean` (`V3electionpb.LeaderKeyM` (moved from `V3election`),
`campaignReq`, `proclaimReq`, `resignReq`, `leaderReq`, `campaignResp`, `proclaimResp`, `resignResp`,
`leaderResp`; `reqFields`, `resp_fold`, `leaderKeyRO`).

## from 2d (round 1)

2d's round-1 repairs (`notes/specs-only/batch-2d.md`, "Round 1 repairs"); new laws in `ApiApply.lean`.

**To 2c.**
1. (2c's items 3 and 5) `readCtx_register` (a fresh request id of a started member's id space,
   `srvIdSpace s γi`, registers `be64 id` with `readLbQ l`), `readReg_register`/`readReg_get` (a
   `readTicket γ t Rel Q l0`, exclusive; generic in the relation `Rel`: instantiate it with
   `srvStep who rq`). `isServer_names` now also gives `∃ γi, srvIdSpace s γi`.
2. (2c's item 6) `srvReadAt s γ k` (slot) with `srvApplied_read`: state the read specs (`Range`,
   `Txn`, `doSerialize`, the lease and auth reads) over it; the subsystems' specs instantiate it
   (requested from 3e, 3c, 3d).
3. **The conf-change waiter's payload** (2d's provability F8, completeness F3): `P cc.ID x` must accept
   `x = &confChangeResponse{membs, rac, err}` with `answered γ k cc.ID res`, `histAt γ k σ`, `membs`
   listing `σ.members` (2e's `membersOwn`), `err = nil ↔ res` a success, and `advancedAt (&s.r) rac
   last`. `configure` (and `ReqConfChangeAnswered`) rely on "`err = nil` ⇒ the change's node is in
   `membs`", which this gives.
4. `histPropose` no longer takes `mc`: the step is at the cluster's shared `γ.mc`; it needs raft's
   namespace `etcdN .@ "raft"` and a non-empty normal entry.

**To 2e.**
5. **The shared apply configuration** (the coordinator's decision on 2d's provability F1):
   `Names.mc : MemberCfg` (3a's: the lease minimum TTL, i.e. the election timeout and tick) is fixed
   at the cluster's allocation; `NewServer` takes the premise that the member's configuration yields
   `γ.mc` (every member configured alike for the apply). The allocation also fixes raft's namespace
   `γ.raft.ns = etcdN .@ "raft"`.
6. **Run's hand-off** (completeness F4): `srvMember_node` (from `NewServer`'s `srvMember` to `srvNode`;
   `srvNode` holds from the server literal on, so `raftOk` for `tr.Start()` inside `NewServer` can
   use `Process.spec`), `srvRunTok_intro` (what `start` must hold: the driver placed at `s.r` with
   `rnLoop`, `rnStopper`, `applycPos (s.r) p₀.appliedi`; `applyInit s γ p₀ c₀` with `c₀ ≥ p₀.appliedi`;
   your `srvClosers s ds`; with `srvNode`, `srvStarted`), `srvStopped_disk` (`srvStopped s γ id ds ∗
   srvClosed ds ⊢ memberDisk γ.etcd id ds`: `run` deposits both in `s.done`'s escrow). Member ids are
   `Nat` (yours); raft's node id is `W64 id`.
7. **`raftNodeBuilt rn γ id st`** (your provisional slot) is 2d's `rnInit v γ id n` (`newRaftNode`'s
   post) then `isRaftNode`/`rnLoop`/`rnStopper` after `rnInit_place`; `raftNodeBootCfg` needs only
   `0 ≤ heartbeat`.
8. **`stopWithDelay`** (names-only in the translation, called by `applyEntries` in a raw goroutine):
   a trusted spec: after the delay it sends its error on `s.errorc` (2f's `errChanOk`, which `run`
   receives and returns on) or returns on `s.done`; it takes and keeps a thread token.
9. **`srvNet γ ν`** at `net_alloc` (2f's `Net`): `ν.γ = γ.raft`, `ν.img = imgAt γ` (an image of the
   state machine at a snapshot's point), `ν.dbIn i` the member's record over its `snapDbs` that the
   kept file of `i` holds such an image; the member's invariant over `Snap.snapDbs` keeps it; the
   save update `saveOk` fires it.
10. `errorc`: `srvNode_errorc` (2f's `errChanOk` of `s.errorc`), from the server literal.

## from 3c

The lessor's API: `Spec/go_etcd_io/etcd/server/v3/lease/Api.lean` (namespace `Lease`): the
writer's token `lessorState γl n ls` (the apply thread's), the persistent history `lessorAt γl j ls`
(readers answer from a state `j ≥` their lower bound `lessorLb γl i`), the objects `leaseObj γl l
id ttl`, `isLessor le γl c` (persistent), `lessorStop le`. What 3c gives and needs:

**To 2c (the request path).**

1. **Lease reads**: `lessor.Lookup.spec`, `lessor.Leases.spec`, `lessor.Renew.spec`,
   `Lease.Keys.spec`, `Lease.TTL.spec`, `Lease.Remaining.spec`, `Lease.Demoted.spec` (any goroutine,
   `isLessor` and a `lessorLb γl i`): each answers from a state `j ≥ i` of the lessor's history,
   returned as `lessorAt γl j ls`. `Leases`: the live ids, each once (`List.Forall₂` of objects to
   ids); `Lookup`: the live object or `nil`; `Renew`: the TTL of the live lease, `ErrLeaseNotFound`
   (not live at a state `≥ i`) or `ErrNotPrimary`, no other error; `Remaining`, `Demoted`: any value
   (time); `l.ID`: `leaseObj_id`. 2c's "at the member's applied point" needs from 2d (item 4) a
   `lessorLb γl i` for `srvApplied s γ k`, and the tie of `lessorAt γl j ls` to the history.
2. **The keys may be mid-entry**: `Keys` answers from any state of the lessor's history, which
   includes the states between two `Detach`es of a revocation's deletes and two `Attach`es of a
   transaction's puts: a key set no revision had (`nonissues/etcd-lease-keys-mid-apply.md`).
   W0's `leaseTimeToLive` (keys exactly those at some revision `r`) is false of etcd there; asked of
   W0 (`req/go_etcd_io_etcd_api_v3.md`, "from 3c").

**To 2d (the apply thread).**

3. **The expiry channel**: `lessor.ExpiredLeasesC.spec` gives `expiredCh γl c ch`, whose receive
   (`expiredCh_recv`) delivers `Lease.expiredSl γl sl ids` (persistent: the read-only slice of
   objects, `leaseObj` of each) and only when `c.expiry = true`. Replace `ApiApply.lean`'s
   provisional `expiredLeases sl ids` by `Lease.expiredSl γl sl ids`; `NewServer` makes the lessor
   with `c.expiry = γ.cfg.leaseExpiry`, so `run`'s arm gets `γ.cfg.leaseExpiry = true` from the
   receive.
4. **The history tie** (2d's invariant): the apply thread holds `lessorState γl n ls`; record, for
   each applied index `k`, the lessor's history index `n_k` the entry ended at, with
   `ls_{n_k}` the lessor of `histAt γ k σ` (`ls.table` agreeing with `σ.leases` on ids, the
   attachment invariant with σ's store); the states strictly between `n_k` and `n_{k+1}` are the
   middle of entry `k + 1` (only that entry's `Attach`/`Detach` steps; a `Grant` or a revocation's
   removal is one step). `srvApplied s γ k ⊢ lessorLb γl n_k` is then 2c's lower bound.
5. **`Promote`, `Demote`**: `isLessor` only, no change to the model, no panic (the logger is
   `isLessor`'s). **`Recover(newbe, rd)`** (`applySnapshot`): `lessorState`, `beOk newbe`,
   `beLeases newbe B` (2e's `OpenSnapshotBackend`, the image's bucket); gives the loaded state at
   `n + 1` (fresh objects, TTLs raised, no keys: mvcc's `Restore` re-attaches) and the old backend's
   bucket back (`beLeases ls.be ls.bkt`, for its close).

**To 2e (bootstrap, lifecycle).**

6. **`NewLessor(lg, be, cluster, cfg)`**: `Zap.isLogger lg` (the zero logger panics), 4a's `beOk be`,
   4b's `beLeases be B` (the opened backend's bucket: empty for a new member, the last commit's on a
   restart), `clusterOk cluster` (membership's), and the expiry mode `exp` with `exp = false →
   Lease.leasesOutliveRun`. ApiBoot's `leaseBootRes cfg ecfg` can be realized as
   `⌜ecfg.leaseExpiry = false → Lease.leasesOutliveRun⌝` (W0's K2 premise, opaque, the program's).
   It gives `isLessor le γl {minTTL := MinLeaseTTL, expiry := exp}`, `lessorState γl 0 _`,
   `lessorStop le`. The lessor is a `lease.Lessor` interface value: `Lease.lessorIface le`.
7. **`SetCheckpointer(cp)`**: `cp = func.nil` or `Lease.ckptOk cp`: for any context (`ctxOk`) and an
   owned `*LeaseCheckpointRequest` (`Proto.msgAt`), it returns `nil` or `ErrNotPrimary` (the server's
   closure: `ensureLeadership`, `raftRequest` of the checkpoint, its error dropped).
8. **`Cleanup`**: `lessor.Stop.spec` takes `lessorStop le` once; the lease bucket comes back from the
   writer's token by `lessorState_bkt` (for the backend's whole open token at close).
9. **`leasehttp`**: `RenewHTTP`'s spec and `Leasehttp.rtOk` are yours (`lease/leasehttp/`); 3c adds
   nothing: `TimeToLiveHTTP` has no translated caller (2c's `leaseTimeToLive` is untranslated).

## from 2a, round 1

1. **(2c) Apply-time token refusals go back unfired.** The handlers send a token or learner
   refusal (`ErrUserEmpty`, `ErrAuthOldRevision`, `ErrInvalidAuthToken`,
   `ErrGRPCNotSupportedForLearner`) only by the contract's second way: the caller's update is given
   back unfired, as 1c's `AttemptTriple` needs. The case arises when the apply's `isOpPermitted`
   returns `ErrUserEmpty`, because auth was enabled after a proposal without a user. 2c's
   `SrvCallTriple` must classify that as outcome 2 (`srvUnfired`, the update returned), never fire
   it. This is sound because the entry is a no-op. Used by every `*.spec` handler of v3rpc
   (`V3rpc.firedAns`).
2. **(2c) Error outcomes carry `V3rpc.srvErrOk err`.** Outcomes 2 and 3 of `SrvCallTriple`, and the
   error of outcome 1, need more than the pure `srvUnfired`/`srvIndef`. Each must carry one of:
   - a context's error (`context.isCtxErr`);
   - a comparable (`Grpc.cmpErr`), non-status, non-context error with a stable message
     (`Grpc.errMsg err m`) that is either `srvErrOf err e`, or unmapped with `V3rpc.indefMsg m`.

   This is what `togRPCError.spec` takes: its map lookup panics on a non-comparable key, and its
   fallback sends the message. 2c's errors are package variables (`errors.New`) and context
   errors, all comparable.
3. **(2e) The member's address.** `servesAt γ ep` is `Grpc.addrAt ep (V3rpc.etcdContract γ ep)`,
   2f's `Http.protoAt ep (grpcOver _ P)`. To serve it, 2e:
   - reserves the advertised client URL string `ep` (`Http.reserve` from the environment's
     `addrFree ep`; the environment premise is one string per socket, so the listen and advertise
     strings must be the same string);
   - listens (2f's `net.Listen`);
   - serves either with `Grpc.start.spec` (a `Http.handlerPool` of the caller's tokens; plain or
     cmux's HTTP/2 part, `Grpc.cmuxSubAt`, `cmux_split`), or through net/http with
     `Grpc.startHTTP.spec` and `Server.ServeHTTP.spec` (the TLS path's `grpcHandlerFunc`, whose
     other requests follow the protocol `P`).

   cmux (`github.com/soheilhy/cmux`) needs its names in the Goose configuration for its specs.
   embed's v3election/v3lock registrations need contracts in `etcdContract` (or an extended `C`)
   before embed can apply `start`.


## from 3a

The apply layer (3a, `Spec/go_etcd_io/etcd/server/v3/etcdserver/apply/{Api,ApiResult}.lean`),
answering 2c's and 2d's items and asking for what its sketches need.

**To 2d** (the replacement of `ApiApply.lean`'s provisional names):
1. `MemberCfg` is `Apply.MemberCfg` (a structure: `minLeaseTTL`, `MemberCfg.ok`); `applyStep mc σ e σ'
   res` is `Apply.applyStep` (same signature, transparent: an empty entry changes nothing, else the
   decoded request's `irrStep … true`); `applyStep_fun` is `Apply.applyStep_fun.spec`; totality
   `Apply.applyStep_total.spec` (for an entry whose request is `IrrOp.ok`: the request path's
   validation, the depth bound in `irrDecodes`). **A member's state machine (`smAt ua σ`) is at its
   own TTL-variant of the history** (`ttlEq`, `irrStep_ttl`): `histAt` records the proposer's answer;
   `applyAt`'s realization should hold `smAt ua σ_m` with `ttlEq σ_m σ_k`.
2. The uber-applier's contract: `Apply.isUber ua mc γ γc R` (persistent; `NewUberApplier.spec` gives
   it with `smAt ua σ`), its method bundle `Apply.isUber_apply.spec` (the approved parametric shape:
   `apply.Apply.spec` takes it as `P`/`Q`). `R` is 2d's choice, lent at each call and fixed at
   construction: what the backend's post-lock hook (mvcc's writes, `kvOk … R`), `ConsistentIndex()`
   (`ciOk … R`) and `ForceSnapshot()` (`snapSrvOk … R`, 2d's item 4) need, e.g. `forceSnapW s ∗` the
   consistent index's writer at most the applying index.
3. The membership: a `ClusterMemberAttrSet` entry needs the caller's update of 2e's `clusterSt`
   (`Apply.memberUpd γc op Q`), fired in both modes (also at the replay); its precondition (the
   member known: a member or removed) is the cluster's invariant (only a member publishes itself).
4. Without `shouldApplyV3` the model state does not move (`irrStep_noV3`); the result is `nil`,
   except an administration request refused (its error) and the membership requests (`&Result{}`).
5. `NewUberApplier` takes the stores at the model state as slots (`optsOk`, `optsSt`): mvcc's,
   the lessor's, the auth store's, the alarm store's (`alarmSt γa σ.alarms`: **the request path's
   concurrent `Alarms()` reads need a split of it**, the apply thread's part in `smAt`: 2d's/2e's
   protocol), the backend's member buckets (`beView`); `statusOk` (the server's `MemberID`, `Leader`,
   `Term`), `snapSrvOk`, `ciOk` (2d's, provisional in 3a's `Api.lean`).

**To 2c**:
6. (2c's item 1) `Apply.resultAt γ ar ir sk res` is the result: `nil` with the placeholder answer,
   or `applyResult γ ar b res'` for 2c's body `b` (`Apply.opBody ir.op b`; a token's checked
   revision any) and an answer `res'` with `resMatch ir.op sk res res'`: **`res` itself, except an
   alarm list in another order (the alarm store's map), a skipped transaction's ranges (`sk`), and
   `ErrNoSpace` after a write the quota applier applied**. Needed: the waiter's predicate and 2c's
   outcomes accept these (`irrReply` of an alarm list up to permutation; the `ErrNoSpace` case as
   outcome 3, W0's item 1 in `req/go_etcd_io_etcd_api_v3.md`).
7. (2c's item 2) The answer is a function of the state: `irrStep_fun`, `applyStep_fun`; a client
   request's apply is `Step ir.who rq` (`irrStep_step`) for a header the request path stamps
   (`Irr.hdrOk`: a user iff a nonzero revision) and an admitted request (`reqAdmitted`: the gRPC
   validation, a nonzero lease id; `txnAdmitted` from 2a's `txnChecked`). The stale revision:
   `ErrAuthOldRevision` changes nothing (`irrStep_oldRev`); it arises only for the KV and revoke
   checks (`isOpPermitted`), **never for an administration request** (`IsAdminPermitted` checks no
   revision: W0's `mayCall` at the current state).
8. (2c's item 3) `CheckTxnAuth.spec`: `nil` only if each pair of the transaction's `perms` is
   permitted at some auth state of a reached state's `authTables` (the checks are not atomic); else
   `ErrUserEmpty`, `ErrAuthOldRevision` or `ErrPermissionDenied` (`srvErrOf`). It takes 3d's
   `authRead ast γ` and 3c's `lessorRead le` (provisional in 3a's `Api.lean`).
9. **`Wait.list.IsRegistered`**: a `false` answer should give a persistent fact that `id` is no
   longer (and never again) registered, so that `apply.Apply`'s skipped transaction (`sk`) and its
   `nil` return for an unregistered read are harmless to the waiter (2d's `Trigger` then delivers
   nothing). Then `Apply.spec`'s post carries `⌜sk = false⌝ ∨ <that fact>`. Used by `Apply.spec`
   (a margin today).
   ```go
   needResult := w.IsRegistered(id)                                     // apply.go:40
   ```
10. The `InternalRaftRequest` the request path proposes decodes (`Apply.irrDecodes`, 3h's) to an
    `Irr` with `hasId` and `IrrOp.ok`; `irrOwn p ir` (2c's provisional) should be stated over
    `Apply.Irr` (a user change carries the hash, `Authenticate` the password and the token prefix).

## from 2c (round 1)

2c's round-1 repairs change its API (`ApiReq.lean`, `errors/Api.lean`); **the callers in this
directory must follow** (2e's `EtcdServer__{AddMember,RemoveMember,UpdateMember,PromoteMember,
configure}.lean` no longer build against it):

- `reqPrin ctx p tls` (two principals: `p` with auth enabled, the certificate's `tls`), and every
  spec's update over `srvStep p tls rq σ σ' res lo` with the caller's `authLb γ lo`;
  `SrvCallTriple e P B γ p tls rq rep reply`;
- every returned error carries `srvErrShape err` (`errors/Api.lean`, which now holds `srvErrOf`,
  `srvIndef`, `srvUnfired` and the sentinels `srvErrVal`);
- `irrOwn p dq ir` (the inner request at `dq`, given back by `raftRequest`), `IrrBody.wf` (was
  `depthOk`; with the gRPC layer's validation), `IrrBody.authToken name pw rev` (fires),
  `irrStep p tls lo ir`, `IrrBody.backOk`.

Needs (amending "from 2c"):

1. **One-shot proposals need `dup = false`** (item 4's "or fire only an entry's first committed
   occurrence" is withdrawn: the apply applies every occurrence). 2d's server-level raft cluster is
   allocated with `dup = false` (2f's rafthttp supports it).
2. **Raft's namespace inside `etcdN`**: the cluster's invariant fires the callers' updates (mask
   `⊤ \ ↑etcdN`) inside raft's proposal and read updates (mask `⊤ \ ↑γ.raft.ns`): `↑γ.raft.ns ⊆
   ↑etcdN`, the history's invariant in a disjoint sub-namespace (a fact of 2d's `Names`).
3. **The read registry no longer serves `Authenticate`** (a one-shot update now: the token entry's
   commit fires it iff the auth revision is still the checked one; else the update is given back with
   the token, `IrrBody.backOk`). 2d's commit rule for `.authToken name pw rev`: fire the caller's
   update with `.ok .authenticate` when `σ.auth.rev = rev`, with the apply's `ErrAuthNotEnabled` /
   `ErrAuthFailed` when those are its answers, else keep it (the result's `P id x` carries it back).
4. **The wait registry's answer predicate covers both kinds of id**: a normal entry's, a non-nil
   `*apply.Result` (`applyResult`); a conf change's, a non-nil `*confChangeResponse` (`configure`
   panics on `nil`, `server.go:1793`). For the apply's `IsRegistered` (`apply/apply.go:40`) the
   invariant supplies `Wait.waitWasReg` for this member's ids and burns the token of another member's
   (`Wait.waitToks_never`: `waitNever`), so `false` gives `waitDone` and `Trigger` owes nothing.
5. **The health checks' read permission**: `etcdhttp/health.go`'s `Range` of the empty key needs a
   persistent update over `etcdState` (`srvStep`'s `emptyRangeStep`); `isServer` (or 2e's health
   handler's slot) must hold one (W0's `etcdPeek`).
6. **`publishV3`** (`.publish`, no update): if 1c's `memberServes` (a published member's client URLs
   serve `γ`) is proved at the publication's commit, the commit needs `servesAt γ u` for each URL;
   say whether it comes some other way (the bound listener), else `.publish` must carry it
   (completeness F14).
7. **2b's bridges**: `isServer s γ ⊢ watchMemberAt s γ` (2e: 2b's handle), and `srvWatchable`'s
   bridge from mvcc's store names to `γ`'s history (2d with 3f; `srvWatchable_mvcc` gives
   `Mvcc.watchableAt`).
8. **The package variables' values**: `etcdserver/errors`' sentinels hold `srvErrVal e` (a law of the
   package's initialization; `errors/Api.lean`'s `srvErrVal`), as do `membership`'s (2e), for
   `errors.Is` at the callers.

## from 3d

The auth store's API is `Spec/go_etcd_io/etcd/server/v3/auth/Api.lean` (namespace `Auth`). What
the server batches must supply and what they get, against the needs 2b and 2c filed
(`req/go_etcd_io_etcd_server_v3_auth.md`):

**To 2c (the request path).**
1. **`doSerialize`'s revision re-check does not justify the read's permission**
   (`nonissues/etcd-auth-revision-before-visible.md`): an admin step bumps the revision atomic before
   it publishes the new users and roles, so a simple token's or a certificate's `AuthInfo.Revision`
   (the atomic) can be the new revision while the check reads the old state, and the re-check after
   the read passes. `Range.spec`'s sketch ("the token's revision equal at the end means the auth
   state did not change in between, so the check holds at `kr`") is false; `srvStep` needs a disjunct
   (the read's answer at a state whose auth state is the check's predecessor) or a fix on the fork
   (bump the atomic after the batch transaction's `Unlock`). **Decision for the user**, with the
   `AuthEnable` race. What the store states: `authStore.IsRangePermitted.spec`'s `checkPost` (each view
   at a recorded state at or after the caller's `authLb`; a pass is `State.permits` at one of them).
2. **`Authenticate`'s loop is sound as sketched**: `CheckPassword`'s revision is the backend view's,
   the same as the user it read (`authStore.CheckPassword.spec`), and two equal revisions mean the same
   users and roles (`Revision.spec`, `authAt_reach`, W0's bump). But its success no longer says the
   password is the user's (`req/go_etcd_io_etcd_api_v3.md`, "from 3d", item 1).
3. **`reqPrin ctx who`'s realization** needs the cluster: `AuthInfoFromCtx` maps the context's token
   (`Auth.ctxToken ctx o`) to a user `u` with `tokenUser γ tok u`; so `reqPrin` should take `γ`
   (`reqPrin γ ctx who`), or be defined per server (`isServer s γ`). With W0's `tokenUser_agree` and
   2a's `mdPrin`, `who = some u`. The TLS fallback: `Auth.ctxCertUser ctx c` (`AuthInfoFromTLS.spec`).
4. **`WithRoot`** (`revokeExpiredLeases`): `authStore.WithRoot.spec` gives `ctx` itself or a context
   carrying a token `tokenUser γ tok "root"`; it needs `Auth.rootTokOk γa`, which the simple
   provider (etcd's default) does not give (`nonissues/etcd-auth-withroot-token-collision-panic.md`):
   **decision for the user**.
5. **The readers' lower bound**: every reader spec takes `Auth.authLb γa i0` (every view of the store
   at its `i0`-th state or later). 2d's invariant should give, with `srvApplied s γ k`, an `authLb γa
   i` whose `authAt γa i a` has `a = (histAt γ k).auth` (the store is at the applied point), if 2c
   needs a lower bound (the linearizable read); `authLb γa 0` (from `authCur_at` at boot) otherwise.
6. `BcryptCost()` is in `[4, 31]` (`BcryptCost.spec`), so `bcrypt.GenerateFromPassword` fails only for
   a password over 72 bytes (`Bcrypt.GenerateFromPassword.spec`); the proposal's `HashedPassword` must
   be `Auth.b64 h` (an `encoding/base64` boundary spec of `EncodeToString` returning `Auth.b64`, 2c's)
   so that `Auth.hashedPw_intro` gives the store's `authReqAt`.
7. The package's error variables: `Auth.init.spec` (`errOf`), `AuthErr.etcd` (`togRPCError`'s table).

**To 2d (the apply thread, the snapshot install).**
8. The apply thread holds the store's writer `Auth.authCur γa i a` with `a` the auth state of the
   history at the applied point, and supplies each admin step's `Auth.admNext γ rq a` (the next state
   is reached: the committed entry's, fixed at the commit; its records fit, `recordsFit`, the
   name-length scope restriction of `issues/etcd-auth-useradd-long-name-fatal.md`).
9. `applySnapshot`'s `Recover(newbe)`: `authBackendAt be' a'` (4b) with `a'` the snapshot's auth state,
   `authReached γ a'`, `AuthReach a a'` (the snapshot is at a later index: the history's auth steps
   between are `admStep`s or identities), `validPerms a'`; it gives back the replaced backend's share.
10. `Authenticate`'s apply: the entry's index `idx` above the last one (`Auth.tokFrom γa n`, `n < idx`;
    2d mints `tokFrom γa 0` from `NewAuthStore`), and `Auth.authnCtx γa ctx name idx` (the context's
    index and prefix with `tokenUser γ (p.idx) name`: 2d's realization of `tokenUser`).

**To 2e (boot, cleanup).**
11. `NewTokenProvider.spec`: the waiter `s.applyWait.Wait` as `Auth.waiterOk` (a channel any
    goroutine may receive on), a `threadTok` for the simple provider's keeper, `Auth.jwtTokOk γ opts`
    for a JWT configuration. `NewAuthStore.spec`: `authBackendAt be a` (4b's `schema.NewAuthBackend`),
    `authReached γ (normRev a)` (the fresh backend's state is W0's initial auth state; a restart's is
    the consistent index's), `validPerms a`, `recordsFit`. It gives `authStoreAt`, the writer
    `authCur γa 0 _`, `tokFrom γa 0`, and `rootTokOk γa` unless the provider is simple. **Slot**
    `authBootRes cfg` (ApiBoot's provisional) should be: `jwtTokOk γ cfg.AuthToken` for a JWT kind
    (no other condition: `BcryptCost` is normalized, `TokenTTL` any). `Close.spec` needs only
    `authStoreAt` (the "closer" of `srvClosers` is nothing).

## from 2e, round 1

Supersedes "from 2e", **To 2c** item 1 (withdrawn: false of Go, `issues/etcd-read-after-backend-close-panic.md`).

**To 2c.**
1. **The gate.** `Start` gives `srvGate s 1` (fractional, `ApiBoot.lean`); `HardStop`/`Stop` take it
   whole (no request in flight). Every request-path spec over `isServer s γ` must take a share
   `srvGate s q` and give it back (its realization is the readers' tokens of the store and the
   backend, which the stop rebuilds into the backend's open token for `Cleanup`). After the stop no
   request runs, so nothing is claimed of a stopped server. The fork fix (a gate in Go, reads then
   failing with `ErrStopped`) is the user's open alternative (`batch-2e.md` Q7).
   ```go
   go func() { _, _ = s.Range(ctx, req) }() // holds a share; the program waits for it before s.HardStop()
   ```
2. **The member operations are 2e's** (2a's item 7): `EtcdServer.{AddMember, UpdateMember,
   RemoveMember, PromoteMember, configure}` in `SrvCallTriple`'s shape over your `srvStep pr tls rq
   … lo`, `reqPrin ctx pr tls`, `authLb γ lo`, with `srvGate` and a `threadTok`; their answers are
   `respMembers res` (`ApiBoot.lean`). They use your `srvErrOf`, `srvUnfired`, `srvIndef`,
   `srvWatchable` (`EtcdServer.KV.spec`): keep those names or tell 2e.

**To 2d.**
3. 2e's hand-off laws are your `isServer_names`, `srvMember_node`, `srvRunTok_intro`,
   `srvStopped_disk`: 2e keeps `memberDisk`'s realization as `srvStopped ∗ srvClosed` gives it. Two
   changes: (a) the snapshot directory is **not** in `memberDisk` nor in `srvStopped`: `Snap.snapDbs`
   lives in a per-directory invariant for good (any raft handler of any incarnation may add files
   through `SaveDBFrom`, also after the stop: provability F5); `srvStopped` carries only the deletion
   right `snapDel` (`ReleaseSnapDBs`, `OpenSnapshotBackend`'s rename) and the presence of the file
   the restart needs. (b) The members' shared apply configuration is `ApplyCfg` with
   `applyCfgIs cfg mc` and `clusterApplyCfg γ mc` (provisional in `ApiBoot`, since `ApiApply` imports
   `ApiBoot`): identify `ApplyCfg` with your `MemberCfg` at integration (`cluster_alloc` takes `mc`,
   `NewServer` takes `clusterApplyCfg γ mc ∗ ⌜applyCfgIs cfg mc⌝`).
4. Member ids: `NewServer` gives `0 < id < 2 ^ 64` (`srvMember_id`); `Nat` throughout, as yours.
5. `raftNodeBootCfg_intro` is stated as your item 10 asks (`1 < ElectionTicks`, a non-negative
   heartbeat): restate it in your slot when you own it.

## from 2d (round 1b)

Supersedes "from 2d (round 1)" items 4 and 5 (the coordinator's update: 3a's resolution of the
member-dependent apply, with no premise).
1. **No shared apply configuration.** 2d's `Names` has no `mc`; 2e's `ApplyCfg`/`clusterApplyCfg`
   (added at 2d's round-1 request) are not needed: please drop them and the `NewServer` premise. A
   member's own configuration is `srvCfg s mc` (2d, persistent; `srvNode_cfg` gives it with
   `mc.ok`): 2e's `NewServer` establishes it with 3a's `Apply.MemberCfg` of the member's
   configuration (its lessor's minimum TTL).
2. **To 2c**: `histPropose` takes the proposer's `mc` (from `srvNode_cfg`); the history records the
   proposer's step (3a's `Apply.applyStep mc`), and every member's state machine is at a TTL-variant
   (`Apply.ttlEq`) of it. W0's lease reads already allow any TTL, so the read slot `srvReadAt`
   answers stay `Step`'s.

## from 2e, round 2 (crash restart)

**To 2d.** The durable state is now client-owned throughout (`ApiBoot.lean`, "Crashes"):
`diskState γ ds k` stays in the program's crash invariant; the running server reaches it through the
persistent access `diskAcc γ ds` (an update over `diskState` with no value change visible to the
program). So:
1. The raft loop **deposits the batch's `readyEnter` in the disk** (through `diskAcc`) before the
   WAL's `Save`, and fires it inside `Save`'s update (`storage.Save.spec`), so that after a crash
   `disk_crash` can apply R1's `raftState_crash` to the in-flight batch. A snapshot-carrying batch is
   outside the crash scope (R1's law excludes it).
2. Every other durable write (the backend's commits through the post-lock hook, `SaveSnap`,
   `Release`, a snapshot install's rename) fires `diskAcc` too, keeping `diskState`'s realization
   (`walHolds`, `beHolds`) true at each instant.
3. `memberDisk γ id ds` is now a definition, `diskIdle γ ds (.member id)` (the volatile idle token):
   your `srvStopped_disk` still type-checks, but `srvStopped ∗ srvClosed` now gives only the idle
   token (the files' content is in `diskState`, never moved).
