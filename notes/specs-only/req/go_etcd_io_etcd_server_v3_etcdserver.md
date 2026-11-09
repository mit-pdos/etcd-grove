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
