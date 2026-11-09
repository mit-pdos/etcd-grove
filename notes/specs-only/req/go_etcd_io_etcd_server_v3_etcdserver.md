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
