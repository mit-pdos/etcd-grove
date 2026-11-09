# The top: a linearizable etcd, and the cluster contract (batch W0)

What everything on this branch exists to prove, and what each layer below owes it. The vocabulary:
`Spec/go_etcd_io/etcd/api/v3/Model.lean` (the model of what a client observes: `State`, `Step`,
`EnvStep`, `Reach`), `State.lean` (`etcdState`, `etcdLb`, `envUpd`, `servesAt`, `errVal`),
`Wire.lean` (the messages), `Spec/go_etcd_io/etcd/client/v3/Api.lean` (the client's handles and the
KV contract, `KV.*Triple`).

## 1. The linearizability spec

**One resource, owned by the program.** `etcdState γ σ` says the cluster `γ`'s state is `σ`. The
program that starts the cluster gets it in full (§3) and keeps it in an invariant of its own; the
cluster never owns it. Every client call takes an atomic update over it, fired once (a write) or
as often as the cluster likes (a read: `□ AU`; also the lease and alarm writes `retry.go` marks
repeatable, `LeaseGrant`, `LeaseRevoke`, `Alarm`, which the interceptor may resend after an
attempt that applied: they take persistent updates and may take effect more than once, 1c's specs;
the KV writes take effect at most once), by `Step who rq σ σ' res`; the environment
(lease expiry, auto-compaction, alarms, members publishing themselves) changes it only through the
permission `envUpd γ cfg` the program gave when it started the cluster. So **the program's
invariant sees every change of the cluster's state, in the order the cluster made them, with each
call's answer**: that is linearizability, stated TaDa-style, for the whole API (KV, leases, auth,
membership, alarms), every mode (auth on and off, leases, compaction, members added and removed,
snapshots, restarts) and every reply (success, a definite error, a refusal); only an indefinite
error (`indefCall`: a timeout, the leader or the connection lost, the context done) leaves the call
unsettled, and then the update may still fire later, inside the program's invariant.

**Persistent facts.** A client carries between calls `etcdLb γ σ` ("the cluster has been in state
`σ`"), taken from `etcdState` inside any update it fires (`etcdState_lb`); the current state is
reachable from it (`etcdLb_reach`), and two of them are ordered (`etcdLb_ord`). Every fact a client
carries is a pure consequence of `Reach σ₀ σ` it proves from the model: a revision reached (the
history only grows), a history prefix (`KVHist.revs` only grows), what a key held at a revision
(the history is kept whole; `compacted` only refuses reads), a lease granted (`granted` only grows),
a member added. They are the cluster's, never one member's: a later call may reach any member.

## 2. How a client program proves linearizability

### `examples/etcd/txnlin` (porcupine)

`Main` starts one member and a client, then `lintest.Run(Model(), Apply, Gen, clock, clients, ops,
timeout)` runs concurrent clients and porcupine's check; `Main` panics if porcupine finds the
history illegal. The proof:

1. **Start** (§3): `etcdState γ (State.init [m])`, `servesAt γ clientAddr`, `isClient cli γ none`
   (auth off; `Principal` none).
2. **The invariant** `I`: `∃ σ L, etcdState γ σ ∗ linLog L ∗ ⌜σ.kv` agrees with `L` replayed by
   `txnlin.Model`⌝ ∗ (each pending call's prophecy and token), where `linLog L` is a ghost list
   of the operations linearized so far with their outputs (porcupine's witness), and
   `⌜σ.leases = ∅⌝` (no principal grants leases: every update fired is the program's own).
   Environment steps keep `I`: `txnlin` never grants a lease (no `leaseExpire`), compaction and
   alarms do not change the store nor its revision (`txnlin.Model` sees neither), publications
   change members only. That is the obligation `envUpd γ cfg` asks of the program.
3. **Each call** (`Apply`): the update `I` makes for its request appends `(input, output)` to
   `linLog` when it fires at `σ` with `res`, where `output` is `res` read as `txnlin.Output`
   (a get's value, mod revision and version, the store's revision, a transaction's branch and
   results): `Model`'s `step` agrees with the model's `Step` on these (a pure lemma of the example:
   `Step`'s range, put, delete and transaction cases, at auth off, no leases). A read takes its
   update persistently (`□ AU`, `Req.isRead`): each firing appends nothing new to the KV (`σ' =
   σ`), and the `Q` returned is the firing's at the state the member read (registered before the
   read index is taken; txnlin resolves which with its read-revision prophecy `rp`). A call that errs: definite errors are
   linearized answers (porcupine's model treats `Err` as "maybe applied"; a definite one is
   applied as a no-op), indefinite ones leave the update pending, fired later or never: the
   prophecy `p.ResolveBool(!out.Err)` (in `Apply`) tells the update at its firing whether the call
   will return an error, so it records the operation as porcupine will see it.
4. **The check**: `linLog` is a linearization of the recorded history (each operation between its
   call and return, outputs matching); porcupine's spec (`CheckOperations` never returns `Illegal`
   when a linearization exists) gives that `Main` does not panic.

Two scope points of `txnlin` that the model makes explicit: a compare-only transaction is answered
from a stale view (`issues/etcd-txn-empty-serializable.md`: `Step`'s read-only serializable view),
so `txnlin`'s generator must not send one or its model must accept stale answers; a keys-only read
reports lease `0` (`issues/etcd-range-keys-only-lease.md`), invisible to `txnlin`.

### Kubernetes' etcd3 store (`k8s.io/apiserver/pkg/storage/etcd3`)

The store's resource versions are revisions; its objects are keys under a prefix; its writes are
compare-and-swaps on the mod revision (`OptimisticPut`/`OptimisticDelete`, `client/v3/kubernetes`:
`If(ModRevision(key) = rv).Then(OpPut(...)).Else(OpGet(key))`); its reads are `Get`/`GetStream` at
a revision or the current one; its compactor a compare-and-swap of `compact_rev_key` then
`Compact`. The proof's invariant holds `etcdState` with the store's own abstraction (each object's
versions: `versionAt k r o`, "version `r` of key `k` is `o`", the persistent mapping the old proofs
used, now a pure function of `σ.kv`'s history) and tolerates every environment step but the
compaction below what it reads (with the cluster's auto-compactor configured, `cfg.autoCompact`,
reads below the floor fail with `ErrCompacted`, which the store reports as "too old resource
version"). The snippets `clientv3kv/txn.go` (`ReqCASModRevision`), `history.go`, `stream.go`
cover its patterns.

### `client/v3/concurrency`'s `Mutex`, `Election`, `STM`, `Session` (batch 1d)

A `Session` grants a lease and keeps it alive; `Mutex.Lock` puts `pfx/lease-id` with the lease
(`If(CreateRevision(key) = 0)`), then waits until no key under the prefix has a lower create
revision. With the model's lease expiry (an environment step at any time; keep-alive guarantees
nothing, `Model.lean`'s header), **mutual exclusion holds of revisions, not of time**: the
holder's key was the prefix's first when it acquired (`etcdLb` of that state), and any write
fenced by `If(CreateRevision(holderKey) = rev)` (`Mutex.IsOwner`) takes effect only while the key
is still the holder's. That is the guarantee 1d can prove and what etcd documents; a time-based
mutual exclusion would need clocks in the model.

## 3. The cluster contract

What starting a cluster (or a member, joining or restarting) must give the client side, stated as
requirements on the server batches (2a, 2c, 2d, 2e: `req/go_etcd_io_etcd_server_v3_etcdserver.md`,
`req/go_etcd_io_etcd_server_v3_etcdserver_api_v3rpc.md`; the gRPC boundary
`req/google_golang_org_grpc.md`; rpctypes `req/go_etcd_io_etcd_api_v3_v3rpc_rpctypes.md`; the
messages `req/go_etcd_io_etcd_api_v3_etcdserverpb.md`; the client's other parts
`req/go_etcd_io_etcd_client_v3.md`).

**K1 — the state is allocated by the program, with the cluster's start resources** (2e's
vocabulary; the names are suggestions):

    cluster_alloc : ⊢ |==> ∃ γ, etcdState γ (State.init ms) ∗ [∗ list] m ∈ ms, memberBoot γ m cfg

**K2 — starting a member** (`NewServer`, 2e) takes one of: its `memberBoot` (a new cluster), its
durable state (a restart: the program's durable half, raft's durable node API: a restart is a
fresh volatile half over it), or `etcdLb γ σ` with the member in `σ.members` (a member a
`MemberAdd` answered: joining); and `envUpd γ cfg` (persistent), with `cfg.autoCompact` iff its
configuration runs an auto-compactor; `cfg.leaseExpiry = false` (no lease expires during the run)
is a **trusted deployment premise about time** (a timeless proof cannot show the lessor never
revokes), taken by the program, not proved by the server; and the configuration's scope premises
(K8). Nothing else:
no restriction to a first start, one member, auth off, no leases or no compaction.

**K3 — serving** (`Serve`, 2e over 2a's `grpc.start`): `servesAt γ ep` for the member's client
endpoint: its KV, lease, auth, cluster and maintenance services answer by `Step`, firing the
caller's update as the client's contract says (K4). The client's `New` (1c) turns `servesAt` into
`isClient c γ who`.

**K4 — every answer is a `Step`, fired at most once for a KV write**: a reply, or a definite error, is the
answer of `Step who rq σ σ' res` at a state where the caller's update was fired, with the reply's
`Q`; a KV write is fired at most once per call (a repeatable lease or alarm write, `retry.go`'s
policy, may be fired once per attempt, so its update is persistent) (at its entry's commit; never for an attempt the
client resends: a stale token); a read's update is registered before its read index is taken and
may be fired at every state from then on; the read answers with the `Q` of the firing at the state
the member read; a refusal is a step with no change; an indefinite error fires nothing at
return (the update may fire later). At-most-once is the cluster's (one proposal per call, an entry
committed once, rafthttp never resending).

**K5 — the environment's steps go through `envUpd`**: the lessor's revocation of an expired lease
(fired at the revocation entry's commit, the lease live), the compactor's compaction (only if
configured), an alarm's activation, a member's publication. Nothing else changes the state.

**K6 — the history is the committed log's**: snapshots, restores, restarts and membership changes
continue the same `σ`; an answered step is durable on a quorum (no crash transition in the model).

**K7 — the resource's laws** (2c/2d realize `etcdState` and `etcdLb` from the committed log's
states): `etcdState_timeless`, `etcdState_excl`, `etcdLb_persistent`, `etcdLb_timeless`,
`etcdState_lb`, `etcdLb_reach`, `etcdLb_ord`, `etcdState_revFits`, `etcdState_sizeFits`. etcd
never refuses at `2 ^ 63` (mvcc wraps), so the last two come from a **step budget**: a counted
resource fixed by the adequacy theorem (as Perennial's thread tokens), one spent per committed
entry, each entry writing a bounded number of events, held by the cluster's invariant (the bounds
plan's rule: the bound at its owner).

**K8 — scope** (configuration premises at `NewServer`, each an issue): `--max-txn-ops ≤ 4999`
(`issues/etcd-txn-nested-depth-apply-panic.md`), `--max-request-bytes` below the bound of
`issues/etcd-txn-keysonly-reply-alloc-panic.md`; at the client, `Compact` at a revision other than
`0` (`issues/etcd-restore-scheduled-compact-zero.md`). A read racing `AuthEnable`
(`nonissues/etcd-doserialize-auth-enable-race.md`) is in the model (a read's permission is checked
at an auth state since its start: `Step`'s `lo`), no premise; a user or role name over 32 KiB makes every member
exit (`issues/etcd-auth-useradd-long-name-fatal.md`): zap's `Fatal` diverges, so it is liveness
only, no premise.

**The principal of a request** is per call: `ClientV3.ctxPrin dflt ctx p` (a premise of every
client call, `Step p ...`): the client's own (`dflt`, its credentials) for a context with no token
metadata, a forwarded token's user for a client without credentials (the gRPC proxy, the in-process
`v3client` of `v3lock`/`v3election`), the server taking the principal from the request's metadata.

**What the model already contains of etcd's known quirks** (no premise needed, the client sees
them): the limit pushed down before a sort with no order (`issues/etcd-range-sort-none-limit.md`),
lease `0` in keys-only reads (`issues/etcd-range-keys-only-lease.md`), stale compare-only
transactions (`issues/etcd-txn-empty-serializable.md`), a put and a delete of one key in sibling
nested transactions (`issues/etcd-txn-check-intervals-sibling.md`: sequential events of one
revision), lease ids that collide (`issues/etcd-lease-id-mask-member-prefix.md`: `ErrLeaseExist`),
TTLs that differ by member (`nonissues/etcd-lease-ttl-differs-across-members.md`: a granted TTL at
least the asked), a deposed leader's keep-alive and time-to-live (a keep-alive says nothing).
