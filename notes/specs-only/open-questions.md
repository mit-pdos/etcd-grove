# Open questions for the user (specs-only run)

Every decision the specs-only run (batches W0, 1b-1g, 2a-2f, 3a-3h, 4a-4d, R1-R4; integrations
I1-I7, X, Y) left to the user, compiled 2026-11-09 from `notes/specs-only/batch-*.md`,
`integration-*.md` and `top.md`. Paths below are relative to the repository root; a batch's report is
`notes/specs-only/batch-<id>.md`. Each item gives the question, the options and their costs, who raised
it, and what the specs assume today ("**Now:**"). A question several batches raised appears once,
listing them all. Questions a later round settled are left out; technical gaps that need no decision
(provisional names, unrealized slots, sketches still to check) are not listed: see each report's
"Not done" and "Needed from" sections.

Sections: [A. Decided by the coordinator](#a-decided-by-the-coordinator-revisit-if-you-disagree) ·
[1. Top-level model & client](#1-top-level-model--client) · [2. Raft](#2-raft) ·
[3. Server](#3-server) · [4. Storage & bbolt](#4-storage--bbolt) ·
[5. Trust boundaries & environment premises](#5-trust-boundaries--environment-premises) ·
[6. Fork fixes proposed for real etcd/raft bugs](#6-fork-fixes-proposed-for-real-etcdraft-bugs) ·
[7. Perennial / translation changes](#7-perennial--translation-changes) ·
[Real bugs found](#real-bugs-found)

## A. Decided by the coordinator (revisit if you disagree)

Choices the coordinator (or, where said, a batch on its behalf) made during the run, with the
alternative not taken. The specs are written to the choice.

A1. **Concurrency recipes: a permission lent per call.** `Mutex`/`Election`/`STM` writes take
   `etcdLent γ T P ∗ P` and give `P` back when every write was answered. Alt.: one persistent
   permission for everything (round 0: simpler, callers learn nothing of their keys afterwards), or an
   exclusive TaDa update per operation (`Proclaim`, `Resign`, `Unlock`, `Session.Close`, an STM
   commit) as 1f's queues have, letting a caller linearize at the commit. 1f kept TaDa for queues and
   the lock key: two shapes coexist. (`batch-1d.md` round 1 F8, open question 1; `batch-1f.md` D1.)
A2. **The `doSerialize`/`AuthEnable` race and the auth-revision race are in the model, no premise.**
   W0 round 4 (`authHist`, `lo`, `authLb`) and round 6 (`permittedSince`): a linearizable read may be
   answered as permitted at any auth state since its start. Alt.: the fork fixes (§6, F1) and a
   tighter model, or a premise "no `AuthEnable`/auth change while reads are in flight" (no local
   statement). (`batch-W0.md` rounds 4, 6; `batch-2c.md` D1; `batch-3d.md` Q1;
   `nonissues/etcd-doserialize-auth-enable-race.md`, `nonissues/etcd-auth-revision-before-visible.md`.)
A3. **`ErrNoSpace` is indefinite.** An over-quota member applies the write and still answers
   `ErrNoSpace`; a client seeing it learns nothing, even when the refusal really came before
   proposing. Alt.: the old workload premise `backendUnderQuota`. (`batch-3a.md` D2; `batch-W0.md`
   round 5; `nonissues/etcd-apply-quota-nospace-after-write.md`.)
A4. **Per-member lease reads in scope.** `State.leaseHist`, `leaseViewLb γ ep i`: `Leases`/`TimeToLive`
   answer from a table the member has reached. Alt.: a single-member mode (no model change).
   (`batch-W0.md` open question 6, round 3.)
A5. **The principal per call** (`ctxPrin dflt ctx p`, W0 round 3): forwarded tokens (proxy,
   `v3client`) authenticate as their user. Alt.: one principal per client handle (excludes the proxy
   and `v3client`). (`batch-W0.md` round 3; `batch-1e.md` "Decisions, updated" (3).)
A6. **Members configured differently.** The history records the proposer's lease TTL; every other
   member's state machine equals it up to TTLs (`Apply.ttlEq`, `irrStep_ttl`); no premise. Alt.: a
   `NewServer` premise that all members have the same minimum TTL (exact histories per member,
   restricts deployments etcd allows). W0 declined a model change. (`batch-3a.md` D1; `batch-2d.md`
   Q2; `batch-W0.md` round 5 "Declined".)
A7. **Stopping a member: a drain premise.** `HardStop`/`Stop` take the whole `srvGate s 1`; every
   request-path call holds a share. Alt.: the fork fix (§6, F3), after which a program could stop a
   member while serving it. (`batch-2e.md` round 1 F2, Q7.)
A8. **mvcc's compactor `Rev()` and hashing.** `Rev()` without a reader token (option (a), then Y's
   persistent `mvccRevTok`); `Hash`/`HashByRev` take a share of `mvccRestoreGate`, so hashing excludes
   `Restore`. Alt. for hashing: `Restore` returns the old storage's slots except those of hashes in
   flight (cuts nothing off, more bookkeeping); for `Rev`: make the server wait for the compactor
   (a code change). (`batch-3e.md` Q1, Q3, round 1; `integration-Y.md` (2).)
A9. **Reader tokens (not thread tokens) for mvcc's and the lessor's reads, and the watch stream's
   loops** (applying your 2026-11-06/07 decision). (`batch-3f.md` Q4; `batch-3c.md` round 1.)
A10. **4a F1: `Unlock` publishes in two visible updates** (the session's puts, then its deletes).
   Alt.: one update and read ranges tolerating the session's deleted keys (a persistent "deleted"
   mark, smaller client statements). (`batch-4a.md` Q1; `batch-3e.md` round 2.)
A11. **`DefaultPageSize` trusted to be 4096** (the linux/amd64 constant the old development trusted).
   (`batch-4d.md` D5.)
A12. **`MsgApp` entries' capacity: `msgRecv`.** A message stepped into raft from outside owns its
   entries slice's capacity (`node.Step`, `RawNode.Step` take `msgRecv`; rafthttp's decoders and
   `Unmarshal`/`Clone` supply it). Alt.: the fork clips in `logSliceFromMsgApp`
   (`slices.Clip`), and the premise goes back to `msgPts`. (`integration-I2.md` item 8;
   `nonissues/raft-msgapp-inprocess-aliasing.md`.)
A13. **A token provider's error in `Authenticate`'s apply is admitted, no provider flag**
   (`provErrResult`; the no-op provider always fails, JWT on signing). Alt.: an `aok` flag on
   `tokenProviderAt`, given by the simple provider only, letting `Authenticate.spec` drop the error
   disjunct. Cost now: 2c's `Authenticate` may return an error after its update fired.
   (`integration-I5.md` "Coordinator's decisions" 1; `integration-X.md` open item 4.)
A14. **Non-`nil` empty `RangeEnd`: a scope premise.** Filed `nonissues/etcd-auth-empty-range-end-point-check.md`;
   `CheckTxnAuth`/`checkTxnPermission` take `endsDecoded`/`opsDecoded` (what gRPC decoding gives).
   Alt.: a margin in 2c/3a at that input, or a fork fix of the auth check. (`integration-I5.md`
   "Coordinator's decisions" 2.)
A15. **The peer-URL right `urlsRight γ urls` lives in W0's `State.lean`** and is taken by the client's
   `MemberAdd`/`MemberUpdate`; spent even when the call is refused. (`integration-I1.md`, first
   section.) See 3.1 for the single-use question itself.
A16. **`IrrBody` (the raft request's model) is 3h's**, 2c's copy dropped. (`batch-3h.md` Q4;
   `integration-I4.md`.)
A17. **Watch exactness gated on `exactFrom`** (1b round 3, adopted downstream by I1): events are exact
   only when no revision up to the compaction changes a key twice (the sibling put/delete bug). Alt.:
   gate the condition into the watch's creation (the approved old design), or exclude such
   revisions in W0's model (false of the code). Users (1d `Observe`, 1f, 1g cache) carry it as an
   invariant clause. (`batch-3f.md` Q1; `batch-1b.md` round 3; `integration-I1.md`.)
A18. **Decided inside W0 (not the coordinator):** `Cluster` stays an opaque client-side name, with the
   bridge `isServer_names` to 2d's `Names` (alt.: `Cluster` a structure with raft's names and the
   configuration, putting raft's vocabulary into every client spec); 3c's per-member granted TTLs not
   modelled; `LeaseTimeToLive`'s keys weakened to "attached at `r` or `r + 1`" (3c's finding; alt.: a
   fork fix, §6 F11). (`batch-W0.md` round 5 "Declined"; `batch-2d.md` Q1; `batch-3c.md` D1.)

## 1. Top-level model & client

1.1 **Watch responses as `etcdLb` facts, not atomic updates; `Created`/progress/closing unstated
   (liveness).** A client's invariant cannot act at the moment of a response (no user needs to).
   Alt.: the old `□ AU` form. Raised by 1b (D1, D3), `batch-1b.md`. **Now:** facts.
1.2 **A refused watch delivers nothing only on an up-to-date member.** `examples/etcd/auth/authkv.go`
   relies on it with one member. Options: (a) a lower bound on the admitting state for a one-member
   cluster, taken at the call; (b) keep, recording that authkv's check rests on its single member.
   1b round 1, open question 4, `batch-1b.md`. **Now:** (b).
1.3 **Repeatable lease/alarm writes.** `retry.go` resends `LeaseGrant`, `LeaseRevoke`, `Alarm` after
   `Unavailable`, which may follow an applied attempt: `Grant` may grant two leases, `Revoke` may
   answer `ErrLeaseNotFound` for a lease it revoked; their updates are persistent (KV writes stay at
   most once). Alt.: the fork makes them non-repeatable (an upstream question: etcd treats them as
   idempotent). 1c D1/Q2, `batch-1c.md`; `top.md` §1, K4. **Now:** persistent updates.
1.4 **1c's client scope premises**: `RoleGrantPermission`'s type among the three (`permTypeM`),
   `AlarmDisarm` of a model alarm (`alarmKindM`), `LogConfig` without `Logger` out of scope, auto-sync
   only with `ETCD_VERIFY` off, `Status` only with the endpoints token. Accept as filed scope
   restrictions? `batch-1c.md` Q3, round 1. **Now:** premises.
1.5 **The in-process client (`v3client`: v3lock, v3election, the gateway's adapter).** Its watches are
   out of scope (the adapter's pipe passes message pointers; both ends read fields after `Send`).
   Options: restate `Send` at both ends as a transfer with read-only shares, 1b and 2a adjusting their
   laws, plus a pipe realization of the stream slots (no batch owns the adapter); or leave them out.
   Also open with it: `isClient_conn` is false for an in-process client, and a principal for an
   unissued token (`tokenUnissued`, 3d). 2b round 1, 1c round 1 items 2-3, 2a round 1 "Still open",
   `integration-I1.md` needs 3-4; `batch-2b.md`, `batch-1c.md`. **Now:** out of scope.
1.6 **Client-certificate principals.** With `ClientCertAuthEnabled`, a token-less request's principal is
   its certificate's CN. W0 covers it only when the client's certificate names its own principal (a
   scope premise of `connOk`: one identity per client); otherwise
   `nonissues/etcd-write-tls-principal-auth-enable.md` (a write proposed with auth off, applied after
   `AuthEnable`, runs as the certificate's user). Options: accept the scope premise, or take
   `ClientCertAuthEnabled = false` at `NewServer`. 2b round 1, 2c round 1 "Still open", W0 round 5;
   `batch-2b.md`, `batch-2c.md`. **Now:** the scope premise.
1.7 **Streamed ranges** (`GetStream`): the model says only what a default-order stream returns; sorted
   or filtered streams' contents and every stream's counts are open
   (`issues/etcd-rangestream-sort-none.md`); 2c's `RangeStream` takes `rangeStreamOk` (default order,
   no revision filters). Enough for Kubernetes. Want a stronger stream model? W0 Q3, 2c round 1;
   `batch-W0.md`. **Now:** default order only.
1.8 **Leasing KV: weak contract or the fixes** (see §6 F5). Also: linearizable cached reads (the
   package doc's claim) need a time model and a premise that every writer of the data keys is a
   leasing client (the old `LeasingProtocol`). 1e D1-D2, round 1; `batch-1e.md`. **Now:** the pinned
   code's weak contract (`lkvMarks`/`lkvClean`, cached answers serializable only for unmarked keys).
1.9 **Leasing's cache reader slots**: each read-locker takes a thread token, but the pool needs
   `threadBound` below the `RWMutex`'s reader limit (`2^29`), which nothing supplies (the old `NewKV`
   took `ThreadBoundLe GF (2^29)`). Who owns the fact (the bounds plan's owner)? 1e Q1, `batch-1e.md`.
   **Now:** dropped from the specs.
1.10 **Recipes.** `dbPerm`'s guards fit a one-round use of a barrier key only (a stronger guard needs a
   round notion the code lacks); `Dequeue` errors drop the caller's update, `RemoteKV.Delete` on a
   deleted object too (margins). Accept? 1f D3 and open questions, `batch-1f.md`.
1.11 **The cache (1g).** (a) Make the cache a drop-in `Watcher` (unify with 1b's `watchChAt`, a
   cache-specific cancel arm; five differences recorded) or keep its own `cacheWatchAt`; (b) confirm
   linearizable freshness as an anchor (`etcdLb γ σ0` in `Get`'s pre) rather than the caller's update;
   (c) confirm `New` taking `etcdPeek γ` (a new premise on a client-facing spec). 1g D1-D3,
   `batch-1g.md`; `integration-I1.md` table. **Now:** own vocabulary, anchor, `etcdPeek`.
1.12 **`txnlin`'s scope** (`top.md` §2): a compare-only transaction is answered from a stale view
   (`issues/etcd-txn-empty-serializable.md`), so the example's generator must not send one or its model
   must accept stale answers. Which? `notes/specs-only/top.md`.
1.13 **`Mutex`'s guarantee is revision fencing, not time** (`top.md` §2, W0 D2; the recipes' "no one
   acquires while I hold" likewise, 1f D2): time-based exclusion only under `EnvCfg.leaseExpiry =
   false` (5.3). Accept? `batch-W0.md`, `batch-1f.md`.

## 2. Raft

2.1 **`ConfigOk`'s scope restrictions**: `ReadOnlySafe` only (lease reads need clocks), no
   `AsyncStorageWrites` (async would need a queue of hand-outs in `LogState`), conf-change validation
   on. Keep as filed scope restrictions? R1 Q1, R2, R3 round 1; `batch-R1.md`.
2.2 **`MaxInflightMsgs ≤ 2^62`** in `ConfigOk`: the ring's `int` arithmetic would wrap above it in
   Perennial's model (Go cannot allocate such a ring; etcd uses 4096). Alt.: a step or memory bound
   argument (no spec has one). R4 Q1, `batch-R4.md`; `integration-I2.md`. **Now:** in `ConfigOk`,
   marked open.
2.3 **The term/index bound and raft's sort bound** (merged into 5.1).
2.4 **A storage is attached once**: `Stop` does not give the storage back; every user restarts on a
   new storage from its durable state. Alt.: `Stop` returns the contents (every storage update gated
   by `nodeRunning`). R1 Q2, `batch-R1.md`.
2.5 **`StartNode` on a non-empty storage** (Go warns and restarts) is excluded (`S StorState.empty`);
   etcd calls it only without a WAL. Accept? R1 Q3.
2.6 **Configurations ahead of the log.** (a) A restart's configuration above the WAL's commit (etcd
   restarts at the backend's consistent index): adopted, `RestartNode`/`NewRawNode` take the
   configuration at any committed `a ≥ max off applied`; (b) a snapshot whose configuration is ahead of
   its index (`nonissues/etcd-replay-snapshot-confstate-ahead.md`): adopted, `snap_make` at any
   committed point at or after the index. Both put a safety obligation on R2's proof (a tracker at a
   committed configuration ahead of the commit). Alt.: `a ≤ hs.commit` and snapshots at their own
   configuration as scope restrictions, under which etcd's restart after such a crash and snapshots
   during replay are not covered (or etcd fixed). R1 Q6-Q7, `batch-R1.md`. **Now:** adopted.
2.7 **A crash's vacancy** (`nodeVacant` after a process crash): from the adequacy theorem's crash rule
   (assumed), or should raft export a crash law? R1 Q8, `batch-R1.md`. **Now:** the crash rule's
   (`crashGone`, 2e round 2).
2.8 **Crash restart scope `confAboveOk`** (at most one conf-change entry above the stored commit) and
   no crash during a snapshot-carrying batch's write. etcd's WAL writes entries, then the state, then
   one fsync: a crash in between can break `confAboveOk` (a lagging follower catching up across several
   member changes in one `Ready`), letting a restarted node win an election counted in an older
   configuration: `issues/raft-commit-lost-with-entries-kept.md` (reproduced). Options: accept the
   scope (`crashScope`, an environment premise of `disk_crash`), or treat it as a blocking bug and fix
   (§6 F8); for snapshots, extend R1's crash law to snapshot batches. R1 Q10 and round 3, 2e Q2 and
   round 2, `integration-I2.md`; `batch-R1.md`, `batch-2e.md`. **Now:** `crashScope` premise; K6 holds
   only within it.

## 3. Server

3.1 **Joins and membership changes use single-use peer-URL sets.** A removed member's URLs can never be
   given to a member again ("replace a failed member at the same address" is out of scope); every
   `MemberAdd`/`MemberUpdate` the program makes takes the set's right (a workload premise). Alt.: W0's
   original per-id right minted at the add's commit, plus a premise that no `MemberUpdate` moves URLs
   onto or off a pending joiner (same kind of premise, more bookkeeping). 2e Q1 (revised), F12;
   `batch-2e.md`. **Now:** single-use sets (A15).
3.2 **etcd's own peer handler** (`etcdhttp.NewPeerHandler`, embed's): a join through it needs its spec
   (`/members` from the applied view); the repository's starters serve only the raft handler, with
   which a join always fails. Specify it, or keep joins out of the examples? 2e Q8.
3.3 **A failed `NewServer` loses the start right** (a half-made WAL or backend; a started raft node
   leaks if the transport fails): a program cannot retry a failed start. Accept? 2e Q3.
3.4 **`bootstrap`'s scope**: excludes `--force-new-cluster` and discovery; trusts remote peers'
   membership answers (`GetClusterFromRemotePeers`, `isMemberBootstrapped`) to be `γ`'s members'.
   Accept? 2e Q4.
3.5 **Member configuration that must agree**: (a) `--max-learners` could decide a learner add
   differently per member: premise that all share it? (2e Q5); (b) `ClusterVersionSet` panics on an
   unparsable version or one above the member's binary (`clusterVerOk`): a cluster invariant (the
   leader proposes the minimum of the members' versions) or a deployment premise (no member runs a
   binary older than the cluster version) (3a D4, "2e's to settle"). `batch-2e.md`, `batch-3a.md`.
   (Lease TTLs: A6.)
3.6 **Requests in flight at a stop, beyond the gate (A7).** (a) `LeaseServer.LeaseKeepAlive`'s
   context-done path returns while its goroutine may still be in `LeaseRenew` holding a `srvGate`
   share: options, 2c's `LeaseRenew` without the gate (it touches nothing `Cleanup` closes) or a fork
   change; (b) `maintenanceServer.Snapshot` reads the backend without a gate share (the same race as
   `issues/etcd-read-after-backend-close-panic.md`). `integration-X.md` open items 1, 3.
3.7 **The TLS path lends no run resource** (`Grpc.startHTTP`): a member serving clients over TLS cannot
   run handlers over 2c's request path from these specs. Needs net/http's handler pool to lend a run
   resource too (2f's `Http.handlerPool`): a protocol decision. `integration-X.md` open item 2.
3.8 **The watch wire-request scope.** The server's watch contract covers clients that send
   `WatchId = 0` (no caller-chosen id: an explicit id can reuse a canceled watch's id and receive its
   queued events, `issues/etcd-watch-id-reuse-stale-events.md`), no empty/`nil` oneof (also the
   translator bug, 7.3), and a non-negative start revision (v3rpc refuses negative ones;
   `nonissues/etcd-mvcc-watch-negative-start-rev.md`). etcd's Go client and grpc-proxy meet it; the
   grpc-gateway and raw clients are outside. Alt.: a per-stream weakening (an empty oneof a no-op,
   which needs 7.3; an explicit id's guarantees while the id was never used), which would serve the
   gateway too. 2b D1 and round 1, 3f Q2-Q3; `batch-2b.md`, `batch-3f.md`. **Now:** the scope premise.
3.9 **Synchronization registries take client predicates** (`listAt`'s and `timeListAt`'s `P`, as
   Perennial's lock/channel idioms): a departure from "TaDa, not HoCAP" for generic primitives. Alt.:
   ghost tokens per id threaded by every client. 2c D4, `batch-2c.md`. **Now:** predicates.
3.10 **Lease API design** (confirm): the checkpointer's contract restricts its errors to `nil`/
   `ErrNotPrimary` (`ckptOk`) so `Renew`'s errors are exact (alt.: "any error" in one more disjunct);
   the range deleter's contract `rdOk` carries the caller's `P`, `D`, `Q` (alt.: state `Revoke` over
   mvcc's vocabulary, coupling to 3e); readers' history `lessorAt` is a new abstraction beside the
   writer's token. 3c D2-D4, `batch-3c.md`.
3.11 **The auth store's handle names W0's `Cluster`** (`authStoreAt st γ γa`). Alt.: a cluster-free
   store API (a saved predicate fixed at creation, or a client-owned history through an atomic update:
   more general, a parameter for every caller). 3d Q4, `batch-3d.md`. **Now:** the concrete cluster.
3.12 **An inverted permission range's refusal (`Apply.invRefused`) stays provisional.** The cache's
   answer depends on the interval tree's insertion order (an unstable sort), so it is not a function of
   W0's `AuthState`; a sound exact form needs a per-index `cacheInvRefused` threaded through
   `isRangeOpPermitted`, `checkKeyInterval`, `cacheEntry` (costly). Do it, or keep the provisional
   name used only as "the cache's answer at the writer's state"? `integration-I5.md` "Left open"
   (a) and 3a's follow-up 1.
3.13 **The snapshot database image's meaning is fixed at the network's allocation** (`net_alloc`,
   `snapImg ν i bs ∗-∗ Img i bs`): the approved kind of departure from TaDa. Alt.: a client-owned set of
   images every server threads through `SendSnapshot`. 2f Q1, `batch-2f.md`. **Now:** fixed predicate.
3.14 **The HTTP boundary's replay ticket was narrowed** (only `onceOnly` requests carry one: the old
   statement was false for a replayed `GET`). A trust statement change to accept. 2f Q3, F2.
3.15 **The snapshot sender's timeout drain** (`snapshot_sender.go:169`): `GracefulClose` from a
   `time.AfterFunc` goroutine reads the body concurrently with `io.ReadAll`; 2f needs a shared reader
   of trivial knowledge (requested). Not a panic (Go's body reads are locked). 4b Q4, `batch-4b.md`.

## 4. Storage & bbolt

4.1 **The meta page after a crash (4c-D1, "the user's decision").** Under OsFs's crash model every byte
   not known durable is arbitrary after a crash, so a meta slot may hold any 80 bytes, including a
   valid checksum for a state that never existed: `boltCrash.spec` is false under OsFs as it is.
   Options: (a) add the narrow physical rule to OsFs's crash relation (`GooseLang/Ext/OsFs/`: a sector
   changed by at most one `pwrite` since the last successful sync holds its durable bytes or that
   write's), with the kernel argument in `Impl.lean` (`folio_wait_stable`), benefiting every OsFs
   client; (b) a crash premise visible in every bbolt closed theorem (`osFsSemWith Q`, as minibolt's
   P1). `batch-4c.md` 4c-D1. **Now:** undecided; the spec is true under either.
4.2 **The commit's prophecy (4c-D2)**: resolved on "the meta page was written" (its mapped txid), not
   `err == nil`, via a prophecy patch in `etc/proph-patches/bbolt/` (`etc/prophcheck` must admit that
   read: not checked). Alt.: a third update. `batch-4c.md`.
4.3 **The durable state in the client's state (4c-D3, D4)**: `BoltSt` carries `dur`, `busy`, `lost`
   (alt.: a bbolt-owned "synced" witness, unsound under `NoSync`; a synced flag, raced by `DB.Sync`);
   files named once per generation, the state living across opens. Confirm. `batch-4c.md`.
4.4 **The txid bound across crash generations.** Receipts are counted per generation (`Open`'s
   `2^62`), and the crash law hands `fileHolds` on, so no fixed bound survives unboundedly many
   crashes. Options: txid `< 2^63` plus a premise on the number of generations, or a bound carried in
   `BoltSt`. `integration-I7.md` open item 1.
4.5 **Durability through the batch lock's resource**: the client chooses at `New` the lock's
   resource `Pk` and its commit step `commitOk`, which every commit (including the run loop's) runs
   (alt.: a persistent atomic update handed to `New`, the same thing spelled differently). Accept?
   4a Q2, `batch-4a.md`.
4.6 **`lg.Fatal` paths in the backend** (puts into a missing bucket, an empty key, a failed commit):
   the specs take no premise (`Fatal` never returns). Is an exit acceptable in the closed theorems, or
   should premises exclude it (`beMade` on writes)? 4a Q4, `batch-4a.md`; `integration-I6.md`
   ("Not taken").
4.7 **The schema is stated over transaction contracts**: the callers' per-concern slots (3c's
   `beLeases`, 3d's `authBackendAt`, 2d's `beStoredCI`) are their realizations over 4a's parts, not
   schema predicates. Confirm. 4b Q1 and "The schema's design", `batch-4b.md`.
4.8 **bbolt API choices (4d)**: no opaque page predicate in `BboltCommon` (transparent decoders over
   byte points-tos); `ReleasePendingPages` leaves open which extra releasable pages it frees (margin);
   local bound `flMaxIds = 2^59` on counting/sorting freelist methods. Confirm. 4d D1, D3, D4,
   `batch-4d.md`.
4.9 **bbolt's scope restrictions**: read-write open, default page size, `Mlock` off, `MmapFlags`
   `0`/`MAP_POPULATE`, bucket names within `MaxKeySize`
   (`nonissues/bbolt-bucket-name-length-unchecked.md`), entries within `bboltEntryMax`, `Prev` on read
   transactions only (`issues/bbolt-cursor-prev-empty-leaf.md`), `WriteTo` with a writer without
   `ReadFrom`. Accept? `batch-4c.md` "Scope restrictions kept".

## 5. Trust boundaries & environment premises

5.1 **One execution step bound, fixed by the adequacy theorem.** Several bounds need it: W0's
   `etcdState_revFits`/`sizeFits` (K7's step budget, since etcd never refuses at `2^63`); raft's term
   and index bound (`cluster_alloc.spec`, `∀ [ReceiptBoundLe GF (2^63)]`), which would also discharge
   R3's `2^63` range premises, its index-wrap premises and R4's sort bound (`size ids ≤ 2^62`); mvcc's
   watch-id counter (`ReceiptBoundLe GF (2^48)`). Options: add the binder to `cluster_alloc`'s
   statement; a Perennial-level fact that live slices total below `2^63` (7.2); local filed scope
   restrictions; a size bound in `Membership.Valid` with `changeV2` refusing past it (a refusal Go
   does not make). R1 Q9, R2 Q1, R3 Q2-Q3, R4 Q2, 3f round 1 S2, `top.md` K7, `integration-I2.md`.
   **Now:** in `cluster_alloc`'s docstring only, not its statement.
5.2 **Message size premises.** grpc-go's codec panics on an encoding over `2^48` bytes. Now:
   the opaque workload premise `Grpc.msgsFit` where connections and servers are made (closed
   theorems conditional on it; may subsume K8's `--max-request-bytes`); `MarshalConfChange`'s
   `c.wireBound < Proto.marshalMax` on `ProposeConfChange` (a client-facing premise); mvcc's put marshal
   of key and value (`encSize < 2^48`) and the storage's entry bound: still open whether a workload
   premise on the store's producer or the gRPC request bound carried down. Alt.: per-call size
   premises (W0 refused), or a grpc fork. 2a D1, W0 Q4, 3h Q3, 3e Q2, `integration-I6.md`;
   `batch-2a.md`, `batch-3h.md`, `batch-3e.md`.
5.3 **`EnvCfg.leaseExpiry = false`** (no lease expires during the run) is a trusted deployment premise
   about time, taken by the program: a timeless proof cannot show the lessor never revokes. Keep the
   mode? Without it, keep-alives and `Session.Done` say nothing, and lease-based exclusion is fencing
   only. W0 D2, `top.md` K2, 2e Q6, 1d Q5, 1e D2, 1f D2/C-4.
5.4 **The peer network's closed world**: every URL the transport is given is reserved for the
   network's protocol (`peerAddr`); `addrFree` is issued for at most one string per socket, never port
   0, and no proxy relays peer traffic (aliases are the one case the bind cannot settle). Acceptable,
   or should the boundary model address resolution? 2f Q2, Q6, `batch-2f.md`.
5.5 **The HTTP/gRPC handler pool**: `Serve` takes `handlerPool p n` of the caller's thread tokens; the
   physical premise "at most `n` concurrent handlers" is assumed. Alt.: the old client-supplied
   `httpProcSlots`. 2f Q4/Q7, 2a D3/round 1 F2.
5.6 **Request-id freshness across one member's runs** is a trusted assumption of `idutil.Next`'s model
   (`nonissues/etcd-request-id-restart-reuse.md`; the true condition: 256 ids per ms). Across members:
   an allocation premise (`idSpace_alloc`). 2c D5, `batch-2c.md`.
5.7 **Passwords**: the stored credential is modelled with trusted opaque `pwHash`/`pwMatch` (bcrypt), so
   the model state is a function of the log. 3a D3, 3d round 1, W0 round 5.
5.8 **Unowned helper libraries.** Specified only by their use in sketches, assumed panic-free or
   trusted: `pkg/v3/ioutil`, `httputil.GracefulClose`, `pbutil`, `client/pkg/v3/transport`
   (`NewTimeoutTransport`, `NewListenerWithOpts`, `IsClosedConnError`), `xiang90/probing`,
   `x/time/rate`, `Masterminds/semver`; prometheus metrics, the otel tracer, `verify.Assert`,
   `math/rand.Int63n`, zap; `fmt.Sprintf` forms, `strings.Split`, `time.Now().UnixNano()`,
   `errors.Is`. Who owns them (and their specs)? 2f Q5, 2b open questions, 1f open questions.
5.9 **Configuration scope premises at `NewServer`/the client** (each filed): `--max-txn-ops ≤ 4999`,
   `--max-request-bytes` below the keys-only amplification bound, `Compact` at a revision other than
   `0` (W0 Q1: alt., model a first `Compact(0)` as a no-op and accept a false spec in that corner),
   `watchIntervalCfgOk` (your 2026-10 "skip"), rafthttp's `ConnReadTimeout`/`ConnWriteTimeout ≥ 5s`,
   no distributed tracing (`traceutil.Init` never called: 4b Q3). `top.md` K8, `batch-W0.md`,
   `batch-2c.md` D6, `batch-2f.md` round 1, `batch-4b.md`.

## 6. Fork fixes proposed for real etcd/raft bugs

Each: the bug, the proposed fix, and what the specs do without it. Say which to take into the pinned
fork (then the specs tighten as noted).

F1. **Auth races on reads** (`nonissues/etcd-doserialize-auth-enable-race.md`,
   `nonissues/etcd-auth-revision-before-visible.md`): re-check the permission after the read when auth
   is enabled by then; bump the auth-revision atomic after the batch transaction's `Unlock`. **Now:**
   the model admits both (A2). 2c D1, 3d Q1/round 1 Q2.
F2. **`WithRoot` root-token collision panic** (`nonissues/etcd-auth-withroot-token-collision-panic.md`,
   the default simple provider): `assignSimpleTokenToUser` returns an error on an existing token
   (`WithRoot` already maps it). **Now:** `rootTokOk` premise, given only by the no-op and JWT
   providers: auth-on members with the default `--auth-token` have no usable `WithRoot` spec (the
   lessor's revocations, the health checks). Alt.: a probabilistic premise (against PRINCIPLES).
   3d Q2/round 1 Q1.
F3. **Backend closed under in-flight reads** (`issues/etcd-read-after-backend-close-panic.md`): a gate
   in Go (`Cleanup` waits for readers; later reads fail with `ErrStopped`). **Now:** the drain
   premise (A7), with 3.6's two gaps. 2e Q7.
F4. **A `PrevKv` watch's first events without `PrevKv`** (`issues/etcd-watch-prevkv-before-created.md`):
   a flush-time `prevKV` lookup in `sendLoop`, or `sws.mu` held across mvcc's `Watch` in `recvLoop`;
   then the strong `prevOk` holds and Kubernetes' watches are served exactly. **Now:** the loose
   window. 2b round 1.
F5. **The leasing KV**: the six `leasing-*` branches on upamanyus/etcd, `put`/`delete` not resending
   after an error (`nonissues/leasing-write-resend-after-error.md`), the `WithPrevKV` fix
   (`issues/leasing-delete-range-drops-prevkv.md`, blocks-proof: yes). With them writes take W0's
   exclusive update and every cached answer is serializable (no marks). **Now:** the pinned code's weak
   contract. 1e D1, round 1.
F6. **Stale read-buffer copy after a commit** (backend `ConcurrentReadTx`): `bufVersion++` in
   `readTx.reset`, branch `fix/etcd-backend-read-buffer-cache-stale-after-commit`. **Now:** weaker
   concurrent-read specs (single keys, lingering values). 4a round 1 Q7.
F7. **`MsgApp` slice aliasing** (`nonissues/raft-msgapp-inprocess-aliasing.md`): clip in
   `logSliceFromMsgApp`. **Now:** `msgRecv` (A12).
F8. **Commit lost with entries kept** (`issues/raft-commit-lost-with-entries-kept.md`): raft's campaign
   guard scanning the whole stored log above `applied`, or etcd writing the commit with the entries
   atomically (or syncing the commit before acknowledging a second pending conf change). **Now:**
   `crashScope` (2.8).
F9. **Two merged snapshots of one index** (`nonissues/etcd-merged-snapshot-same-index-image.md`,
   blocks-proof: yes; Go names the file by index only): a fork fix would remove the scope premise "a
   member never saves two merged snapshots of one index with different points before installing one".
   2d Q3.
F10. **Concurrent `RemoveMember`s removing the last voter** (`nonissues/etcd-concurrent-remove-last-voter.md`,
   blocks-proof: yes): a fork fix would remove the premise "no two `RemoveMember` calls in flight".
   2d Q3.
F11. **`LeaseTimeToLive`'s keys mid-apply** (`nonissues/etcd-lease-keys-mid-apply.md`): a fork fix
   instead of W0's weakened step (A18). 3c D1.
F12. **`Mutex.Lock` on a recreated key** (`issues/mutex-lock-recreated.md`): upstream PR #22617; then
   `Lock`'s post would be `holdsAt` at the header's state. **Now:** the fork's code (`lockedSince`:
   create revision `≥ c`); fenced writers see no difference. 1d Q4.
F13. **Hash's unlocked current-revision read** (`issues/etcd-mvcc-hash-currentrev-race.md`, fixed
   upstream): cherry-pick #22609 into the fork. **Now:** open alternative, recorded. 3e round 1.
F14. **A `rev = 0` watch across a reconnect** (`issues/etcd-watch-current-resume-past-event.md`): the
   member would return its registration revision so the client can resume exactly. **Now:** the
   watch's position is a floor from the call (`WatchPos.floor`), completeness from the first event.
   1b D2.
F15. **Repeatable lease writes** (1.3): make `LeaseGrant`/`LeaseRevoke` non-repeatable (upstream
   question).

## 7. Perennial / translation changes

7.1 **A functional `sort.Sort` spec** (the output as a function of input and comparator; true of
   pdqsort). Needed so a range's answer is a function of the store: 2c's read registry, 2d's
   commit-time answers (`applyStep_fun`). **Now:** `Txn.goSort` named, opaque (`goSort_sorted`),
   unprovable against Perennial's current "sorted permutation". Alt.: keep the relation; the registry
   fires every allowed answer, and 2d needs a prophecy of the apply's answer. 3b D1 (recommends the
   Perennial change, to record in `notes/perennial-changes.md`), 2c open questions.
7.2 **`sort.Sort`'s `2^62` size premise / slice lengths** at `Revoke`/`Leases`, the freelist's
   `ReleasePendingPages`, raft's sorts and R3's read ranges: a Go slice cannot exceed it, but
   Perennial's slice model does not say so. A Perennial fact that live slices total below `2^63`
   elements would discharge them. Also: `Leases`' `sort.Sort` uses a time-dependent `Less`
   (inconsistent order; Go stays in bounds). 3c round 1, 4d D4, R3 Q2, `integration-I5.md`.
7.3 **Goose: bind a type switch's variable in `default:`** (`recvLoop`'s `default:` branch reads `uv`,
   unbound in the translation; stuck in the model). Forces part of 3.8. 2b finding 2.
7.4 **Untranslated etcdserverpb/mvccpb declarations** (`Code/go_etcd_io/etcd/api/v3/{etcdserverpb,mvccpb}.toml`,
   each blocking a stated spec or law): `RangeStream` client/handler/stream types;
   `NewClusterClient`, `NewMaintenanceClient`, their stubs and `_Cluster_*`/`_Maintenance_*` handlers;
   structs `Member`, `MemberAddResponse`, `MemberListResponse`, `StatusResponse`, `AlarmResponse`;
   `Event.IsCreate`/`IsModify`; `RangeRequest_SortOrder_name`/`_SortTarget_name`. Translate them?
   `batch-3h.md` "Consolidated translation request".
7.5 **OsFs's crash relation** (this repository's `GooseLang/Ext/OsFs/`, trust base): 4.1's option (a).
7.6 **A bbolt prophecy patch** (`etc/proph-patches/bbolt/`) reading the mapped meta page's txid: 4.2;
   `etc/prophcheck` must admit the read.
7.7 **Opaque predicates without their heap binder** (branch-wide): an `opaque p : IProp GF :=
   iprop(True)` under section variables does not take `hG`, so it cannot be realized over the heap
   (`Backend.beFile`, `Mvcc.kbData`, ...). Fix: put the binders in each opaque's own signature (also
   settles 4a's `[HasExt osFsExt]` gap). The README convention causes it. `integration-I6.md` "Two
   findings left open" 2.

## Real bugs found

New in `issues/` on this branch (each with a Go test), relative to `037bf21c75`:

- `issues/etcd-client-dial-empty-endpoints.md`: `Maintenance.Status` panics after `SetEndpoints()` with no endpoint, and races it (blocks-proof: no).
- `issues/etcd-mvcc-watch-compacted-after-progress-restore.md`: after a follower restores a snapshot, a watch a progress declared current at `P` is cancelled as compacted at `P` (no).
- `issues/etcd-rangestream-auth-revoked-midstream.md`: a streamed range keeps sending keys after the user's read permission is revoked, then fails (no).
- `issues/etcd-v3lock-watch-shared-stream-principal.md`: with auth on, a waiting v3lock `Lock` fails with permission denied while another user waits (shared stream's principal) (no).
- `issues/etcd-watch-current-resume-past-event.md`: after a reconnect, a watch from the current revision delivers an event committed before it (no).
- `issues/etcd-watch-prevkv-before-created.md`: a `PrevKv` watch's first events can lack `PrevKv` when the key is written during creation (no).
- `issues/leasing-delete-fromkey-skips-revoke.md`: a `WithFromKey` delete does not make other leasing clients drop cached keys (no).
- `issues/leasing-delete-range-drops-prevkv.md`: a range delete through the leasing KV ignores `WithPrevKV` (yes).
- `issues/raft-commit-lost-with-entries-kept.md`: a crash after a `Ready`'s entries are written but before its `HardState` lets two nodes commit different entries at one index (no; moved from `nonissues/`).
- Updated: `issues/etcd-mvcc-hash-currentrev-race.md` (proof section: `mvccRestoreGate`, #22609).

New in `nonissues/`:

- `bbolt-commit-after-failed-sync`: a commit succeeding after a failed sync can leave a database a crash corrupts (no).
- `etcd-applied-index-stale-after-snapshot`: `AppliedIndex()` lags after a snapshot install until the next entry (no).
- `etcd-apply-quota-nospace-after-write`: an over-quota put/txn/grant is applied and answered `ErrNoSpace` (no).
- `etcd-auth-empty-range-end-point-check`: a non-`nil` empty `RangeEnd` is checked for its key alone but reads from it on (yes).
- `etcd-auth-password-72-byte-prefix`: a 71/72-byte password also accepts longer extensions (bcrypt) (no).
- `etcd-auth-revision-before-visible`: a read can return data written after its permission was revoked (yes).
- `etcd-auth-withroot-token-collision-panic`: two internal root tokens with the same random prefix panic the member (yes).
- `etcd-cache-get-keys-only-ignored`: `Cache.Get` with `WithKeysOnly` returns values (no).
- `etcd-cache-rewatch-from-original-revision`: after a clean upstream close the cache re-watches from its first load's revision (no).
- `etcd-cache-waittillrevision-goroutine-outlives-close`: a consistent `Get`'s timeout goroutine outlives `Close` (no).
- `etcd-client-getstream-abandoned-leak`: `GetStream`'s goroutine blocks forever when the caller stops reading (no).
- `etcd-client-keepalive-close-never-closed`: a `KeepAlive` racing the lessor's `Close` can return a never-closed channel (no).
- `etcd-client-lessor-nil-logger`: `NewLeaseFromLeaseClient(remote, nil, ttl)` panics on a keep-alive stream error (no).
- `etcd-compact-admin-check-lagging-member`: a user whose root role was revoked can still compact through a lagging member (no).
- `etcd-concurrent-remove-last-voter`: two concurrent `RemoveMember`s can remove the last voter and panic every member (yes).
- `etcd-doserialize-auth-enable-race`: a read started with auth off can return a key written after `AuthEnable` to an unpermitted client (no: the model covers it).
- `etcd-embed-raft-read-timeout-ticker-panic`: `--raft-read-timeout` below 3ns makes every stream writer panic (no).
- `etcd-lease-keys-mid-apply`: `LeaseTimeToLive` with `Keys` can return a key set no revision had (yes).
- `etcd-lease-setcheckpointer-once`: `SetCheckpointer` is safe only once, before the lessor is primary (no).
- `etcd-merged-snapshot-same-index-image`: two merged snapshots of one index can leave a follower's backend and raft configuration apart (yes).
- `etcd-rafthttp-peerurl-comma-split`: a peer URL with a comma makes the receiver's `AddRemote` panic on every request (no).
- `etcd-rangestream-count-compacted`: a streamed range at the current revision can fail with `ErrCompacted` before sending anything (no).
- `etcd-rangestream-negative-revision-unpinned`: a streamed range at a negative revision reads a new revision per page (no).
- `etcd-replay-snapshot-confstate-ahead`: a snapshot taken during WAL replay records a configuration later than its index (no).
- `etcd-v3client-defragment-nil-notifier`: `Defragment` through the in-process client panics (no).
- `etcd-v3election-proclaim-rev-zero`: a `Proclaim` with leader revision 0 creates the leader key (no).
- `etcd-v3lock-auth-cleanup-unauthenticated`: with auth on, a canceled `Lock`/`Campaign` leaves its waiter key behind (no; unconfirmed).
- `etcd-write-tls-principal-auth-enable`: a write proposed with auth off and applied after `AuthEnable` is checked as the TLS certificate's user (no).
- `grpcproxy-leasing-auth-cached-read`: with the proxy's leasing prefix and auth, a cached key is served to a user without read permission (no).
- `leasing-gatherops-spare-capacity`: a nested transaction writes into the caller's `Op` slices (no).
- `leasing-monitorlease-spin-done-ctx`: a lease monitor spins when its watch ends before a revoke (no).
- `leasing-txn-own-lease-key-livelock`: a transaction may retry forever on the client's own lease key after an error (no).
- `leasing-write-resend-after-error`: a write that failed and was resent may take effect after a later write (yes).
- `probing-addhttp-preconditions`: `Prober.AddHTTP` panics on a non-positive interval, empty URL list or unparsable URL (no).
- `raft-heartbeat-resp-short-context-panic`: a leader panics on a heartbeat response context shorter than 8 bytes (no; with a test sketch in its directory).
- `raft-ismsginarray-negative-type-panic`: `IsLocalMsg`/`IsResponseMsg` panic on a negative `MessageType` (no).
- `raft-msgapp-inprocess-aliasing`: a stepped `MsgApp`'s entries slice is adopted, so its spare capacity must be the receiver's (no).
- `recipes-dbarrier-leave-without-key`: `DoubleBarrier.Leave`, `RWMutex.Unlock`/`RUnlock` panic when the process created no key (no).
- Updated: `bbolt-hashmap-init-empty-stale-cache` (the four specs' premise), `bbolt-txid0-reader-release` (mechanism: two calls; the `2^64-1` mirror), `etcd-client-dialoptions-unary-interceptor` (the gRPC proxy).
