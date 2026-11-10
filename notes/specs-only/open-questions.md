# Open questions for the user (specs-only run)

Every decision the specs-only run (batches W0, 1b-1g, 2a-2f, 3a-3h, 4a-4d, R1-R4; integrations
I1-I7, X, Y) left to the user, compiled 2026-11-09 from `notes/specs-only/batch-*.md`,
`integration-*.md` and `top.md`. Paths below are relative to the repository root; a batch's report is
`notes/specs-only/batch-<id>.md`. Each item gives the question, the options and their costs, who raised
it, and what the specs assume today ("**Now:**"). A question several batches raised appears once,
listing them all. Questions a later round settled are left out; technical gaps that need no decision
(provisional names, unrealized slots, sketches still to check) are not listed: see each report's
"Not done" and "Needed from" sections.

The verification round's repairs (`notes/specs-only/verify/repair-*.md`, 2026-11-09) added section C
(at the end) and the **verify-round:** notes under the entries they settle or change. The re-review
rounds' repairs (`verify/repair2-*`, `repair3-boot`, `cleanup`, `repair4-*`, `repair5-crash`, second
half of 2026-11-09) added section D and the **re-review:** notes; entries they replace are marked
**Superseded**, not deleted.

Sections: [A. Decided by the coordinator](#a-decided-by-the-coordinator-revisit-if-you-disagree) ·
[1. Top-level model & client](#1-top-level-model--client) · [2. Raft](#2-raft) ·
[3. Server](#3-server) · [4. Storage & bbolt](#4-storage--bbolt) ·
[5. Trust boundaries & environment premises](#5-trust-boundaries--environment-premises) ·
[6. Fork fixes proposed for real etcd/raft bugs](#6-fork-fixes-proposed-for-real-etcdraft-bugs) ·
[7. Perennial / translation changes](#7-perennial--translation-changes) ·
[Real bugs found](#real-bugs-found) ·
[C. Decisions from the verification round](#c-decisions-from-the-verification-round-2026-11-09) ·
[D. Decisions from the re-review rounds](#d-decisions-from-the-re-review-rounds-2026-11-09-second-half)

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
   **verify-round (re-review N1, `verify/R-A2-client-watch-lease.md`):** the description above was wrong for
   `TimeToLive`: a follower forwards it to the leader (`v3_server.go:636-676`), so only `Grant` and `Leases`
   answer from the member's own table; the per-member clause is dropped for `TimeToLive`.
   **re-review:** the single-member alternative is now in place, as a gated row: `TimeToLive`'s
   per-member clause holds under `soleMember γ ∗ peerLeaseServed γ` (W0's new persistent facts, from
   2e's `soleMember_intro` with `urlsReserve γ 1` and `peerLeaseServed_intro`), in 1c's `viaFact`, 2c's
   `srvLeaseFact` and 2a's `leaseFact`; the general per-member `TimeToLive` stays dropped. See D1, D8.
   (`verify/repair2-client.md` RR-1, `repair4-lease.md` F1.)
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
   **verify-round:** unchanged; server-core also states the `errorc` self-stop (A8-provability F3) as a
   scope in `run.spec`'s text (C46). (`repair-server-core.md`.)
A8. **mvcc's compactor `Rev()` and hashing.** `Rev()` without a reader token (option (a), then Y's
   persistent `mvccRevTok`); `Hash`/`HashByRev` take a share of `mvccRestoreGate`, so hashing excludes
   `Restore`. Alt. for hashing: `Restore` returns the old storage's slots except those of hashes in
   flight (cuts nothing off, more bookkeeping); for `Rev`: make the server wait for the compactor
   (a code change). (`batch-3e.md` Q1, Q3, round 1; `integration-Y.md` (2).)
   **verify-round:** still yours: `KV.Restore.contract`'s whole gate cannot be collected from
   unsynchronized hashers (A10 O1); server-core states "no hash during a snapshot install" as a scope
   in `applySnapshot.spec`/`run.spec`'s text until you decide (C46). (`repair-server-core.md`,
   `repair-mvcc.md`.)
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
   **verify-round:** `msgRecv` now has a producer, `RaftPb.msgRecv_intro` (from protobuf's `mergeDst`,
   which `Clone`/`Unmarshal` now give; C36), and rafthttp's decoders and `raftOk`'s `Process` deliver
   it (C39). (`repair-raft-conf-pb.md`, `repair-rafthttp.md`.)
A13. **A token provider's error in `Authenticate`'s apply is admitted, no provider flag**
   (`provErrResult`; the no-op provider always fails, JWT on signing). Alt.: an `aok` flag on
   `tokenProviderAt`, given by the simple provider only, letting `Authenticate.spec` drop the error
   disjunct. Cost now: 2c's `Authenticate` may return an error after its update fired.
   (`integration-I5.md` "Coordinator's decisions" 1; `integration-X.md` open item 4.)
A14. **Non-`nil` empty `RangeEnd`: a scope premise.** Filed `nonissues/etcd-auth-empty-range-end-point-check.md`;
   `CheckTxnAuth`/`checkTxnPermission` take `endsDecoded`/`opsDecoded` (what gRPC decoding gives).
   Alt.: a margin in 2c/3a at that input, or a fork fix of the auth check. (`integration-I5.md`
   "Coordinator's decisions" 2.)
   **verify-round:** extended to the client (C3: W0's and leasing's KV triples and `Cmp.WithRange`
   exclude such an end); `endsDecoded` is now a share of the message with the pure `endsOk` (C13).
   (`repair-client-core.md`, `repair-grpc-v3rpc.md`.)
A15. **The peer-URL right `urlsRight γ urls` lives in W0's `State.lean`** and is taken by the client's
   `MemberAdd`/`MemberUpdate`; spent even when the call is refused. (`integration-I1.md`, first
   section.) See 3.1 for the single-use question itself.
   **verify-round:** new law `urlsRight_norm` (the right survives `urlsNorm`); the server's
   `AddMember`/`UpdateMember` now give the right back on a refusal, while the client's calls still
   spend it (`reqRight`'s margin). (`repair-client-core.md`, `repair-server-core.md`.)
A16. **`IrrBody` (the raft request's model) is 3h's**, 2c's copy dropped. (`batch-3h.md` Q4;
   `integration-I4.md`.)
A17. **Watch exactness gated on `exactFrom`** (1b round 3, adopted downstream by I1): events are exact
   only when no revision up to the compaction changes a key twice (the sibling put/delete bug). Alt.:
   gate the condition into the watch's creation (the approved old design), or exclude such
   revisions in W0's model (false of the code). Users (1d `Observe`, 1f, 1g cache) carry it as an
   invariant clause. (`batch-3f.md` Q1; `batch-1b.md` round 3; `integration-I1.md`.)
   **verify-round:** narrowed (C9): `watchStep` and mvcc's `wStep` now say unconditionally that each
   delivered event is a history event the watch keeps; only exactness stays gated. Recipes' `Dequeue`
   value is ungated, its front still gated (C11). (`repair-client-watch.md`, `repair-mvcc.md`,
   `repair-client-users.md`.)
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
   **verify-round:** auto-sync is no longer an `ETCD_VERIFY` premise: `cfgOk` requires
   `AutoSyncInterval = 0` (C1); the other premises stand. (`repair-client-core.md` A2 S4.)
1.5 **The in-process client (`v3client`: v3lock, v3election, the gateway's adapter).** Its watches are
   out of scope (the adapter's pipe passes message pointers; both ends read fields after `Send`).
   Options: restate `Send` at both ends as a transfer with read-only shares, 1b and 2a adjusting their
   laws, plus a pipe realization of the stream slots (no batch owns the adapter); or leave them out.
   Also open with it: `isClient_conn` is false for an in-process client, and a principal for an
   unissued token (`tokenUnissued`, 3d). 2b round 1, 1c round 1 items 2-3, 2a round 1 "Still open",
   `integration-I1.md` needs 3-4; `batch-2b.md`, `batch-1c.md`. **Now:** out of scope.
   **verify-round:** still out of scope. The in-process client's lease and watcher constructors now
   take a ghost client `null` for readiness (C4); `tokenUnissued` unchanged (gaps); any new `ctxPrin`
   introduction must keep `ctxStreamKey_prin` (C8). (`repair-client-core.md`, `repair-client-watch.md`.)
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
   **verify-round:** unchanged; the cache's "no progress without `WithProgressNotify`" clause is left
   open (gaps). (`repair-client-users.md` C-F5.)
1.12 **`txnlin`'s scope** (`top.md` §2): a compare-only transaction is answered from a stale view
   (`issues/etcd-txn-empty-serializable.md`), so the example's generator must not send one or its model
   must accept stale answers. Which? `notes/specs-only/top.md`.
1.13 **`Mutex`'s guarantee is revision fencing, not time** (`top.md` §2, W0 D2; the recipes' "no one
   acquires while I hold" likewise, 1f D2): time-based exclusion only under `EnvCfg.leaseExpiry =
   false` (5.3). Accept? `batch-W0.md`, `batch-1f.md`.
   **verify-round:** now true (C10): `mutexEff`/`campaignEff` write only the session's key (`sessKey`)
   and `Mutex.Lock` orders create revisions, so holders of two sessions are exclusive in time under
   `leaseExpiry = false` (snippet `ReqMutexNoTwoHolders`); fencing only without it. What remains is
   5.3. (`repair-client-users.md` C-F2.)

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
   **verify-round:** `crashGone_intro` (from `srvRunning` at the crash) is now its producer, and
   `diskIdle_crash` carries an idle disk across. (`repair-server-core.md`.)
   **re-review (supersedes the verify-round line):** `crashGone`, `crashGone_intro` and
   `diskIdle_crash` are deleted. The vacancy now comes with `raftState`'s generation crossing (D18);
   there is one disk crash law, `disk_crash` (D21); per-generation tokens' exclusivity gives the
   generation's `crashed` (D28). (`verify/repair2-crash.md` N1, `repair4-raft-crash.md`.)
2.8 **Crash restart scope `confAboveOk`** (at most one conf-change entry above the stored commit) and
   no crash during a snapshot-carrying batch's write. etcd's WAL writes entries, then the state, then
   one fsync: a crash in between can break `confAboveOk` (a lagging follower catching up across several
   member changes in one `Ready`), letting a restarted node win an election counted in an older
   configuration: `issues/raft-commit-lost-with-entries-kept.md` (reproduced). Options: accept the
   scope (`crashScope`, an environment premise of `disk_crash`), or treat it as a blocking bug and fix
   (§6 F8); for snapshots, extend R1's crash law to snapshot batches. R1 Q10 and round 3, 2e Q2 and
   round 2, `integration-I2.md`; `batch-R1.md`, `batch-2e.md`. **Now:** `crashScope` premise; K6 holds
   only within it.
   **verify-round:** `crashScope` is gone: `disk_crash` is per generation and concludes the disjunct
   `crashOutOfScope γ ds` (`confAboveOk` broken, or a snapshot batch interrupted); raft's
   `raftState_crash` is split into two whole-record cases matching the WAL's `crashedMid`; the WAL and
   the snapshotter have crash laws (C40). The question stands. (`repair-server-core.md`,
   `repair-raft-core.md`, `repair-server-boot.md`.)
   **re-review (supersedes the verify-round line):** `crashOutOfScope` and the `crashScope` premise
   are deleted. The scope is stated over the WAL's records, `Wal.Recs.crashScopeOk` (the window
   between a snapshot record and the state record, plus `confAboveOk`), and enters the logic as W0's
   environment premise `Wal.crashInScope` (every crash leaves WAL records meeting `crashScopeOk`),
   taken by the WAL's crash laws and by `disk_crash`, which has no out-of-scope case. `raftState_crash`
   covers snapshot batches written not at all or wholly. The question (accept the scope or fix, §6 F8)
   stands. (`verify/repair2-crash.md` N2, decision 3; `repair5-crash.md` F2.) See D19, D29.

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
   **verify-round:** specifying it (a `leaseCompat` protocol on `/leases/internal`) would also make
   lease-auth's `leasePeerURL` premise derivable (C24). (`repair-lease-auth.md`.)
   **re-review:** a second reason to specify it: `examples/etcd/leaseexpiry`'s `TimeToLive` check needs
   a starter serving `s.LeaseHandler()` on the peer address (`etcdstart` serves only the raft
   handler), with a `LeaseHandler` spec making `leasePeerURL` derivable (D8). (`verify/repair3-boot.md`
   decision 1, `repair4-lease.md` decision 1.)
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
   **verify-round:** (b): `clusterVerOk ver` is now transparent, `∃ sv, Semver.parse ver = some sv ∧
   Membership.verFits sv`, over 2e's `clusterVerInv` and `RaftCluster.Version`/`SetVersion` specs;
   invariant vs deployment premise for `verFits` is still open. (`repair-apply-txn.md`,
   `repair-server-boot.md`.)
3.6 **Requests in flight at a stop, beyond the gate (A7).** (a) `LeaseServer.LeaseKeepAlive`'s
   context-done path returns while its goroutine may still be in `LeaseRenew` holding a `srvGate`
   share: options, 2c's `LeaseRenew` without the gate (it touches nothing `Cleanup` closes) or a fork
   change; (b) `maintenanceServer.Snapshot` reads the backend without a gate share (the same race as
   `issues/etcd-read-after-backend-close-panic.md`). `integration-X.md` open items 1, 3.
   **verify-round:** unchanged ((a) recorded again by grpc-v3rpc); `LeaseRevoke.spec` no longer takes
   a `srvGate` share. (`repair-grpc-v3rpc.md`, `repair-server-core.md`.)
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
   **verify-round:** the rule needs a second clause (C31): a sector past the durable size written by
   one `pwrite` since the last sync holds zeros or that write's bytes (ext4 `data=ordered`, xfs; not
   `data=writeback`); `boltCrash` is written as under (a), over `crashRestQ` under (b). Still
   undecided. (`repair-bbolt.md` F2, F10.)
4.2 **The commit's prophecy (4c-D2)**: resolved on "the meta page was written" (its mapped txid), not
   `err == nil`, via a prophecy patch in `etc/proph-patches/bbolt/` (`etc/prophcheck` must admit that
   read: not checked). Alt.: a third update. `batch-4c.md`.
4.3 **The durable state in the client's state (4c-D3, D4)**: `BoltSt` carries `dur`, `busy`, `lost`
   (alt.: a bbolt-owned "synced" witness, unsound under `NoSync`; a synced flag, raced by `DB.Sync`);
   files named once per generation, the state living across opens. Confirm. `batch-4c.md`.
   **verify-round:** `BoltSt` also gains `named` (C2); `fileHolds_new` now needs `named` and
   `m.hi = 0`. (`repair-bbolt.md` F1, F3.)
4.4 **The txid bound across crash generations.** Receipts are counted per generation (`Open`'s
   `2^62`), and the crash law hands `fileHolds` on, so no fixed bound survives unboundedly many
   crashes. Options: txid `< 2^63` plus a premise on the number of generations, or a bound carried in
   `BoltSt`. `integration-I7.md` open item 1.
4.5 **Durability through the batch lock's resource**: the client chooses at `New` the lock's
   resource `Pk` and its commit step `commitOk`, which every commit (including the run loop's) runs
   (alt.: a persistent atomic update handed to `New`, the same thing spelled differently). Accept?
   4a Q2, `batch-4a.md`.
   **verify-round:** the commit's two updates are now one nested `commitAU` (C28), which the batch
   lock's whole `boltState` builds (`boltState_commit_au`). (`repair-bbolt.md` F5,
   `repair-backend-schema.md`.)
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
   **verify-round:** also waiting on it: `histPropose`'s step budget (A7-provability F8).
   (`repair-server-core.md`.)
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
   **verify-round:** some now specified: zap's `Float64`, `Time`, `Binary`, `Logger.{Named,With,Sync}`,
   otelgrpc's handlers (`statsOk`), `fmt.Sprintf("%+v", md)` (assumed); not zap's `Logger.Core`,
   `WithOptions`, `Sugar` (gaps). (`repair-client-core.md`.)
5.9 **Configuration scope premises at `NewServer`/the client** (each filed): `--max-txn-ops ≤ 4999`,
   `--max-request-bytes` below the keys-only amplification bound, `Compact` at a revision other than
   `0` (W0 Q1: alt., model a first `Compact(0)` as a no-op and accept a false spec in that corner),
   `watchIntervalCfgOk` (your 2026-10 "skip"), rafthttp's `ConnReadTimeout`/`ConnWriteTimeout ≥ 5s`,
   no distributed tracing (`traceutil.Init` never called: 4b Q3). `top.md` K8, `batch-W0.md`,
   `batch-2c.md` D6, `batch-2f.md` round 1, `batch-4b.md`.
   **verify-round:** rafthttp's `vars_init` docstring now says embed binds the timeouts to flags and
   etcdmain clamps them to `5s`; taking their points-to as a `Transport.Start` premise was declined
   (gaps). (`repair-rafthttp.md`.)

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
   the environment premise `Wal.crashInScope` over `Wal.Recs.crashScopeOk` (2.8; was `crashScope`).
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
   **verify-round:** the missing stubs and handlers now have WP-form specs
   (`etcdserverpb/StreamShapes.lean`; `authClient.*`, `clusterClient.*`, `maintenanceClient.*`,
   `RangeStream`); their proofs still need the bodies, so the question stands (gaps).
   (`repair-grpc-v3rpc.md`.)
7.5 **OsFs's crash relation** (this repository's `GooseLang/Ext/OsFs/`, trust base): 4.1's option (a).
7.6 **A bbolt prophecy patch** (`etc/proph-patches/bbolt/`) reading the mapped meta page's txid: 4.2;
   `etc/prophcheck` must admit the read.
7.7 **Opaque predicates without their heap binder** (branch-wide): an `opaque p : IProp GF :=
   iprop(True)` under section variables does not take `hG`, so it cannot be realized over the heap
   (`Backend.beFile`, `Mvcc.kbData`, ...). Fix: put the binders in each opaque's own signature (also
   settles 4a's `[HasExt osFsExt]` gap). The README convention causes it. `integration-I6.md` "Two
   findings left open" 2.
   **verify-round:** settled: the binders landed branch-wide (`1aa6fc1337`); `beCrash` now concludes
   at the crashed heap. (`repair-backend-schema.md` B2.)

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
- verify-round: `issues/etcd-client-resolver-build-race.md`: `SetEndpoints` (a caller's or auto-sync's) races grpc's `Build` of the resolver when the channel leaves idle (no; excluded by C1).

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
- re-review: `etcd-backend-name-lost-restart-panic` (a crash after a first boot's first local snapshot can lose `member/snap/db`'s name, and the restart panics in `recoverSnapshot`; yes, pending D7). Updated: `bbolt-create-dir-not-synced` ("etcd recovers from its WAL" only before the first local snapshot), `etcd-admin-check-authenable-race` (the denial's principal, D9).
- verify-round: `bbolt-create-dir-not-synced` (a database file bbolt creates can vanish at a crash; C2), `etcd-auth-read-denied-across-views` (a read denied though permitted at every auth state it spans), `etcd-backend-defrag-rollback-nil-tx` (a deferred `Rollback` on a `nil` transaction), `etcd-client-withrange-empty-end` (C3), `etcd-member-id-raft-reserved` (a member id raft reserves, about 2^-63) (all no).

## C. Decisions from the verification round (2026-11-09)

Every decision the repair groups flagged for the user after the verification round (their "New
decisions"/"Decisions for the user" sections, and the findings "fixed differently" in a way that
changes an API shape), plus the coordinator's two. A report `repair-<group>` is
`notes/specs-only/verify/repair-<group>.md`; spec paths are under `Spec/go_etcd_io/etcd/` unless they
start otherwise. The specs are written to each choice; say if you disagree.

### Coordinator's decisions

C1. **The resolver race is excluded by option (b).** `issues/etcd-client-resolver-build-race.md`:
   grpc's `Build` of the client's resolver (when the channel leaves idle) races `SetEndpoints`. Now
   auto-sync and `Sync` are out of the top-level workloads and `SetEndpoints` runs only before the
   first RPC: a new exclusive `resolverIdle c` (`client/v3/ApiClient.lean`: no RPC can wake the
   connection) is a premise, given back, of `Client.SetEndpoints.spec`/`Client.Sync.spec`; `newClient`
   holds it for its own `SetEndpoints` and gives it to no caller; `cfgOk` requires `AutoSyncInterval =
   0` (the `verifyOff` alternative dropped), so `New`, `newClient`, `kubernetes.New` give the endpoints
   token unconditionally and `autoSync.spec` covers only interval `0`; snippet `ReqSync` removed. Alt.:
   (a) a token every RPC on the connection takes a fraction of (keeps a running client's endpoint
   changes, more bookkeeping), or the resolver's fields stated as racy, outside the model.
   (`repair-client-core` A2 S4; `repair-client-watch` S4.)
C2. **bbolt F1: a database file bbolt creates may vanish at a crash.** bbolt opens with `O_CREATE` and
   never syncs the directory, so under POSIX/OsFs the new file's name is not durable. Chosen: (ii) the
   bbolt-local flag `BoltSt.named` (`false` for a generation started from no file; `recovers` then
   admits the empty database) and the new law `boltFresh_alloc` (start a generation from no file, or an
   empty file whose name may not be durable); `fileHolds_new` takes only an empty file with a durable
   name and `m.hi = 0`; `boltCrash` may conclude "no file" when `named = false`; the backend's `beCrash`
   and `beFile_none` follow. Alt.: (i) OsFs says a file's sync makes its name durable (true of
   ext4/xfs, false of POSIX; changes the shared model), (iii) forbid starting from no file (etcd's
   first boot unprovable). Files: `Spec/go_etcd_io/bbolt/{Model,Api}.lean`,
   `server/v3/storage/backend/Durable.lean`; `nonissues/bbolt-create-dir-not-synced.md`.
   (`repair-bbolt` F1, "New decisions"; `repair-backend-schema` second pass.)

### Client

C3. **Non-`nil` empty range ends are out of scope on the client.** `OpM.emptyEnd = false` (new, with
   `anyEmptyEnd`) in `KV.{Get,Delete,Do,GetStream}Triple` and `Txn.{Then,Else}Triple`;
   `Cmp.WithRange.spec` takes `e ≠ []`; leasing's `LKV.*`/`LTxn.*` triples take the same premise. No
   caller in scope passes such an end. Alt.: a transport mode in the client's request model (a dialed
   member reads the end as one key, an in-process one as every key from it), which needs a second
   message model beside `Wire.endOf`. Files: `client/v3/Api.lean`, `client/v3/leasing/`;
   `nonissues/etcd-client-withrange-empty-end.md`. (`repair-client-core` A1-P F5, "New decisions";
   `repair-client-users` second pass.) See A14.
C4. **Readiness recorded per handle through a ghost client.** `NewLeaseFromLeaseClient.spec` takes
   `cr = c ∨ cr = null` and returns `lessorHandle l cr`; `NewWatchFromWatchClient.spec` takes the stub
   as `□ (clientReady rc -∗ remoteWatchAt …)` and returns `watcherHandle w rc …`; `NewLease`/`NewWatcher`
   pass the client, the in-process client passes `null` (`clientReady_null`). The `New*Client` stubs
   now take the client (`clientConnOk`, `c.conn ↦□ conn`) and give `□ (clientReady c -∗ remote*At …)`.
   Alt.: record the Go client argument, circular for the in-process client (`clientBare_assemble`
   mints `clientReady c` only after the fields are set). Files: `client/v3/{ApiLease,ApiWatch,
   NewWatchFromWatchClient,NewWatcher}.lean`, `api/v3/etcdserverpb/New*Client.lean`.
   (`repair-client-core` L1, "New decisions"; `repair-client-watch` W3, "New decisions";
   `repair-grpc-v3rpc` routed requests.)
C5. **A per-member lease view threaded through the wire contract (`via`).** `AttemptTriple`/`uiOk_call`
   take `via` (pre `viaPre γ (grpcConnVia cc) via`, post `viaFact`), `CallTriple` an optional extra post,
   `RemoteCallTriple` an optional member condition `V` (default `False`); `LeaseRead.Triple`'s post is
   `viaFact` (removing an overpromise: `leaseAnsAt` of a refusal). The report names no alternative; it
   changes the shape of every attempt triple. Files: `client/v3/{ApiClient,ApiLease}.lean`, grpc-v3rpc's
   `Realize.lean` (`grpcConnVia_unfold`). (`repair-client-core` A2-P L2.)
C6. **`GetStream` takes no thread token** (fixed differently from "give it back"): Perennial's
   `wp_fork` forks without tokens, so the premise is dropped from `KV.GetStreamTriple`'s pre and post;
   the margin is the leaked goroutine (`nonissues/etcd-client-getstream-abandoned-leak.md`). Files:
   `client/v3/{Api,kv__GetStream,Client__GetStream}.lean`, leasing's `GetStream`. (`repair-client-core`
   A1-C F1; `repair-client-users` second pass.)
C7. **`ctx.Value` through a new persistent predicate `Context.ctxValueIs ctx key v`** (from
   `WithValue.spec`'s post; `Value.spec`, `ctxValueIs_child`/`_other`/`_wp`), rather than a value
   argument on `ctxValueAt`, which six other groups' files use; auth's `ctxValIs` is now its
   abbreviation. Files: `Spec/context/Api.lean`, `server/v3/auth/Api.lean`. (`repair-client-core` A1-C F5;
   `repair-lease-auth` second pass.)
C8. **`ctxStreamKey_prin` is a law about W0's `ctxPrin`, stated in 1b's `ApiWatch.lean`**: two contexts
   with the same stream key have the same principal. It constrains every future `ctxPrin` introduction
   (outgoing metadata must print injectively), and an introduction at an arbitrary principal (1.5's
   unissued token) would contradict it. No functionality law for `ctxStreamKey` (grpc's
   `FromOutgoingContext` does not say whether an empty map was attached). Files: `client/v3/{ApiWatch,
   streamKeyFromCtx,Api}.lean`, `Spec/fmt/{Api,Sprintf_md}.lean`. (`repair-client-watch` W2, "New
   decisions"; `repair-client-core` second pass.)
C9. **Compaction affects only exactness, stated in `watchStep` and mvcc's `wStep`**: outside the
   `exactFrom` gate, every delivered event is a history event of its revision that the watch keeps (key
   in range, not filtered; a put's key-value the record its revision wrote). Alt.: every event fact
   gated (A17's previous form). Files: `client/v3/ApiWatch.lean`, `server/v3/storage/mvcc/ApiWatch.lean`.
   (`repair-client-watch` S2, "New decisions"; `repair-mvcc` second pass.) See A17.
C10. **A mutex and an election write only their session's key.** New `sessKey pfx lease := pfx ++
   hexadecimal lease`; `mutexEff`/`campaignEff` allow only a put or delete of it, the posts name it, and
   `Mutex.Lock`/`lockerMutex.Lock` give the create-revision order. This narrows the permission callers
   give and makes 1.13 true under `leaseExpiry = false`. Callers use the real prefix `name ++ "/"`
   (v3lock and v3election done by server-boot). Alt.: the old effects over any key, under which
   no-two-holders was unprovable. Files: `client/v3/concurrency/`, `server/v3/etcdserver/api/
   {v3lock,v3election}/`; snippet `ReqMutexNoTwoHolders`. (`repair-client-users` C-F2, "New decisions";
   `repair-server-boot` A3 F1.)
C11. **Recipes' `Dequeue`: only the front stays gated on `exactFrom`.** First the cheap fix (snippets
   assume `exactFrom`), then, with C9, the claimed key, its record and the value are unconditional;
   the front (`frontByRev`/`frontByKey`) stays gated because a caller cannot tell the read path from the
   watch path. Alt.: a post telling the caller which path ran. Files: `client/v3/experimental/recipes/`.
   (`repair-client-users` P-F3, "New decisions", second pass.)
C12. **Sentinel errors are read from their globals; their values are existential** (cross-cutting,
   the brief's item 3). A post returning a sentinel says `globalAddr ErrX ↦□ err`; one excluding them
   uses `notConcErr`/`notRecipeErr` or the owner's `errIs`; each `init.spec` gives the values non-`nil`,
   pairwise distinct and (client users) distinct from `context.Canceled`'s and `io.EOF`'s. The server's
   pure `srvErrOf`/`srvErrVal` are deleted for a persistent `srvErr err e` with `sentinelAt`; the tie of
   a lower package's sentinels to the server's mapping lives with the owner of the mapping
   (`etcdserver/errors/Api.lean`: `authErr_srv`, `leaseErr_srv`, `mvccErr_srv`, `bcryptErr_shape`;
   `membership/Errors.lean`: `errs_srv`), not in the lower package (mvcc: layering). rpctypes' `errVal`
   stays a constant (`EtcdError` is a struct value). Alt.: Lean constants per error (unrealizable: fresh
   `errors.New` pointers). Files: `client/v3/{Api,concurrency/Api,experimental/recipes/Api}.lean`,
   `server/v3/{auth,lease,etcdserver/errors,etcdserver/api/membership,etcdserver/api/rafthttp,
   storage/mvcc}/`, `Spec/golang_org/x/crypto/bcrypt/`, raft's `raft_init` (`errBreak`).
   (`repair-client-users` P-F4, "New decisions"; `repair-lease-auth` "New decisions"; `repair-server-core`;
   `repair-mvcc`; `repair-server-boot`; `repair-rafthttp`; `repair-client-core`; `repair-raft-core`.)

### gRPC and protobuf

C13. **`Proto.Content` holds Go values; the wire carries `norm c`.** Quotienting contents by
   `proto.Equal` was inconsistent (a `nil` and a non-`nil` empty range end are `Equal`, but W0's `endOf`
   tells them apart: `False` from a terminating program). Now `norm` is the wire view (implicit-presence
   zero fields unset, empty repeated fields `nil`, explicit-presence fields kept), decoded contents are
   canonical (`decodedAt` removed), `Equal` compares `norm`s, `Clone` gives `mergeDst … (norm c)`, and
   `endsDecoded t p` is redefined as a share of the message with the pure `endsOk`. Every owner of a
   message relation states a `*_norm` law (`raftpb_norm`, `schema_norm`, `ltlReply_norm`, 3h's
   `holds_norm` under `endsOk`). Files: `Spec/google_golang_org/protobuf/proto/`,
   `Spec/google_golang_org/grpc/Api.lean`, `api/v3/etcdserverpb/Api.lean`,
   `server/v3/etcdserver/api/v3rpc/`. (`repair-grpc-v3rpc` P-F2, "New decisions", follow-up;
   `repair-raft-conf-pb` second pass.)
C14. **`Proto.depthMax = 10001`**: protobuf-go decodes 10000 levels; the old bound made the transaction
   reply at `--max-txn-ops = 4999` unsendable. Alt.: a stricter `maxTxnOps` premise. Files:
   `Spec/google_golang_org/protobuf/proto/`, `api/v3/etcdserverpb/Api.lean` (`holds_depth_resp`).
   (`repair-grpc-v3rpc` P-F6, "New decisions".)
C15. **The election and lock services sit under `etcdContract` with trivial contracts** (a member
   promises only that a run returns; their handlers run over the in-process `v3client`, 1.5). Alt.: a
   contract sum `etcdContract ⊕ X`. Files: `server/v3/etcdserver/api/v3rpc/`
   (`RegisterElectionServer.spec`, `RegisterLockServer.spec`). (`repair-grpc-v3rpc` C-F4, "New
   decisions".)
C16. **Dial options are pass-through, with no chain model in `DialCfg`** (fixed differently):
   `WithChainUnaryInterceptor`, `WithChainStreamInterceptor`, `WithStatsHandler`, `WithContextDialer`
   are `dialOptAt v (fun cfg => cfg)` under premises on their argument (`cliIcPass`, `cliSicPass`,
   `statsOk`, `ctxDialerOk`), feeding `dialOptsOk_neutral`; otelgrpc's handlers give `statsOk`; the
   server's `StatsHandler.spec` takes `statsOk`. Alt.: the reviewer's `uis : List val` in `DialCfg`
   (changes `connAt`'s arity in other groups' files for no extra guarantee). Files:
   `Spec/google_golang_org/grpc/`, `client/v3/Api.lean`, `Spec/go_opentelemetry_io/…/otelgrpc/`.
   (`repair-grpc-v3rpc` C-F2; `repair-client-core` second pass 4.)

### Apply and txn

C17. **`ownStep`: a backend operation is pinned to its request's own step, no refusal**
   (`opStep_step` concludes `kvStep ∨ leaseStep ∨ authStep ∨ clusterStep`), so a client learns that a
   valid write was not refused. A law the apply proof proves; nothing added to the trust base. Alt.: W0's
   whole `Step` (refusal disjunct included). Files: `server/v3/etcdserver/apply/Api.lean`.
   (`repair-apply-txn` F4, "New decisions".)
C18. **The lease deleter's contract is a slot `kvDelOk` beside `kvOk`/`kvSt`** (fixed differently from
   a `□ ∀ …, rdOk` producer in `optsSt`): `rdOk`'s resources are the store's writer resources, named only
   by `kvSt`/`kvOk`'s realization, so the three are introduced together (2d's `srvStores_kv`); `lessorSt`
   now takes the KV and the backend. Files: `server/v3/etcdserver/{apply/Api,ApiApply}.lean`.
   (`repair-apply-txn` F2, "New decisions".)
C19. **Superseded by D10 (re-review RR3, `verify/repair2-server.md`): the three check specs take
   only the request's own predicate, and 3h's `endsDecoded` family is deleted.** Was:
   **`CheckTxnAuth` and its helpers give `endsDecoded`/`opsDecoded` back** (differently from "the
   persistent closure"): the request path holds the request at a share, so a persistent form cannot be
   produced there; the apply thread uses the `□` form (`endsDecoded_ro`). Files:
   `server/v3/etcdserver/apply/` (`CheckTxnAuth`, `checkTxnPermission`, `checkTxnReqsPermission`).
   (`repair-apply-txn` second pass.)

### Lease and auth

C20. **Partly superseded by D13 (`verify/repair2-server-core.md`): `NewLessor` returns the caller's
   token and the loop runs on its fork's own; `Stop` returns none.** Was: **The lessor's run loop takes a thread token**: `NewLessor` takes a `threadTok` and `Stop` gives
   it back; `ckptOk` is at `context.Background()` with a token, and `lessor.Renew` takes the caller's.
   The untranslated loop is a goroutine of the program and calls the checkpointer, whose server closure
   needs a token. Alt.: none (the trusted `NewLessor` would otherwise hand a counted resource to a
   thread that took none). Files: `server/v3/lease/` (`Api`, `NewLessor`, `lessor.{Renew,Stop}`).
   (`repair-lease-auth` F2, "New decisions".)
C21. **The token provider's waiter is gated on a persistent `R`** (`waiterOk iw R`; `tokenProviderAt …
   R …`; new `authGate γa R` from `NewAuthStore`; the server uses `R := srvStarted`). Alt.: a gate token
   as `SetCheckpointer` has, but the provider never learns the server started (no Go call to hang it
   on). Files: `server/v3/auth/{Api,Internal}.lean`. (`repair-lease-auth` F7, "New decisions".)
C22. **The auth store's backend is exclusive writer state, `authBeCur γa be`**, so the hook contract is
   stated over the backend value (`authHook_intro` from `authBeHook`) while the admin specs keep
   `authHook γa`; `Recover` moves it and returns `authBackendAt be0 _`. Alt.: fold the backend into
   `authCur` (changes its arity and every apply statement). Files: `server/v3/auth/Api.lean`,
   `server/v3/storage/backend/AuthBackend.lean`, `server/v3/etcdserver/apply/Api.lean` (`authSt`,
   `hooksOk`). (`repair-lease-auth` F4, "New decisions"; `repair-backend-schema` second pass;
   `repair-apply-txn` F3.)
C23. **`Lease.clusterOk` is transparent** (fixed differently from an introduction law): the `Version()`
   triple through the `cluster` interface; each client proves it for its type (`noCluster` from its
   body, `*RaftCluster` from 2e's new `RaftCluster.Version.spec` with `clusterVerInv`). A law in
   membership naming `clusterOk` would make membership import lease. Files: `server/v3/lease/Api.lean`,
   `server/v3/etcdserver/api/membership/`. (`repair-lease-auth` F3; `repair-server-boot` A8-C F3.)
C24. **`leasePeerURL` is a deployment premise** of the new trusted `leasehttp.TimeToLiveHTTP.spec` and
   of 2c's `leaseTimeToLive` ("the leader's peer URLs are etcd members' lease endpoints"); without it a
   malformed `200` reply panics (`issues/etcd-leasehttp-timetolive-nil-{response,header}-panic.md`). It
   cannot be derived: rafthttp's `raftCompat` allows, but does not forbid, a `200` on `/leases/internal`.
   Alt.: server-boot strengthens the peer port's protocol (`leaseCompat`, see 3.2), then a law in
   `leasehttp/Api.lean` replaces the premise. Files: `server/v3/lease/leasehttp/TimeToLiveHTTP.lean`,
   `server/v3/etcdserver/ApiReq.lean` (`ltlReply_replyHdr`). (`repair-lease-auth` second pass;
   `repair-server-core` second pass.)
   **re-review:** the premise now also enters through a gate: `leaseURLOf_intro` (2e) gives
   `Leasehttp.leaseURLOf γ ep (u ++ "/leases/internal")` from `srvEp` and `leasePeerURL`, and
   `leaseURLOf_peerURL` gives `leasePeerURL` back to `TimeToLiveHTTP`'s callers; the lessor view
   `ltlView` is gated on `leaseURLOf` (D15). `leasePeerURL` is false of `etcdstart`'s peer URLs, so the
   `TimeToLive` row's gate `peerLeaseServed` cannot be met there (D8). Still no law derives
   `leasePeerURL`; specifying `LeaseHandler` (3.2) would. (`verify/repair3-boot.md` item 3, decision 1;
   `repair2-relay.md`; `repair4-lease.md`.)

### Storage and bbolt

C25. **The batch lock's turn, `beTurn γ`**: every `Lock*` returns an exclusive token that `Unlock`'s
   second visible-image update takes back atomically: "no session begins before the previous one's
   second update fired", which mvcc's bridge (state parked between sessions) needs. Changes the shape of
   `Unlock`'s second update for every client. Alt.: (a) the backend parks client-chosen state per
   footprint, (b) generations with a persistent `beEnded` (cannot be tied to the bridge). Files:
   `server/v3/storage/backend/{Api,MvccStorage,SchemaTx}.lean`. (`repair-backend-schema` B1, "New
   decisions".)
C26. **`backend.Snapshot` is bounded below by a history prefix and carries only its size.** It takes
   `beHistLb γ L0` and returns an image that is the last of an extension of `L0`; `beSnapN γ s I n`
   replaces `beSnap` (fixed bytes; deleted), and `WriteTo` writes some `bs` with `imgBytes I bs`. Alt.:
   "the last commit" (false: the history's commit step fires before bbolt's meta write) or "some
   committed image" (too weak for the merged snapshot). Files: `server/v3/storage/backend/{Api,Durable}.lean`,
   `server/v3/etcdserver/ApiApply.lean`. (`repair-backend-schema` F1, F5, "New decisions".)
C27. **mvcc over a backend without `meta`**: `keyBackend_intro` takes `m : Bool` (`m = false` puts
   `meta`'s existence cell in mvcc's footprint, for `examples/mvccrand`); the server's case `m = true` is
   unchanged, differing from mvcc's request only in keeping the frozen case's `metaMade := true`. Files:
   `server/v3/storage/backend/MvccStorage.lean`. (`repair-backend-schema` A10-C F2; `repair-mvcc`.)
C28. **A bbolt commit's two updates are nested** (fixed differently from one law realized with an
   invariant): `Tx.Commit`/`DB.Update` take one `commitAU … S` whose commit yields the settling update,
   with one client predicate `S ok synced failed brk`; a holder of the whole state builds both
   (`boltState_commit_au`). Every client changes shape. Files: `Spec/go_etcd_io/bbolt/{Api,Tx__Commit,
   DB__Update}.lean`, the backend's commit citations. (`repair-bbolt` F5, "New decisions";
   `repair-backend-schema` second pass.)
C29. **`DeleteBucket` resets the generations strictly below the deleted bucket** (`TxView.dropBkt`):
   its exact post was unreachable through its own recursion. Clients see no difference (those handles
   were already stale). Files: `Spec/go_etcd_io/bbolt/{Model,Internal}.lean`. (`repair-bbolt` F9, "New
   decisions".)
C30. **No keyed `bolt.Options` literal spec**: no translated code builds one; etcd's one keyed literal,
   `boltOpenOptions`, is an untranslated initializer whose value is the backend's assumed `PkgInit` fact
   (`boltOpenOptions_init.spec`, `MmapFlags = MAP_POPULATE`). Files: `Spec/go_etcd_io/bbolt/Options.lean`,
   `server/v3/storage/backend/Durable.lean`. (`repair-bbolt` F7, "New decisions"; `repair-backend-schema`
   second pass.)
C31. **The sector rule of 4.1 needs a second clause**: a sector past the file's durable size written by
   one `pwrite` since the last sync holds zeros or that write's bytes (ext4 `data=ordered`, xfs; not
   `data=writeback`), or `init`'s crash safety fails. Under (a) `boltCrash` is as written, under (b) over
   `crashRestQ`. 4.1 itself is still yours. Files: `Spec/go_etcd_io/bbolt/Api.lean` (header).
   (`repair-bbolt` F2, F10, "New decisions".)

### Raft and raft messages

C32. **An idle token for the raft struct, `coreIdle r`**: `node.Advance` returns before the run
   goroutine steps the acknowledgements, so R3 publishes a floor ahead of `applied` in that window, where
   a `MsgHup` would panic in Go (`hasUnappliedConfChanges`); `node.run`'s sequencing is stated as the
   token (every step from outside, `hup` and the ticks take it), and `RawNode.Advance.spec` now covers
   only the steps (a direct caller applies `rawNodeAt_advance` first). Alt.: a "pending Advance" node
   state (needs the same R3 change and still has the window). Files:
   `Spec/go_etcd_io/raft/v3/{ApiCore,ApiLog}.lean`. (`repair-raft-core` P3, "New decisions".)
C33. **`storedLb` as a second, weaker storage bound**: snapshotting a delivered entry before `Advance`
   (kvdurable, kvreconf) needs only `storedLb` (given by `readyStor_append`'s COMM); compaction still
   needs `appliedLb`. Alt.: `appliedLb` only (those programs unprovable). Files:
   `Spec/go_etcd_io/raft/v3/{Api,ApiLog}.lean`. (`repair-raft-core` F1, "New decisions".)
C34. **`loggerOk` gives the logger no ownership of the arguments** (a transparent bundle: the methods
   raft calls return), as the old `isLogger` did; a formatting logger (zap's adapter) rests on its own
   trust-boundary specs. Files: `Spec/go_etcd_io/raft/v3/Api.lean`. (`repair-raft-core` F3, "New
   decisions".)
C35. **`fmt.Errorf` with non-`ArgsWf` arguments is a raftpb-local assumed spec**,
   `RaftPb.fmtErrorf.spec` (raftpb enums under any verb, held `*ConfState`s read only), for
   `Changer.apply` and `ConfState.Equivalent`. Alt.: restore the old general `Spec/fmt/Errorf.lean`
   (client-core's directory), or the Perennial change (gaps, below). Files:
   `Spec/go_etcd_io/raft/v3/raftpb/FmtErrorf.lean`. (`repair-raft-conf-pb` F2, F3, "New decisions".)
C36. **`msgRecv` is introduced from protobuf's `mergeDst`** (`RaftPb.msgRecv_intro`; `Clone` and
   `Unmarshal` now give `mergeDst`), not from a new "fresh slices" fact; `msgRecv_lend` lends a read
   share, not `own 1` (with `own 1` the wand could swap the `Entries` slice). Files:
   `Spec/go_etcd_io/raft/v3/raftpb/Api.lean`, `Spec/google_golang_org/protobuf/proto/`.
   (`repair-raft-conf-pb` A5-C F4, "New decisions".) See A12.
C37. **Messages with `Responses` get their own predicate, `msgOut`**; `Msg`/`msgWf` stay without
   responses (only local `AsyncStorageWrites` messages carry them, never marshaled), and raft-core states
   `newStorageApplyMsg`/`newStorageAppendMsg` over it. Alt.: leave the two helpers unspecified as a scope
   restriction (`ConfigOk` excludes async writes). Files: `Spec/go_etcd_io/raft/v3/raftpb/Api.lean`,
   raft's `newStorage*Msg`. (`repair-raft-conf-pb` A5-C F5, "New decisions"; `repair-raft-core`.)
C38. **rafthttp's codecs are transparent definitions** (`msgFrame`, `v2Frame`, `v2Chain`, `v2Compat`,
   over raftpb's `msgEncodes`; `pbEncodes` gone), not an opaque frame with a determinism law (smaller,
   but a law about a pure model the README says to spell out, and easy to misstate for link heartbeats).
   Knock-on: `msgAppV2Encoder.encode` takes `dst ≠ 0`. Files:
   `server/v3/etcdserver/api/rafthttp/Api.lean`. (`repair-rafthttp` F8, "New decisions".)
C39. **`raftOk`'s `Process` takes `msgRecv`** (A12 made concrete at the transport): the decoders deliver
   it, and the server proving `raftOk` receives strictly more. Files:
   `server/v3/etcdserver/api/rafthttp/Api.lean`, `EtcdServer.Process`, `raftNode.Step`.
   (`repair-rafthttp` "New decisions"; `repair-server-core`.)

### Server and boot

C40. **WAL and snapshot writes have two linearization points**: `storage.Save`/`SaveSnap` and
   `SaveDBFrom` take two nested updates with an in-flight state between them (`walWriting`,
   `snapSaving`), so a crash knows a write is in flight (crash laws `walRecs_crash`, `walWriting_crash`,
   `snapDbs_crash`, `snapSaving_crash`); the raft loop fires `readyEnter` in the second. Alt.: one update
   at the start, with a crash relation that may lose the write (the model would claim states before they
   are durable). Files: `server/v3/storage/{wal/Api,storage__Save,storage__SaveSnap}.lean`,
   `server/v3/etcdserver/api/snap/`. (`repair-server-boot` F1.2, F9, "New decisions".) See 2.8.
C41. **The snapshot directory's removals are not durable (`snapGone`)**: etcd fsyncs it only in
   `SaveDBFrom`, so removals and the install's rename can come back after a crash; the client keeps the
   removed images and the crash law resurrects only those, so the server's invariant certifies every
   image ever saved at an index. Files: `server/v3/etcdserver/api/snap/Api.lean`. (`repair-server-boot`
   F9, "New decisions".)
C42. **Install-then-crash: the backend reverts an unsynced rename** (`beRevert p o0`/`beNoRevert p`,
   `beRev`; `beCrash` may conclude the reverted file; `dbFile_rename` gives `beRevert`, `SaveDBFrom`'s
   directory fsync gives `beNoRevert`, `OpenSnapshotBackend` threads it). Its realization waits on OsFs
   (gaps). Alt.: a scope premise "no crash between an install and the next snapshot save", or a fork fix
   (fsync the snapshot directory in `OpenSnapshotBackend`, a simpler model). Files:
   `server/v3/storage/backend/{Api,Durable}.lean`, `server/v3/etcdserver/api/snap/`,
   `server/v3/storage/OpenSnapshotBackend.lean`. (`repair-server-boot` "New decisions", last pass;
   `repair-backend-schema` second pass.)
   **re-review:** `beRevert`/`beNoRevert` are replaced by a revert list, `Backend.beRevs p os`
   (`Snap.revertSt` is it); `beOpenUpd` adds `none` to the list for a file bbolt creates (D7);
   `Snap.dbFile_rename`/`OpenSnapshotBackend` take the destination as `beAt p d`, and a renamed-over
   open backend becomes `beDetached` (D3). The crash law is the one `disk_crash` (D21).
   (`verify/repair2-crash.md` N3, `repair5-crash.md` G-a, G-b.)
C43. **`os.Rename` at the snapshotter's files is a trusted triple** (`Snap.dbFile_rename`, with the new
   opaque `dbPathOf`), not a `snapDbs ↔ osMeta` bridge: `snapDbs` is itself a trusted ghost variable, as
   `walRecs` is. Files: `server/v3/etcdserver/api/snap/`. (`repair-server-boot` F5, "New decisions".)
C44. **v3lock/v3election give the lent `P` back on success only**: the server passes 1d's definite
   errors through unclassified, so the caller cannot tell them from indefinite ones. Alt.: posts naming
   the sentinels' globals (then `P` back on 1d's definite errors too, as client-users asked). Files:
   `server/v3/etcdserver/api/{v3lock,v3election}/`. (`repair-server-boot` A3 F7.)
C45. **`GoAttach`'s token shape**: the caller keeps its `threadTok` and the goroutine runs with the
   fork's fresh one, giving it back at its end (attached goroutines need a whole token; callers
   continue). Realizing it needs the wait group's counter bounded while the goroutine holds a whole
   token: either the reader pools these callees borrow from move to level ≥ 1 (`threadTokFrom 1`), or the
   counter is bounded otherwise. A bounds-plan decision. Files:
   `server/v3/etcdserver/{EtcdServer__GoAttach,ApiApply}.lean`. (`repair-server-core` "New decisions".)
C46. **The self-stop and the restore gate are scope restrictions in text**: `run.spec`/`applySnapshot.spec`
   say that no request-path call is in flight when `run` stops on `errorc` (A8-provability F3) and that
   no hash runs during a snapshot install (A10 O1), outside their statements. Alt.: the fork's stop gate
   (§6 F3, A7) and A8's hashing alternative. Files: `server/v3/etcdserver/EtcdServer__{run,applySnapshot}.lean`.
   (`repair-server-core` "New decisions".)
C47. **`reqCtxOk` is kept at the entry methods** (fixed differently): `EnsureTrace` keeps a found trace
   only given `traceEmpty`, so dropping the no-trace part would leave the entry points unprovable; the
   internal requesters (`AuthInfoFromCtx`, `raftRequest`, `processInternalRaftRequestOnce`, `doSerialize`)
   take the new `reqCtxSpan ctx` (otel's span only). Files: `server/v3/etcdserver/ApiReq.lean`.
   (`repair-server-core` A7-P F5, "New decisions".)

C48. **A second spec for one function: `Bucket.ForEachBucket.spec_del`** (bbolt re-review N2): an internal
   spec used only by `DeleteBucket`'s recursion, whose callback may change the transaction's view at and
   below the bucket and which may visit any increasing subsequence of the nested buckets (Go's skip,
   etcd-io/bbolt#1305). It departs from "one spec per function" (PRINCIPLES): the public spec is not an
   instance of it. Alt.: one general spec with the view-changing callback (heavier for every other caller),
   or restate `DeleteBucket` without going through `ForEachBucket`'s spec (the proof unfolds the loop). Files:
   `Spec/go_etcd_io/bbolt/Bucket__ForEachBucket*.lean`, `Bucket__DeleteBucket.lean`; source:
   `verify/repair-bbolt.md` "Re-review", `verify/RR-raftlog-bbolt.md`.

### Gaps left open by the repairs

Items a repair report says it could not fix, with its reason (items a later pass closed are left out).

- **Unissued token** (`ctxPrin` for `tokenUnissued`): open question 1.5; 3d's vocabulary, and an
  introduction at any principal would contradict `ctxStreamKey_prin` (C8). (`repair-client-core` A1-C F4.)
- **zap's `Logger.Core`/`Core.Enabled`, `WithOptions`, `Sugar`**: need a core/sugared-logger predicate;
  callers' sketches assume them. (`repair-client-core` S1.)
- **The gRPC proxy's replacing `With*Interceptor` dial options**: not covered by `dialOptsOk_neutral`;
  `ReqNewTLS` unchanged. (`repair-client-core` A2-C F2, second pass 4.)
- **Promoted `*kubernetes.Client` methods**: no specs. (`repair-client-core` A2-C S3.)
- **The cache's "no progress notification without `WithProgressNotify`"**: `cacheWatchAt` does not
  record the watch's options, so it needs a new index on the predicate and on `Cache.Watch.spec`'s
  post; second tier, a later round. Not expressible at the client level (a member answers any
  `RequestProgress` on a shared stream). (`repair-client-users` C-F5; `repair-client-watch` A3 F5.)
- **`version.LessThan` over any `val`**: `semver.Version` is not translated; the honest fix is naming
  the type in the Goose configuration. (`repair-grpc-v3rpc` C-F8.)
- **`sicEtcdOk`'s meaning**: left opaque; a transparent statement needs grpc laws for a wrapped server
  stream (the halves and `streamOut` transferring between wrapper and stream); `metricsOk_stream`
  (assumed) still produces an undefined predicate. (`repair-grpc-v3rpc` second tier.)
- **`LeaseKeepAlive`'s leaked loop sending after the run**: unchanged (3.6). (`repair-grpc-v3rpc`.)
- **Untranslated handlers' and stubs' proofs** (7.4): their specs are WP-form statements of generated
  code until the bodies are translated. (`repair-grpc-v3rpc` P-F9.)
- **No introduction law for `Grpc.genCliAt`/`genSrvAt`**: the generic struct's field cannot be named in
  today's points-to syntax; the stream specs rely on the intended realization. (`repair-grpc-v3rpc`
  sub-agent.)
- **`writeOk` of a `*bytes.Buffer`**: needs Perennial's `bytes.Buffer` spec checked against `writeOk`.
  (`repair-backend-schema` S5.)
- **`backend.begin`'s write case does not pin `I` to the last commit** in its pre (`beCommitted γ I`;
  the realization's `btHeld` does): observed, internal, second tier. (`repair-backend-schema` A11-C F4.)
- **`schema.ReadStorageVersion`, `UnsafeMigrate`**: no spec (names only, trusted callers);
  `GracefulClose` stays 3.15. (`repair-backend-schema` A10-C S3, O2.)
- **`os.WriteFile`** is assumed in `ReqSnapshotFresh` (no OsFs spec of it). (`repair-backend-schema` F1.)
- **The revert case of `beCrash`** (C42) and **defrag's `os.Rename`**: unrealizable until OsFs has
  `rename` and a crash case bringing back an unsynced rename's old entry (Perennial gap below; neither
  OsFs nor `boltCrash` states it). (`repair-backend-schema` second pass; `repair-bbolt` A11-C F3.)
- **A non-blocking defrag snippet**: not added (optional). (`repair-bbolt` A11-C S2.)
- **`leasePeerURL`**: no law derives it (C24; re-review: now used through `leaseURLOf_intro` and `peerLeaseServed`, D8). (`repair-lease-auth` second pass; `repair-server-core`
  second pass.)
- **`KV.Restore.contract`'s whole gate** (A8, A10 O1) and **`Watch`'s id fixed to `0`** (3.8, A10 O3):
  your decisions. (`repair-mvcc`.)
- **No spec files for the promoted `storeTxnRead.{Rev,FirstRev,Range}`, `storeTxnWrite.FirstRev`**:
  internal, served through the delegates; four restating files not written (say if wanted).
  (`repair-mvcc` A10-C S2.)
- **`rangeKeys`' proof rests on Perennial's `Errorf` model** (an error argument is not `ArgsWf`):
  Perennial gap below. (`repair-mvcc` second pass.)
- **`ReqReadyCycle`'s last-term check is not in `Wf`**: the author is not certain it holds of every
  state the law covers; it stays a snippet assumption. (`repair-raft-core` A5 S2.)
- **`Transport.Start` does not take the timeouts' points-to**: no package exports an owned resource for
  writable package variables after initialization (a cross-package design). (`repair-rafthttp` A8-C S4,
  second pass.)
- **`ServerStorage.beReadable`** still provisional (`beTx` superseded at the last pass).
  (`repair-server-boot` F5.)
- **`RaftCluster.Recover`'s `MustDetectDowngrade`** over the backend's stored version: not restated.
  (`repair-server-boot` A8-C F3.)
- **`NewMember` reading `*now`**: trusted, unchanged. (`repair-server-boot` second tier.)
- **`electionServer.Observe`'s sent values**: no facts stated (`Send` carries only the reply's model).
  (`repair-server-boot` second pass.)
- **The pre-commit hook's three recorded gaps**: (a) `confStateSave_hook` takes `beLive γ (btLoc γ) 1`
  and a session at `Fp.none`, while `hookOk` lends only the session and `UnsafeSave` returns one at
  `ciCells` (either `hookOk` lends liveness or the law takes any footprint); (b) the pending
  configuration's size bound has no source (`SetConfState`'s model is `Raft.ConfState`, not a content:
  needs raft-conf-pb's `encSize` of a configuration); (c) whether `txStoredCI_sess` needs
  `beCur γ ciCells`. (`repair-server-boot` last pass.)
- **4a `backend.Close` for a file created in the same generation** (requested by
  `verify/repair4-raft-crash.md`: no durable name, C2's root). **Resolved** by `repair5-crash.md` G-a
  (`beOpenUpd` records the may-vanish case in `beRevs`, `Bbolt.boltReopen_alloc`), and replaced by the
  first-boot decision D7.
- **The crash cases of `storage.go`/`snap.go`** (`crashedMid`'s second disjunct, `snapCrashed`): not
  runnable as Go tests. (`repair-server-boot`; `repair-server-core`.)
- **`histPropose`'s step budget**: waits on 5.1. (`repair-server-core` A7-P F8.)
- **`CorruptionChecker.InitialCheck`**: untranslated, no caller in the specs (embed only).
  (`repair-server-core` A7-C S3.)
- **`ReqReadAfterWrite`'s `KV().Rev()` step** rests on 3e's `KV.Rev` contract with `srvReadAt_mvcc`, not
  checked. (`repair-server-core` A7-P F4.)
- **Perennial: `fmt.Errorf`'s spec admits no error argument (`%w`) or `Stringer`**
  (`notes/perennial-changes.md`, 2026-11-09): `rangeKeys`, `Changer.apply` and `ConfState.Equivalent`
  fall outside `ArgsWf`; worked around by `RaftPb.fmtErrorf.spec` (C35) and mvcc's `rangeCtxErr` laws;
  proposed: `%w` (a fresh wrapping error whose `Unwrap` is the argument) and `String`/`Error` arguments.
  Recorded only.
- **Perennial: OsFs has no `rename`, and no crash case reverting an unsynced rename**
  (`notes/perennial-changes.md`, 2026-11-09): etcd renames onto live paths (defrag, the snapshot
  install); worked around by the trusted `Snap.dbFile_rename` and `beRevert`/`beNoRevert` (C42), whose
  revert case is unrealized; proposed: POSIX `rename`, its crash case, and a directory fsync. Recorded
  only.

## D. Decisions from the re-review rounds (2026-11-09, second half)

Every decision the repairs after the re-reviews (`RR-*`, `F-*`) flagged ("New decisions", and those
in their final requests), from `notes/specs-only/verify/` `repair2-client`, `repair2-server`,
`repair2-raft` (none), `repair2-server-core`, `repair2-relay`, `repair2-crash`, `repair3-boot`,
`cleanup` (none; one law strengthened: `holds_norm`'s watch clause drops its `endsOk` premise),
`repair4-lease`, `repair4-raft-crash`, `repair5-crash`. Spec paths are under `Spec/go_etcd_io/etcd/`
unless they start otherwise. The specs are written to each choice except D6 (open) and D7 (pending).

### The user's answers (2026-11-10)

- **The end goal:** an adequacy theorem with no axioms for a porcupine linearizability test at the
  client boundary (`examples/etcd/txnlin`), **with crashes**. Intermediate specs (D1-D3, D5, D6,
  the vocabulary of D32, D8's `leaseexpiry`) are the coordinator's to settle with the snippets.
- **D7/D31: accepted** — a created directory entry is durable at its file's first sync (ext4/xfs),
  provided a Go snippet illustrates why the assumption is needed.
- **D32: accepted** if it is what ext4 guarantees: a rename within one directory is atomic across a
  crash.
- **D4: no Iris axioms.** The end state is a closed theorem with minimal assumptions: a library this
  repository does not verify gets a trusted *operational* model (a GooseLang extension's semantics,
  as OsFs), and its specs are proved from it. Assumed Iris specs on a boundary (net/http, grpc,
  proto, zap, ...) are temporary; the protocol-family question becomes a proof-side design over
  that model.
- **2.8: fix, then prove.** A bug with a failing Go test (`issues/raft-commit-lost-with-entries-kept.md`)
  is fixed on the Goose fork and the fixed code proved; the `Wal.crashInScope` conf-change part is
  deleted, not kept as a premise. The same holds for every `issues/` finding a premise sidesteps.
- **Trust boundaries:** every trusted spec on the goal's path is ultimately to be proved or replaced
  by a justifiable trusted model; where no reasonable model exists, or the Go features a library
  uses would be hard to support, escalate with a concrete example.

- **Fix plan answers (2026-11-10):** `etcd-range-keys-only-lease`: turn `FastKeysOnly` off (the
  performance cost accepted). Kubernetes is out of scope: no fourth fork, no k8s proofs; the goal is
  only the etcd client porcupine test without axioms, so fixes off its path are deferred.
  `msgsFit`: explanation requested (given in the session).

- **The end theorem's program (2026-11-10):** multiple members, **individual members crash**; a new
  test case, not yet written (txnlin has one member; `examples/etcd/partition` runs three in one
  process, so a crash kills all). Semantics: Perennial's distributed language (`DistLang`,
  `goose_dist_crash_adequacy`: a node crashes alone and reruns its boot program; the network and
  other nodes are unchanged). This replaces the whole-program crash design of K6 (generations of
  the one process, the `*_gen` laws for cluster resources, net/http protocol families).

- **The new test (2026-11-10):** (1) the network as **trusted operational models at grpc's and
  net/http's APIs** (Perennial extensions over the network between nodes, no TCP model beneath;
  justified by grpc's and net/http's documented behavior), not translations; (2) the **client node
  never crashes**; (3) **random reconfigurations** during the test (members added, removed,
  promoted), so the raft membership fixes and join specs are back in scope.

- **More answers (2026-11-10):** PreVote **on** in the test; Q1 accepted (Perennial: a node can be
  marked non-crashing, for the client node); Q6: snapshots stay reachable (F9 to be tested and fixed
  under the fix rule). Network design: handler panics are program panics (coordinator; the
  pipeline-panic issue is fixed on the fork).

### Needs your approval

New client-visible ghost state, or a change to an API or decision you approved.

D1. **A single-member mode for `TimeToLive`: `soleMember`, `urlsReserve`, `peerLeaseServed` (RR-1,
   A4).** To prove `examples/etcd/leaseexpiry`'s "gone by `TimeToLive`, so not listed" check, the
   per-member `TimeToLive` clause is back as a row gated on `soleMember γ ∗ peerLeaseServed γ` (W0
   `api/v3/State.lean`; in 1c's `viaFact`, 2c's `srvLeaseFact`, 2a's `leaseFact`, the assumed
   `EtcdServer.leaseTimeToLive`). `soleMember γ` (persistent: the cluster never has a member but its
   one initial member) comes from `soleMember_intro` (2e `ApiBoot.lean`), which gives up the whole new
   fractional `urlsReserve γ 1`, the right to reserve peer-URL sets: `cluster_alloc` gives it whole,
   `urls_reserve` spends a share. `peerLeaseServed γ` (persistent, W0: every member serves its own
   lessor's lease handler at `u ++ "/leases/internal"`) comes from `peerLeaseServed_intro` under
   `soleMember` and 4b's `leasePeerURL` of the member's peer URLs; without it (repair4-lease F1) the
   row was false under `etcdstart`. Alternatives: a membership history in W0's model (declined for
   A4/A6), or drop leaseexpiry's check from the Users (unproved). Cost: every program that reserves a
   URL set (to add a member) now holds a share of `urlsReserve`; two new W0 opaques.
   (`repair2-client.md` "New decisions"; `repair3-boot.md` item 1; `repair4-lease.md` F1.)
D2. **One member per client address for the run: `srvEp γ ep id` and `srvAt s γ ep`.** The lease
   rows are per endpoint (W0's persistent `leaseViewLb γ ep`) and the server specs per member, so 2a's
   `Server.spec` and the lease handlers now hold only for the endpoint the server is bound to, under
   the persistent `srvAt s γ ep := ∃ id, srvFields s γ id ∗ srvEp γ ep id` (2e `ApiBoot.lean`).
   `srvEp` (persistent, keyed by member id, `srvEp_gen` across a crash) is introduced by
   `srvEp_reserve` from `Http.addrFree ep`: a removed member's client URL cannot serve a new member,
   as for peer-URL sets. Keyed by id, not by server object, because a stop-and-restart in one
   generation serves the same member again (the old `srvAt_agree : s = s'` was false of it). The view
   does not survive a crash (no `leaseViewLb_gen`). Alternatives: a member-indexed view
   `srvLeaseLb s j` with a 2a conversion law (the same bridge in 2a); a per-generation binding (needs
   a per-generation address token nothing issues); keeping `∀ ep` (unsound for the lease rows). Cost:
   a deployment cannot reuse a client address for another member. (`repair2-server-core.md`,
   `repair2-relay.md` decision 3, `repair3-boot.md` item 2 and decision 2; `srvEp_agree` narrowed in D5.)
D3. **`beDetached`: a backend file renamed over while open (4a, G-b).** `applySnapshot` renames the
   received database over `member/snap/db` while the old backend is still open (`server.go:1068`,
   closed at `:1144`). New in 4a `storage/backend/Api.lean`: `FileSt` (`closed o` | `opened γ L`),
   `beAt p d` (the destination's crash state), `beRenamedOver p os d`, an exclusive `beDetached γ p`
   (`beDetached_excl`) for an open destination, a detached form of `beCloseUpd` (its final image
   joins the revert list); in `Durable.lean`, `beDetached_crash` (the detached history folds into the
   revert list as some `I ∈ L`). `Snap.dbFile_rename` and `OpenSnapshotBackend` take `beAt p d`
   (`applySnapshot` the open form, `bootstrap`'s recovery the closed one) and now give the renamed
   `beFile` at the commit, fixing a window where a crash found it nowhere. Alternative: leave
   `applySnapshot` outside 4a's crash laws (repair3-boot's recorded gap). Cost: new client vocabulary
   in 4a's file API; its realization waits on OsFs's `rename` (Perennial gap, as every revert entry).
   (`repair5-crash.md` G-b, decision 4; `repair3-boot.md` decision 3.)
D4. **net/http's protocols are per generation (revises the 2026-10-22 HTTP boundary decision 1, "an
   address string's protocol is fixed once").** What is fixed once is now a family, `Http.protoFam a F`
   (`F : GooseLocalGS GF → Proto GF`, persistent, `protoFam_gen`); `reserve` reserves a family, and
   `protoAt a P` is the current generation's member (`protoFam_at`). True of Go: a crash kills every
   connection, so a request a generation-`L` handler reads was sent in `L`. Needed because the client
   contract names per-generation lease views, which a crash loses: with one protocol for the run, a
   member restarted after a crash could neither serve the old contract nor reserve its own. It
   withdraws repair3-boot's `Http.protoAt_gen` and 2f's `raftProto_gen` (new `Rafthttp.raftFam ν`;
   `peerAddr` over `protoFam`), makes grpc's `addrAt` per generation, and changes the posts of
   `cluster_alloc`, `urls_reserve`, `srvEp_reserve` (whose family serves each generation its own
   `etcdContract`). Alternative: index W0's lease views by an incarnation (changes the client API).
   Cost: a trusted-boundary change. (`repair5-crash.md` F3, decision 1.)
D5. **A new trusted net/http law, `Http.addrFree_protoAt_excl : addrFree a ∗ protoAt a P ⊢ False`,
   and `srvEp_agree` within one cluster.** The law is true of the set-once address map (its
   realization is the fragments' validity). With it, `srvEp_reserve` becomes a fancy update at the new
   namespace `srvEpN`, taking `srvNet γ ν`, that opens the cluster's client-address map (allocated by
   `cluster_alloc`) and refutes an existing entry; `srvEp_agree` gives `id = id'` for one `γ` only
   (cross-cluster `γ = γ'` is not realizable from net/http's API; no user needs it). Alternative:
   `srvEp_agree` without a source (F-server-boot F5). Cost: one more trusted law in the trust base.
   (`repair5-crash.md` F5, decision 2.)
D6. **Open (soundness): raft's `readyBatch` for `raftState_crash` (repair4-raft-crash N1).**
   `raftState_crash.spec` takes `readyEnter n γ id st b dl` as evidence of a batch, but that wand's
   premise includes `nodeRunning n q`, which a stopped node refutes (`nodeStopped`, `exclusive`), so a
   client can forge it for any batch and get `raftState` at a state raft never made (a second vote in
   a term), turning into a safety violation in the next generation; pre-existing since round 3.
   Proposed, not done: an opaque persistent `readyBatch n γ st b` (raft's record of the batch handed
   out at `st`), given by `readyGot`, taken by `raftState_crash` instead of `readyEnter`; 2e's disk
   realization deposits it beside the `readyEnter` it fires. Alternative: none found (raft's proof
   cannot inspect a wand without firing it, and firing mints `msgSent`). Cost: a new client-visible
   opaque in raft's approved node API. The law's docstring says "Open (soundness, escalated)".
   (`repair4-raft-crash.md` N1, decision 2.)
D7. **Pending: a first boot's backend file may vanish at a crash, and the restart then panics
   (G-a).** `bolt.Open` creates `member/snap/db` and nothing syncs `member/snap` unless a snapshot
   is received; on a file system that drops unsynced names (POSIX, OsFs's model), a crash after the
   member's first local snapshot loses the backend while the WAL keeps a snapshot record `k > 0`, and
   `recoverSnapshot` panics (`bootstrap.go:482`): `nonissues/etcd-backend-name-lost-restart-panic.md`
   (blocks-proof: yes). The specs now say the file may vanish (`beOpenUpd` adds `none` to `beRevs`;
   `Bbolt.boltReopen_alloc` for a same-generation reopen; `ReqReopen`'s durable-name Assumes dropped),
   so `disk_crash` is not realizable for such a disk until you choose: **(a)** an environment premise
   "a created file's name is durable at its first sync" (ext4 `data=ordered`/xfs; an OsFs crash-rule
   variant in Perennial, and `BoltSt.named` true at `Open`'s first sync, revisiting C2); **(b)** a
   scope restriction "no crash before `member/snap` is synced" (excludes almost every crash of a member
   that never received a snapshot); **(c)** a fork fix, `fileutil.Fsync(cfg.SnapDir())` after
   `OpenBackend` creates the file (smallest; what the WAL does). The repair recommends (c), with (a)
   as what etcd relies on in practice. (`repair5-crash.md` G-a, decision 3.)

   **Wider than the backend file** (`verify/F2-crash.md` N3, `repair6-crash.md`): etcd never fsyncs
   the data directory after creating `member/` (`fileutil.TouchDirAll` is `MkdirAll` plus a written
   and removed `.touch` file, no fsync; the only fsync above the WAL is `wal.Create`'s of `member/`
   itself), so under the same POSIX model a crash may lose all of `member/`: the WAL, the backend
   and the snapshots (`nonissues/etcd-member-dir-not-synced.md`, blocks-proof: yes pending this
   decision), and the WAL's trusted crash laws already assume it does not. So **option (c) alone is
   insufficient**: it would also need fsyncs of the data directory after `member/` (and of the data
   directory's parent), and of the WAL directory after `wal.Create`'s rename (its first segment's
   entry). **Option (a), stated for directory entries generally** ("a directory entry on the path of
   a file is durable once that file is fsynced", true of ext4 `data=ordered` and xfs), settles both:
   the backend file's name at bbolt's first sync and `member/` at the WAL's first fsync.
D8. **leaseexpiry needs a starter serving `s.LeaseHandler()` on the peer address.**
   `examples/lib/etcdstart` serves only `s.RaftHandler()`; a sole member asked before its first
   election forwards `TimeToLive` to its own peer URL, gets rafthttp's `404`, and answers
   `ErrLeaseNotFound` for a lease a client saw. So `leasePeerURL` is false of `etcdstart`'s URLs, D1's
   gate `peerLeaseServed` cannot be met there, and leaseexpiry's final check is unproved (true in
   practice: a single voter keeps leading once it leads). Options: change the shared harness to serve
   a mux with the raft handler at `/raft`, `/raft/` and `LeaseHandler` at `/leases`,
   `/leases/internal` (as `etcdhttp.newPeerHandler`), with a `LeaseHandler` spec deriving
   `leasePeerURL` (3.2, C24); or have leaseexpiry use a starter that does. Not done: the harness is
   shared. The rejected alternative, the row under `soleMember` alone, left a trusted contract false
   as stated. (`repair3-boot.md` decision 1; `repair4-lease.md` decision 1.)

D31. **First boot: `member/` itself is not synced (F2-crash N3; widens D7).** etcd never fsyncs
   the data directory after creating `member/` (`fileutil.TouchDirAll` does no fsync,
   `client/pkg/v3/fileutil/fileutil.go:49-68`), nor the WAL's first segment's directory entry, so
   under POSIX crash semantics a crash can lose all of `member/`
   (`nonissues/etcd-member-dir-not-synced.md`, `blocks-proof: yes` pending D7). D7's option (c)
   (a fork fsync of `member/snap`) is therefore not enough by itself; option (a), a premise that a
   created directory entry is durable at the first sync of its file (ext4/xfs), settles both.

D32. **`Snap.snapRen`: a snapshot install's rename crashes whole (F2-crash N1).** New trusted
   snapshotter vocabulary `Snap.snapRen sd r` (the newest install's rename); `snapDbs_crash` and
   `snapSaving_crash` take the destination's revert list and resolve it jointly: kept (list `[]`)
   or lost (list unchanged, source file back), excluding "old backend back, snapshot file gone",
   which panics at `bootstrap.go:481-482`. It rests on a physical premise: a rename within one
   directory is atomic across a crash (ext4, xfs; POSIX does not promise it). Alternatives
   rejected: the rename's source in 4a's revert entries (4a cannot name the snapshotter's
   vocabulary), four combined laws. Also `Wal.walCreating` (trusted WAL vocabulary, F2-crash N2):
   `wal.Create`'s window between the rename and the parent fsync crashes to the WAL at
   `Recs.init` or no WAL; the disk's kind moves at the fsync (`repair6-crash.md`).

### Other decisions

D9. **The admin denial's principal (RR2).** W0's denial admits the request's principal, or no
   principal (`ErrUserEmpty` only, admissible once auth was ever enabled: a lagging member may apply
   `AuthEnable` between the check's two reads); a root compactor can be refused with `ErrUserEmpty`,
   never as another user. The certificate's name `tls` is kept only at 2a, where W0's one-identity
   scope makes it the principal or none (`adminDenied_of`), so W0 takes no `tls` argument.
   Alternative: thread `tls` into W0. Cost: none for clients beyond the `ErrUserEmpty` reading.
   `nonissues/etcd-admin-check-authenable-race.md` updated. (`repair2-client.md`.)
D10. **3h's `endsDecoded` family retired (RR3; supersedes C19).** `CheckTxnAuth`,
   `checkTxnPermission`, `checkTxnReqsPermission` take and give back only `txnReqOwn`/`msgsOwn`; the
   range-end facts come from W0's `*Own_unfold` and 3h's `*ReqOwn_msgAt` (`endsOk`).
   `EtcdServer.Txn`'s read path splits the request into two shares and rejoins them (statement
   unchanged). Deleted: `endsDecoded`, `opsDecoded`, `cmpsDecoded`, `endsDecoded_of_canon`,
   `endsDecoded_ro`, `endsDecoded_*`. Alternative: C19's give-back. Cost: none (no statement used
   them). (`repair2-server.md` RR3.)
D11. **The stringers' depth bound is kept and supplied (RR4).** Text marshaling recurses like
   `Marshal`/`Size`/`Clone`/`Equal`, which all take `depth c < depthMax`; dropping it for the
   stringers alone would make them the one unbounded protobuf recursion in the trust base.
   `EtcdServer.Txn` keeps a write-only depth premise (the read path gets `txnMsgDepth t ≤ 3` from
   `t.readonly`, not the reviewer's unconditional premise); `WarnOfExpensiveReadOnlyTxnRequest` takes
   the depth itself. Alternative: revert the premise. Cost: callers supply the bound. (`repair2-server.md`.)
D12. **`Config()` over `isServer`.** Available only after `Start` (since `start` writes two `Cfg`
   fields); every user in the code is post-start. Alternative: a fork change defaulting the fields in
   `NewServer`. Cost: none known. (`repair2-server-core.md`.)
D13. **The lessor's run-loop token is the fork's own** (partly supersedes C20): `NewLessor` returns
   the caller's `threadTok`, `Stop` returns none, removing a token `Cleanup` silently dropped.
   Alternative: C20's loan. (`repair2-server-core.md`.)
D14. **No thread token for the token provider.** `auth.NewTokenProvider` takes none (the request
   asked for one returned on success): the simple token's keeper runs on its fork's own token, so the
   "reserved token" design (stored in the keeper field, returned through `donec`) is removed and
   `keeper.stop` returns nothing. (`repair2-relay.md`.)
D15. **`leasehttp`'s lessor view is gated on `leaseURLOf`, not a premise.** `TimeToLiveHTTP` stays
   usable with any URL; only a caller that knows the URL is the serving member's own handler
   (`Leasehttp.leaseURLOf γ ep url`, from 2e's `leaseURLOf_intro`) gets the view (`ltlView`). Keeps
   the trusted spec's assumption to what `leasePeerURL` already assumes. (`repair2-relay.md`;
   `repair3-boot.md` item 3.) See D27.
D16. **`Server.spec` per endpoint**, under `srvAt` (D2); keeping `∀ ep` was unsound for the lease
   rows. (`repair2-relay.md`.)
D17. **The crash frame's access to the disk is a Perennial gap.** Perennial's crash frame gets only
   invariants and its own closure; the program keeps `diskState` in an invariant that callees' atomic
   updates open (`diskAcc`), and an accessor fired inside such an update cannot rule out that the frame
   took it (that needs the generation's `notCrashed`, which only a step owns). Common to every crash
   law over client-owned durable state (`beCrash`, `boltCrash`, the WAL's, the snapshotter's).
   Options: a crash-aware invariant in Perennial (opened at a step, handed whole to the crash frame),
   or durable callees whose updates admit a `crashed` answer; recorded in `notes/perennial-changes.md`
   (crash-frame extraction gap); F-raft-storage's "one-shot witness of `L → L'`" is the general fix
   proposed there. (`repair2-crash.md` decision 1; `repair4-raft-crash.md` requests.)
D18. **The vacancy comes with `raftState`'s crossing**, not a node crash law (false: R-A8 N1); raft's
   realization gives `raftState` a per-id generation record. (`repair2-crash.md` decision 2.) See 2.7.
D19. **The crash scope over the WAL's records** (`Wal.Recs.crashScopeOk`); `raftState_crash` covers
   snapshot batches written not at all or wholly, so the scope is only the window between the
   snapshot record and the state record (narrower than "no crash during a snapshot batch"), and
   conservative about a lagging follower at rest. (`repair2-crash.md` decision 3.) See 2.8, D29.
D20. **Generation independence as `⊣⊢` laws** (`*_gen`: raft's `global`, W0's, `srvNet`,
   `peerAddr`), not a "does not take `hG`" claim, since opaques take `hG` by the convention;
   `raftProto` and `Leasehttp.leaseURLOf` got explicit heap binders (they had none: unrealizable).
   (`repair2-crash.md` decisions 4, 8; `repair3-boot.md` item 3.)
D21. **One disk crash law, `disk_crash`.** `crashGone`, `crashGone_intro`, `diskIdle_crash` are
   deleted; every durable resource is in `diskState` at every step and files no longer move into the
   running server's invariant. (`repair2-crash.md` decision 5.) See 2.7.
D22. **`ReqCrashRecover` narrowed by the window inside `backend.New`** (`repair2-crash.md` decision 6):
   **closed** by D24, the window exclusion removed.
D23. **The rename's joint crash (R-A8 S1) left open** — **superseded, fixed (D32)**: the claim that
   "the model may fail a restart Go completes" was false (Go panics there, `bootstrap.go:481-482`;
   F2-crash N1); the joint crash law is `Snap.snapRen` (`repair6-crash.md`). (`repair2-crash.md`
   decision 7.)
D24. **The backend file moves through updates at open and close.** New `beOpenUpd p o ns R` (an AU
   from `beFile p o` to `beDurInv ∗ beSynced? ∗ beHist γ [I]`, fired at the ghost step before
   `bolt.Open`) in `New`, `newBackend`, `OpenBackend`, `OpenSnapshotBackend`; `beNew` no longer holds
   `beHist`. `backend.Close.spec` takes `beCloseUpd γ p Q` (from `beHist γ L` to `beFile p (some I)`,
   at the release after `DB.Close`) and posts `beFinal γ I ∗ Q I`; 2e's `bootstrapped*.Close` and
   `beClosable` follow. So a crash inside `New` or after `Close` finds the file in the client's crash
   state. Alternative: `beFile` handed over in the post (a crash window). Cost: every opener and
   closer changes shape. (`repair3-boot.md` item 7; `repair2-crash.md` requests 1-2.)
D25. **`applySnapshot`'s backend swap outside 4a's crash laws** (`repair3-boot.md` decision 3):
   **resolved** by D3.
D26. **`leaseViewLb γ ep 0` is free** (`leaseViewLb_zero`, W0, no premise: the trivial view means
   nothing known), replacing `viaPre`'s explicit `i = 0` alternative, one form of the per-member
   premise across 1c and 2a. (`repair4-lease.md` F2, decision 2.)
D27. **`TimeToLiveHTTP` takes the caller's view in its pre** (F3, soundness: `ltlView` accepted views
   obtained after the answer, deriving `False`). New `Leasehttp.leaseLbOpt γ ep vi` (2c's
   `srvLeaseLbOpt` is an abbrev); `ltlView γ ep vi url id found` is about the view held at the call;
   new `leaseURLOf_peerURL`. A caller with no view passes `none` and gets nothing.
   (`repair4-lease.md` F3, decision 3.)
D28. **Per-generation tokens are a token or the generation's `crashed`.** Their exclusivity (raft's
   vacancy; 2e's `diskIdle_excl`, `memberDisk_excl`) gives `crashed`, not `False`, and `diskIdle_agree`
   gives `⌜k = k'⌝ ∨ crashed` (fixing F-raft-storage F1/F-server-boot F1: `raftState ∗ crashed ⊢ False`
   made every crash frame trivial). A running program never sees the alternative (a step refutes it).
   Cost: a client cannot refute two vacancies in pure reasoning, only at a step; none did.
   (`repair4-raft-crash.md` decision 1.)
D29. **The crash scope enters the logic as an environment premise, `Wal.crashInScope`** (opaque
   `Prop`, `storage/wal/Api.lean`, like `ServerStorage.diskOk`): every crash leaves WAL records
   meeting `crashScopeOk`. `walRecs_crash`/`walWriting_crash` take it and give `⌜R'.crashScopeOk⌝`;
   `disk_crash` takes it and `ServerStorage.diskOk`, and loses its `crashOutOfScope` disjunct
   (deleted), so adequacy needs no out-of-scope case. `NewServer` takes no new premise (crash-free WP).
   Alternative: the opaque `crashOutOfScope` disjunct (unconstrained: F-server-boot F2). Cost: W0's
   adequacy statement gains the premise (`top.md` K6). (`repair5-crash.md` F2.) See 2.8.
D30. **`Net.dbIn` names its receiver** (F4): `Net.dbIn : w64 → w64 → IProp GF` (receiver, index);
   `recvd ν id m`, `raftOk ν id`'s `Process`, `saveOk ν lid sd`, `trCfg`, `net_alloc`,
   `recvChanAt`, `newSnapshotHandler` follow, and `EtcdServer.Process` takes the member's own
   `recvd`. Generation-independent (made at `SaveDBFrom`'s directory fsync). (`repair5-crash.md` F4.)
