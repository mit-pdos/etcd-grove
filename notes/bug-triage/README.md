# Bug triage against the proofs

Upstream bug reports classified against this repository's proved specs, per
`.claude/skills/bug-triage/SKILL.md`: how could the bug happen despite the proofs, and what
verification would exclude its class. One report per bug, `<repo>-<n>.md`. The classes (F+, F−, O,
A, C, X, N) are the skill's.

## Batch 2026-10-16: 151 correctness reports (122 etcd-io/etcd, 29 etcd-io/raft)

A pilot of ten, then every candidate of the searches (`gh issue list --label type/bug` with
correctness terms for etcd; all of etcd-io/raft's issues) that reports a correctness or safety
problem, leaving out build, documentation, performance, dependency, logging and metrics reports,
and etcd 0.4-era operational reports. The pins: etcd `107edf7e4`, raft `509271dac`
(`etc/goose.py`). Per-function states from `etc/verified-code.py` at `d606c9cac` (the first ten
and the first groups read the `Spec/`, `Proof/` and `Link.lean` files instead; each report says
which).

**Classes (primary).** F+ 12 · F− 42 · F split (one half F+, the other F−) 5 · A 22 · O 25 · C 11
· N 34 · **X 0**. No report contradicts a proved spec, and no bug was found in a spec or proof of
this repository. What the proofs miss is mostly scope: of the 59 bugs fixed before the pins, 47
would have passed the current proofs too (F− and the F− halves), for the reasons the proposals
below name.

### Trust-boundary assumptions found false or too strong

Not soundness errors of the proofs, but hypotheses of their results that the real code does not
meet (or met only by accident). Each needs a restated contract; see `notes/STATUS.md`, "Bug triage".

- **`apply.isCluster`'s `UpdateAttributes`** (`Proof/.../etcdserver/apply/Contracts.lean:339-343`)
  promises a return for every member id; the code panics on an id neither a member nor removed,
  reachable from the verified apply chain through a committed `ClusterMemberAttrSet` (etcd#16002;
  reproduced at the pin: `issues/etcd-membership-attrset-unknown-member-panic.md`).
- **`EtcdServer.Cleanup.wp_proof`** (pre `isPkgInit`, post `True`) closes the backend without the
  `bOpen γ 1` token the verified backend requires; with it, a reader holding a store slot "cannot
  crash" during shutdown, which etcd#17223 contradicts (`etcd-17223.md`,
  `issues/etcd-backend-close-inflight-rpc.md`).
- **`EtcdServer.revokeExpiredLeases.wp_proof`** (post `True`) starts a goroutine proposing
  `LeaseRevoke`s without the proposal credits the raft contract assumes; harmless only while no lease
  is granted in the verified scope (`etcd-15247.md`).
- **`EtcdServer.applyConfChange.wp_proof`** has no premise on the cluster state; true at the pin only
  because the membership methods now check the member, false on 3.6.0 (etcd#20009, `etcd-20009.md`).
- **`EtcdServer.compactRaftLog.wp_proof` and `EtcdServer.snapshot.wp_proof`** write the raft
  `MemoryStorage` outside their frames; harmless only while no verified code holds
  `ownMemoryStorage` across them (`raft-108.md`).
- Known and deliberate, now with a bug behind each: `storage.NewBackendQuota` (the disk never fills;
  etcd#16659) and `membership.localKept` (etcd#21966).

The audit these suggest (`cleanup-backend-quiescence`): every names-only server axiom whose
precondition is `True` or `isPkgInit`, against what its Go function writes or panics on.

### Bugs present at the pins (34 new `issues/` files)

Reproduced by a Go test, beside the issue (`issues/<slug>/*_test.go`), unless noted. The last
eight were written after the batch, at the user's request, including bugs in untranslated packages
(which step 7 does not require):

| Issue | Bug | Class | Upstream |
|---|---|---|---|
| [etcd-watch-restore-quiet-watcher-compacted](../../issues/etcd-watch-restore-quiet-watcher-compacted.md) | after a snapshot `Restore`, a quiet watcher is cancelled as compacted | O-fn (found triaging etcd#15271) | none |
| [etcd-watch-cancel-before-created-leak](../../issues/etcd-watch-cancel-before-created-leak.md) | a watch cancelled before `Created` leaks its server watcher | C (found triaging etcd#9416) | none |
| [etcd-membership-attrset-unknown-member-panic](../../issues/etcd-membership-attrset-unknown-member-panic.md) | `UpdateAttributes` panics on an unknown id; false contract | A-axiom | etcd#16002 |
| [etcd-election-campaign-error-orphan-key](../../issues/etcd-election-campaign-error-orphan-key.md) | failed `Campaign` leaves its key, `Resign` is a no-op | C-err | etcd#21128 |
| [etcd-lessor-renew-during-revoke](../../issues/etcd-lessor-renew-during-revoke.md) | `Renew` succeeds while `Revoke` deletes the keys | O-fn | etcd#14758, #21389 |
| [etcd-lease-requireleader-ctx-misaligned](../../issues/etcd-lease-requireleader-ctx-misaligned.md) | keep-alive channels paired with the wrong contexts | O-fn | etcd#22081 |
| [etcd-lease-requireleader-orphan-entry](../../issues/etcd-lease-requireleader-orphan-entry.md) | emptied keep-alive entry renewed forever | O-fn | etcd#22094 |
| [etcd-client-etcderror-no-grpcstatus](../../issues/etcd-client-etcderror-no-grpcstatus.md) | client errors lose their gRPC code; watchers halt | C-err | etcd#15539 |
| [etcd-simple-token-index-off-by-one](../../issues/etcd-simple-token-index-off-by-one.md) | simple token carries index e−1; other members reject it | O-fn | etcd#18437 |
| [etcd-hashkv-skips-compacted-revision](../../issues/etcd-hashkv-skips-compacted-revision.md) | `HashKV` skips the compaction revision, against its doc | O-fn | etcd#18337 |
| [etcd-snapshot-applied-index-stale](../../issues/etcd-snapshot-applied-index-stale.md) | after a snapshot the applied index stays 0: "too many requests" | A-pre | etcd#22528 |
| [etcd-snapshot-db-released-before-apply](../../issues/etcd-snapshot-db-released-before-apply.md) | a newer snapshot's release deletes the db not yet opened (deletion step only) | A-pre | etcd#18055, #20133, #20657 |
| [etcd-stalled-wal-no-tick](../../issues/etcd-stalled-wal-no-tick.md) | a stalled WAL `Save` stops raft's ticks | C-live | etcd#13527 |
| [etcd-wait-trigger-full-scan](../../issues/etcd-wait-trigger-full-scan.md) | `Trigger` scans every waiter; backlog never recovers | C-perf | etcd#22450 |
| [leasing-delete-keeps-count](../../issues/leasing-delete-keeps-count.md) | cached delete keeps `Count` | C-obs | etcd#22417 |
| [leasing-get-inflight-write](../../issues/leasing-get-inflight-write.md) | cached `Get` during the holder's own write | C-scope | etcd#20704 |
| [raft-uncommitted-size-reset-across-terms](../../issues/raft-uncommitted-size-reset-across-terms.md) | `MaxUncommittedEntriesSize` not enforced across terms | C-perf | raft#11 |
| [raft-memorystorage-compact-without-snapshot](../../issues/raft-memorystorage-compact-without-snapshot.md) | `Compact` without `CreateSnapshot` panics later | A-pre | raft#108 |
| [etcd-watch-sync-rescan-backlog](../../issues/etcd-watch-sync-rescan-backlog.md) | `syncWatchers` rescans the whole backlog (not reproduced; upstream's) | C-perf | etcd#22264 |
| [etcd-watch-inproc-cancel-storm-deadlock](../../issues/etcd-watch-inproc-cancel-storm-deadlock.md) | in-process watch deadlock (upstream's reproduction) | C-live | etcd#20716 |
| [etcd-backend-close-inflight-rpc](../../issues/etcd-backend-close-inflight-rpc.md) | backend closed under in-flight RPCs (not reproduced) | A-axiom | etcd#17223 |
| [etcd-snapshot-db-rename-no-dirsync](../../issues/etcd-snapshot-db-rename-no-dirsync.md) | snapshot db renamed without a directory sync (needs a crash) | O-fn | etcd#22498 |
| [etcd-inproc-watch-shared-auth](../../issues/etcd-inproc-watch-shared-auth.md) | in-process watches authorized with another user's token | O-path | etcd#17502 |
| [etcd-watch-choose-capped-compacted](../../issues/etcd-watch-choose-capped-compacted.md) | in `choose`'s capped branch a compacted watcher stays unsynced, cancelled again on every resync | C-scope (found triaging etcd#17529) | etcd#22294 |
| [etcd-election-resign-error-forgets-key](../../issues/etcd-election-resign-error-forgets-key.md) | `Resign` forgets the leadership when its own txn fails; the spec states it | C-err | etcd#22123 |
| [etcd-grpcproxy-watch-dead-broadcast](../../issues/etcd-grpcproxy-watch-dead-broadcast.md) | proxy watch broadcast dies on a backend close and keeps taking watchers | O-pkg | etcd#18231, #21813 |
| [etcd-grpcproxy-range-cache-auth](../../issues/etcd-grpcproxy-range-cache-auth.md) | proxy Range cache served regardless of the caller's auth | O-pkg | etcd#22065 |
| [etcd-rafthttp-snapshot-handler-nil-snapshot](../../issues/etcd-rafthttp-snapshot-handler-nil-snapshot.md) | rafthttp snapshot handler panics on a `MsgSnap` without a Snapshot | O-pkg | etcd#22440 |
| [etcd-fileutil-windows-trylock-locked](../../issues/etcd-fileutil-windows-trylock-locked.md) | Windows `TryLockFile` returns nil on a held lock; the purger deletes held WAL files (test compiles for Windows, not run) | O-pkg | etcd#14252 |
| [etcd-peer-members-handler-stale](../../issues/etcd-peer-members-handler-stale.md) | `/members` peer handler not linearizable (no test; harm not shown) | O-pkg | etcd#16687 |
| [etcd-bootstrap-confstate-zombie-voters](../../issues/etcd-bootstrap-confstate-zombie-voters.md) | **unconfirmed**: zombie members in the members bucket become raft voters at restart (the function shown; the upgrade path not) | O-fn (from triaging etcd#20967) | none |
| [etcd-compare-value-missing-key](../../issues/etcd-compare-value-missing-key.md), [etcd-watch-progress-request-dropped-unsynced](../../issues/etcd-watch-progress-request-dropped-unsynced.md), [leasing-cached-get-after-lease-expiry](../../issues/leasing-cached-get-after-lease-expiry.md) | documentation | N / C | etcd#10566, #17507, #19091 |

### The specs that would have excluded the bug (F+)

etcd#21536, #20488, #21535 (cache), #17247 (backend buffer), #17158 (backend delete), #13766,
#21636, #14382 (consistent index), #20573 (watch start revision), #20773, #21105 (premises of
`Compare` and `NewStore`), #7331 (read index), and the F+ halves of raft#392, etcd#20418, #14027,
#15220.

## Proposals, ranked by the bugs they would have caught

A bug counts for a proposal when the proposal would have excluded it (or, for C-live/C-perf, its safety stand-in would). The full statement sketch of each is in the reports that name it.

Read by theme, the proposals cluster:

- **Snapshot install on a running server** (`server-apply-snapshot`, `verify-watchable-restore`,
  `mvcc-restore-from-backend`, `server-snapshot-ci-latest`, `raft-pending-snapshot-ready`,
  `backend-commit-saves-ci`): 17 bugs; four present at the pins (one race reported three times, and
  the stale applied index). The proofs today assume a
  `Ready` carries no snapshot (`rnApP`, `ownRawNode`'s `snap = none`) and that the store is restored
  only from an empty backend. This is the largest single gap.
- **Crashes and durability** (`crash-restart-model`, `fs-crash-model`, `raft-durable-acks`,
  `wal-purge-lock-protocol`, `bbolt-kv-contract`): 18 bugs. Mostly blocked on crash semantics in
  Perennial's Lean port; `raft-durable-acks` and `backend-commit-saves-ci` are the crash-free first
  steps.
- **Membership** (`membership-state-model`, `verify-apply-conf-change`, `join-fresh-identity`,
  `cluster-attrset-known-member`, `verify-force-new-cluster`, `drop-local-kept`,
  `membership-read-barrier`): 15 bugs, and two of the false trust-boundary contracts above.
- **Auth with identities** (`inproc-client-auth-identity`, `auth-state-model`, `simple-token-index`,
  `grpcproxy-cache-auth`): 9 bugs; the auth specs today have no notion of the user.
- **Cheap and catching a bug present at the pins**: `leasing-cached-resp-count`,
  `range-keys-only-lease-fix`, `check-intervals-final-dels`, `raft-compact-needs-snapshot`,
  `election-key-accountable`, the first half of `simple-token-index`, and the restatements of
  `cluster-attrset-known-member` and `cleanup-backend-quiescence` (each a small spec change whose
  proof fails on the pinned code and goes through with the upstream fix).

| Proposal | # | Bugs | Cost |
|---|---|---|---|
| `server-apply-snapshot` | 8 | etcd#20426, etcd#20434, etcd#5857, etcd#18055, etcd#20133, etcd#20657, etcd#20271, etcd#22528 | large overall (leader half small to medium; snapshot-file ownership alone medium); needs raft-pending-snapshot-ready and the store/lessor/auth restores |
| `fs-crash-model` | 7 | etcd#6368, etcd#16596, etcd#22340, etcd#22498, etcd#14211, etcd#18881, etcd#18096 | large; crash semantics are a Perennial proposal first (Perennial's Rocq side has them) |
| `membership-state-model` | 6 | etcd#13196, etcd#13697, etcd#19557, etcd#20793, etcd#20967, etcd#20340 | medium to large (~500 Go lines); builds on verify-apply-conf-change |
| `crash-restart-model` | 5 | etcd#16666, etcd#20451, etcd#18679, etcd#14140, etcd#14143 | large; needs crash semantics (Perennial proposal) |
| `inproc-client-auth-identity` | 4 | etcd#17502, etcd#17623, etcd#20757, etcd#19296 | medium; the main work is an auth model with users |
| `model-kv-hash` | 4 | etcd#18337, etcd#15919, etcd#9022, etcd#20059 | medium (translate hash.go, hashByRev; corrupt.go checks small to medium more) |
| `auth-state-model` | 3 | etcd#14571, etcd#13883, etcd#13984 | large (~600 lines of the auth store) |
| `grpcproxy-watch-relay` | 3 | etcd#9988, etcd#18231, etcd#21813 | medium to large (~835 lines, untranslated package) |
| `mvcc-restore-from-backend` | 3 | etcd#19179, etcd#16693, etcd#17780 | medium to large; interrupted compaction needs crash-restart-model |
| `raft-durable-acks` | 3 | raft#197, etcd#14370, etcd#17855 | medium, no crash semantics (acks and votes justified by what the WAL/storage holds) |
| `verify-apply-conf-change` | 3 | etcd#19571, etcd#20009, etcd#21694 | medium (~300 lines) |
| `verify-client-lessor` | 3 | etcd#22081, etcd#22094, etcd#14631 | medium to large (client lease.go, ~650 lines) |
| `bbolt-kv-contract` | 2 | etcd#15498, etcd#17084 | large (~5k lines of bbolt; mmap and unsafe need a Perennial proposal) |
| `confchange-propose-outcome` | 2 | raft#354, raft#43 | small to medium |
| `join-fresh-identity` | 2 | etcd#20269, etcd#21178 | medium to large |
| `readindex-ctx-reuse` | 2 | raft#392, etcd#20418 | small to medium, ghost layer only |
| `server-snapshot-ci-latest` | 2 | etcd#17146, etcd#14382 | small to medium |
| `verify-client-new` | 2 | etcd#21830, etcd#18090 | medium (~200 lines); discharges premises of every client result |
| `verify-lease-keepalive-stream` | 2 | etcd#8904, etcd#9956 | medium (plus a small note on the grpc version the stream axioms need) |
| `verify-watchable-restore` | 2 | etcd#19487, etcd#15271 | large (the store's log model needs a jump to a snapshot) |
| `watch-under-compaction` | 2 | etcd#18089, etcd#17529 | medium to large (mvcc unit 6b) |
| `apply-path-cost-bounds` | 1 | etcd#22450 | small for the heap timeList against the existing specs; large for cost bounds (no cost model in Perennial) |
| `backend-commit-saves-ci` | 1 | etcd#14749 | small (the receipt) to medium (translate defrag, ~350 lines); a crash-free stand-in for crash-restart-model |
| `check-intervals-final-dels` | 1 | etcd#16380 | small |
| `cleanup-backend-quiescence` | 1 | etcd#17223 | restatement small; discharge medium to large (drain RPC handlers before Cleanup); plus the audit of the names-only server axioms |
| `client-error-status-codes` | 1 | etcd#15539 | small to medium |
| `client-write-at-most-once` | 1 | etcd#18424 | small to medium |
| `cluster-attrset-known-member` | 1 | etcd#16002 | small (restatement) to medium |
| `confchange-validation-complete` | 1 | raft#80 | small to medium |
| `drop-local-kept` | 1 | etcd#21966 | small to small-medium |
| `election-key-accountable` | 1 | etcd#21128 | small after PRs #21165/#22124 |
| `election-liveness-model` | 1 | raft#48 | large, low priority |
| `grpcproxy-cache-auth` | 1 | etcd#22065 | medium plus lru/IntervalTree boundary specs |
| `lease-clock-model` | 1 | etcd#20273 | large |
| `leasing-cached-read-own-writes` | 1 | etcd#20704 | large |
| `leasing-cached-resp-count` | 1 | etcd#22417 | small (~100 lines) |
| `leasing-linearizable-with-clock` | 1 | etcd#19091 | small on top of lease-clock-model |
| `membership-read-barrier` | 1 | etcd#16687 | medium to large, low priority |
| `raft-async-storage-writes` | 1 | raft#234 | medium (etcd does not use it) |
| `raft-compact-needs-snapshot` | 1 | raft#108 | small (raft) to small-medium (etcd) |
| `raft-guards-track-applied-config` | 1 | raft#456 | medium |
| `raft-pending-snapshot-ready` | 1 | raft#157 | moderate to large (STATUS stage S items 2-3) |
| `raft-progress-match-lt-next` | 1 | raft#148 | small |
| `raft-step-untrusted-msg` | 1 | etcd#15595 | small, low value |
| `raft-uncommitted-bound` | 1 | raft#11 | small to medium |
| `range-keys-only-lease-fix` | 1 | etcd#22209 | small |
| `readindex-no-silent-drop` | 1 | etcd#14027 | small to medium |
| `simple-token-index` | 1 | etcd#18437 | medium |
| `stalled-leader-stepdown` | 1 | etcd#13527 | small to medium for the no-clock obligation once upstream restructures the loop; large with a clock model |
| `transport-tracks-confstate` | 1 | raft#174 | medium, low priority |
| `txn-exact-check` | 1 | etcd#18667 | medium; ~15 consumers re-run |
| `verify-embed-close` | 1 | etcd#18853 | medium, low priority |
| `verify-etcdctl-txn-parse` | 1 | etcd#20773 | small to medium (~150 Go lines); also catches an unknown-operator panic at the pin |
| `verify-force-new-cluster` | 1 | etcd#20893 | small to medium |
| `verify-grpc-gateway-handlers` | 1 | etcd#19509 | medium (~2,500 generated lines); needs a net/http handler-lifetime model in Perennial |
| `verify-lease-expiry-leadership` | 1 | etcd#15247 | medium |
| `verify-lessor-renew-revoke` | 1 | etcd#14758 | medium to large |
| `verify-rafthttp-handlers` | 1 | etcd#22440 | small to medium |
| `verify-rafthttp-peer-status` | 1 | etcd#22480 | medium to large |
| `wal-purge-lock-protocol` | 1 | etcd#14252 | medium crash-free |
| `watch-client-cancel-reaches-server` | 1 | etcd#9416 | small to medium |
| `watch-prevkv` | 1 | etcd#6900 | medium (nil case needs watch-under-compaction) |
| `watch-progress-answered` | 1 | etcd#17507 | small to medium |
| `watch-progress-synced` | 1 | etcd#15220 | medium |
| `watch-stream-no-cyclic-wait` | 1 | etcd#20716 | medium after the fix |
| `watch-sync-bounded-scan` | 1 | etcd#22264 | small to medium after a fix is translated |

## All reports

| Bug | Title | Class | Decisive fact | Proposal |
|---|---|---|---|---|
| [etcd#864](etcd-864.md) | 0.4.2: term #18446744073709551615 | N (O-pkg) | etcd 0.4's own removal sentinel; code long gone | — |
| [etcd#5857](etcd-5857.md) | restart fails: db index does not match snapshot (3.0) | F− (O-fn) | fix in pin; createMergedSnapshotMessage is an axiom with post True, applySnapshot verified only for no snapshot | `server-apply-snapshot` |
| [etcd#6368](etcd-6368.md) | WAL rename without directory fsync | F− (O-pkg, A-model) | fix in pin; WAL not verified (0 of 78 functions), Save promises nothing | `fs-crash-model` |
| [etcd#6900](etcd-6900.md) | nil PrevKv panic in gRPCWatcher | F (O-pkg) | resolver removed, never translated; the server proof excludes prev_kv by premise (watchReqOk) | `watch-prevkv` |
| [etcd#7331](etcd-7331.md) | ReadIndex may read stale value (new leader before first commit) | F+ | fix in pin; ownRaftGhost_read_arrive needs the commit index at an entry of the leader's term | — |
| [etcd#8904](etcd-8904.md) | gRPC 1.7.3 "send on closed channel" | F− (A-axiom, O-fn) | fixed in grpc-go v1.7.4; the stream axiom srvRawStreamIs would have been false of grpc 1.7.3 | `verify-lease-keepalive-stream` |
| [etcd#9022](etcd-9022.md) | functional-tester false "data inconsistency" (HashByRev) | F− (O-fn) | fix in pin; hashByRev untranslated, but treeIndex.Keep.spec's premise c ≤ rev forbids the buggy Keep(0) | `model-kv-hash` |
| [etcd#9416](etcd-9416.md) | clientv3: canceling Watch sends no WatchCancelRequest | F− (C-perf) | fix in pin; run's model lets a cancel be sent or not, so the pre-fix code verifies too; a narrower leak remains at the pin | `watch-client-cancel-reaches-server` |
| [etcd#9956](etcd-9956.md) | 3.3.7 "send on closed channel" | F− (A-axiom) | fixed in grpc-go v1.20; the verified Watch/recvLoop rely on stream use after the handler returns, which grpc ≤ 1.19 did not allow | `verify-lease-keepalive-stream` |
| [etcd#9988](etcd-9988.md) | watch through grpc-proxy delays or misses events (3.3.9) | O-pkg (unsettled) | most likely the dead-broadcast defect of #21813, present at pin; grpcproxy untranslated | `grpcproxy-watch-relay` |
| [etcd#10566](etcd-10566.md) | Compare != on a missing key is false | N (documentation) | applyCompare.spec gives cmpHolds false for every value comparison on an empty range; undocumented | — |
| [etcd#13196](etcd-13196.md) | 3.5.0 resurrects ancient unremovable members | F− (O-fn) | v2/v3 two-store mechanism gone at pin; applyConfChange axiom and Members.spec say nothing about which members | `membership-state-model` |
| [etcd#13527](etcd-13527.md) | disk-stalled, partitioned leader does not step down | C-live (A-model, A-pre) | present at pin, reproduced; raftNode.start (verified) calls Save inside the tick loop; a Save that never returns meets isRNWal; CheckQuorum off by premise | `stalled-leader-stepdown` |
| [etcd#13697](etcd-13697.md) | 3.5.0 still resurrects members, "member count is unequal" | N (undiagnosed; cand. O-fn) | duplicate peer URLs impossible via the API, so the stores diverged; join bootstrap untranslated | `membership-state-model` |
| [etcd#13766](etcd-13766.md) | Inconsistent revision and data (consistent index outside the batch lock) | F+ | fix in pin; pre-fix SetConsistentIndex outside the lock can't be justified by hook_set_au/ci_advance_au, breaks stOk/commitOk | — |
| [etcd#13822](etcd-13822.md) | jetcd watch silent after partition and compaction | N (O-fn, C-scope) | withdrawn as a jetcd bug; the compacted-cancel path is outside the specs | — |
| [etcd#13883](etcd-13883.md) | AuthStore.Recover does not invalidate caches | F− (O-fn, C-other) | fixes in pin; cacheP not tied to backend users/roles; isRangeOpPermitted returns some boolean | `auth-state-model` |
| [etcd#13984](etcd-13984.md) | auth: revision in header is old, member revision diverges | N (dup, undiagnosed; A-model, C-other) | crash/replay not modeled; auth revision not in the modeled state | `auth-state-model` |
| [etcd#13989](etcd-13989.md) | Response header revision may not reflect the body | N (O-fn) | leases have no revision; newHeader.spec gives the read-time revision; LeaseLeases not translated | — |
| [etcd#14027](etcd-14027.md) | leader change → "timed out waiting for read index response" | F (stepLeader F+, API F− / C-live) | fixes in both pins; stepLeader.spec requires the postponement, but requestCurrentIndex/ReadIndex allow ErrTimeout after a dropped request | `readindex-no-silent-drop` |
| [etcd#14140](etcd-14140.md) | stale read with loss of un-fsynced writes (Jepsen/LazyFS) | A-model (N) | never reproduced; every candidate cause needs a crash losing unsynced state | `crash-restart-model` |
| [etcd#14143](etcd-14143.md) | split brain / lost committed write with loss of un-fsynced data | A-model (O-pkg, N) | never root-caused; needs durable state lost at restart; MustSync.spec shows commit-only HardState changes are written without fsync by design | `crash-restart-model` |
| [etcd#14211](etcd-14211.md) | 3.4.18 data inconsistency ("range failed to find revision pair") | A-axiom (A-model; unsettled) | rangeKeys.spec excludes the Fatal; the bad state needs bbolt's postulated KV contract broken or memory corruption | `fs-crash-model` |
| [etcd#14252](etcd-14252.md) | WAL file deleted on Windows, restart fails | O-pkg (A-model) | still at pin: Windows lockFile returns nil when already locked; purgeFile assumed with post True | `wal-purge-lock-protocol` |
| [etcd#14370](etcd-14370.md) | single-member cluster acks a write before the WAL write | F− (A-model) | fixes in pin; the raft pin self-acks only at Advance, but PendingOk (.self …) asks only a term bound and Save is True → True | `raft-durable-acks` |
| [etcd#14382](etcd-14382.md) | won't start after alarm list and a power-off | F+ (O-fn/A-model) | same bug as #21636; pre-fix defer can't prove applyEntryNormal's post k = m.index | `server-snapshot-ci-latest` |
| [etcd#14571](etcd-14571.md) | new member: empty perm cache after snapshot, auth failures | F− (O-fn, C-other) | fix in pin; Recover/refreshRangePermCache not translated; the auth layer's reject/pass is a free choice | `auth-state-model` |
| [etcd#14631](etcd-14631.md) | NewSession hangs after server SIGSTOP | O-fn (C-live; arguably N) | lessor.Grant not translated; NewSession.spec partial correctness; by design: bound it with WithContext | `verify-client-lessor` |
| [etcd#14749](etcd-14749.md) | panic: failed to recover v3 backend from snapshot (3.5.5) | F− (O-fn, A-model) | fix in pin; defrag (untranslated) committed without the ci hook; commit specs don't require that the hook ran | `backend-commit-saves-ci` |
| [etcd#14758](etcd-14758.md) | attached keys deleted before lease expired | O-fn (A-model; diagnosis unsettled) | the Renew/Revoke race (#21389) is present at the pin and reproduced; Renew names-only, Revoke unproved | `verify-lessor-renew-revoke` |
| [etcd#15220](etcd-15220.md) | Requested progress notifications overtake watch events | F (F+ in shape, F− in content) | fix in pin; ctrlAnswers .progress = False breaks the old recvLoop proof, but no spec ties a progress notification at R to delivery up to R | `watch-progress-synced` |
| [etcd#15243](etcd-15243.md) | MemberList fails after adding a member to a 1-node cluster | N | works as intended: a linearizable MemberList needs a quorum; serializable option in pin | — |
| [etcd#15247](etcd-15247.md) | old leader stuck in fdatasync revokes all leases | F− (O-fn, A-model) | fix in pin; revokeExpiredLeases is a names-only axiom with post True, LeaseRenew untranslated, no clock | `verify-lease-expiry-leadership` |
| [etcd#15271](etcd-15271.md) | Watch events go back in time after snapshot install | F− (O-fn) | fix in pin; invariant lets a synced watcher's minRev lag, and Restore is not verified | `verify-watchable-restore` |
| [etcd#15498](etcd-15498.md) | invalid db page layout (bytesToRev panic at restore) | O-pkg (A-model) | bbolt's pages are below the *_kv axioms; restoreIntoIndex untranslated | `bbolt-kv-contract` |
| [etcd#15539](etcd-15539.md) | EtcdError lacks GRPCStatus, codes Unknown | C-err (O-fn) | present at pin, reproduced; isHaltErr/openWatchClient specs over an opaque statusCode | `client-error-status-codes` |
| [etcd#15595](etcd-15595.md) | raft panics in maybeAppend under robustness blackhole | N (A-model) | the test proxy spliced the stream into a message no leader sent; raft.Step's isMessage premise excludes it | `raft-step-untrusted-msg` |
| [etcd#15919](etcd-15919.md) | wrong hash when a scheduled compaction resumes after restart | F− (C-obs, A-model, O-fn) | fix in pin; hashes not modeled; resume needs store.restore on a non-empty backend | `model-kv-hash` |
| [etcd#16002](etcd-16002.md) | new member with a wrong ID panics every member | A-axiom (O-fn) | reproduced at pin; isCluster's UpdateAttributes triple promises a return for any id, the code panics on an unknown id; rqOk has no ClusterMemberAttrSet case | `cluster-attrset-known-member` |
| [etcd#16380](etcd-16380.md) | checkIntervals misses a later sibling's delete | A-pre (found by the proof) | = issues/etcd-txn-check-intervals-sibling.md; checkIntervals_nodup proved only under siblingSafeL | `check-intervals-final-dels` |
| [etcd#16396](etcd-16396.md) | Mutex myKey per session blocks locking across pods | N | misreading; mutex_exclusion proves exclusion across sessions; a shared key would break it | — |
| [etcd#16596](etcd-16596.md) | fails to start after power failure during bbolt init | O-pkg (A-model, N) | torn write in bbolt DB.init; upstream documented won't-fix; bbolt.Open spec allows an error | `fs-crash-model` |
| [etcd#16659](etcd-16659.md) | error reported after a successful write (quota) | N (A-axiom) | documented; quotaApplierV3.Txn.spec states "applied, then ErrNoSpace"; NewBackendQuota axiom assumes the disk never fills | — |
| [etcd#16666](etcd-16666.md) | wait-cluster-ready timeout gives stale linearizable reads | F− (A-model, O-pkg) | fix in pin; needs a crash losing HardState.Commit | `crash-restart-model` |
| [etcd#16687](etcd-16687.md) | /members peer handler not linearizable | O-pkg (N) | still present at the pin; etcdhttp not translated; harm never shown | `membership-read-barrier` |
| [etcd#16693](etcd-16693.md) | Revision decreased by 100 (compaction panic) | F− (probable; O-fn, A-model) | same failpoint as #17780, fix in pin; diagnosis unsettled; store.restore axiom only for an empty bucket | `mvcc-restore-from-backend` |
| [etcd#17084](etcd-17084.md) | 3.4.18 "page already freed" plus a member diverging | O-pkg (A-model; unsettled) | bbolt freelist not translated; never reproduced | `bbolt-kv-contract` |
| [etcd#17146](etcd-17146.md) | [3.4] db ci < snapshot index after a kill | A-model (unsettled; O-fn) | durability across a kill not modeled; EtcdServer.snapshot is an axiom | `server-snapshot-ci-latest` |
| [etcd#17155](etcd-17155.md) | inconsistency under heavy writes (no data) | N | no version, logs or data; serializable reads documented, rangeReadOk drops readLogOk for them | — |
| [etcd#17158](etcd-17158.md) | batchTx.UnsafeDelete may break linearizability | F+ | fix in pin; on the old code the backend proof breaks at Unlock's no-commit branch (freeOk needs ndel = 0) | — |
| [etcd#17223](etcd-17223.md) | UnsafeRange panics during shutdown | A-axiom (O-path) | the names-only axiom EtcdServer.Cleanup (pre isPkgInit, post True) closes the backend without the bOpen token the verified backend needs; still reachable at the pin | `cleanup-backend-quiescence` |
| [etcd#17247](etcd-17247.md) | Duplicated watch event in robustness test | F+ | regression and fix in pin; buggy dedupe sets used = 1 on an empty buffer, breaking ownBB bb (canon []) | — |
| [etcd#17265](etcd-17265.md) | 3.4.29 nil zap logger panic in embed/serve.go | F− (O-pkg) | 3.4-only; fixed at pin; embed not translated | — |
| [etcd#17502](etcd-17502.md) | v3election: internal watches authorized with another user's token | O-path (C-scope) | v3election/v3client/adapter not translated; auth specs have no user identity | `inproc-client-auth-identity` |
| [etcd#17507](etcd-17507.md) | No answer to a progress request on a new watch | F− (C-live) | fix in pin; partial correctness: nothing says a progress request is ever answered | `watch-progress-answered` |
| [etcd#17529](etcd-17529.md) | Watch events starved/lost on one stream | F− (C-scope; C-live/C-perf) | fix in pin; faulty branch only runs below the compaction revision, excluded by crevFrozen | `watch-under-compaction` |
| [etcd#17623](etcd-17623.md) | blocked gRPC Campaign fails on an expired auth token | O-path (A-model, C-err) | in-process v3client keeps the caller's token; token TTL untranslated time; Campaign.spec allows any error | `inproc-client-auth-identity` |
| [etcd#17780](etcd-17780.md) | Revision decreasing after panic during compaction | F− (O-fn, A-model) | fix in pin; store.restore axiom covers only an empty Key bucket; crash not modeled | `mvcc-restore-from-backend` |
| [etcd#17855](etcd-17855.md) | tocommit(21) panic on a new node joining | A-model (O-path; unsettled) | a process under the same ID acked and lost the log; the raft spec excludes the panic via heartbeat_commit_le_last / rnInit | `raft-durable-acks` |
| [etcd#18053](etcd-18053.md) | watcher doesn't read older events | N | misuse: Watch("") without WithPrefix watches one key; createRangeOk states exactly that | — |
| [etcd#18055](etcd-18055.md) | panic when two snapshots arrive in a short period | A-pre (O-fn) | present at pin; raftNode.start's Release deletes the .snap.db applySnapshot hasn't opened yet; both verified only under "a Ready has no snapshot" | `server-apply-snapshot` |
| [etcd#18089](etcd-18089.md) | watch drops an event when compacting on delete | F− (C-scope) | fix in pin; watch specs assume crevFrozen (no compaction) | `watch-under-compaction` |
| [etcd#18090](etcd-18090.md) | index out of range in Client.dial | O-fn (unsettled, possibly N) | Sync/dial not translated; the non-empty check at the pin is an assertion, off in production | `verify-client-new` |
| [etcd#18096](etcd-18096.md) | zero page after power-off | A-model (O-pkg) | power loss and possibly an unhonored fdatasync; no fs model | `fs-crash-model` |
| [etcd#18231](etcd-18231.md) | grpc-proxy stops sending watch events after a server cancel | O-pkg | the broadcast goroutine exits on channel close with no re-watch; present at pin | `grpcproxy-watch-relay` |
| [etcd#18267](etcd-18267.md) | Count ignores Min/Max revision filters | N | documented in rpc.proto; executeRange's count is srvCount, exactly the reported outcome | — |
| [etcd#18337](etcd-18337.md) | HashKV skips revisions at or below the compaction revision | O-fn (C-obs) | present at pin and reproduced; hash.go names-only, hasher axiom returns any value; a documentation mismatch | `model-kv-hash` |
| [etcd#18424](etcd-18424.md) | client retry may break Serializable | C-other (O-pkg for jetcd) | = issues/etcd-client-retry-put-ctx-error.md; etcdInterceptorOk takes the server spec as persistent, so a write applied twice is admitted | `client-write-at-most-once` |
| [etcd#18437](etcd-18437.md) | simple token spuriously invalid on another member | O-fn (C-err) | present at pin, reproduced; Authenticate puts ConsistentIndex() = e-1 in the token; tokenSimple untranslated | `simple-token-index` |
| [etcd#18534](etcd-18534.md) | publish times out after rebooting a single node | N (C-live candidate; O-pkg) | converted to a discussion, never diagnosed | — |
| [etcd#18667](etcd-18667.md) | revision in a txn's range may cause inconsistency | F− (C) | fix in pin; backendStep's txn case does not tie rejection to checkTxn; non-plain txns excluded by txnPlain | `txn-exact-check` |
| [etcd#18679](etcd-18679.md) | write txn End()s before panicking on failure | F− (A-model; C-scope) | fix in pin; the error branch is dead under the premises, and the harm needs a crash and restart | `crash-restart-model` |
| [etcd#18853](etcd-18853.md) | double close of errc in embed Etcd.Close | O-pkg (likely misuse) | embed not translated; close(e.errc) outside closeOnce, still so at the pin | `verify-embed-close` |
| [etcd#18881](etcd-18881.md) | 3.5.0 won't start after power outage | A-model (unsettled) | needs a crash; candidates #13766 (F+) and power loss destroying unsynced files | `fs-crash-model` |
| [etcd#18933](etcd-18933.md) | Talos cluster "corrupt cluster" | N | support discussion, no diagnosis; the CORRUPT alarm reaction is verified | — |
| [etcd#19091](etcd-19091.md) | leasing serves stale cached Get after session lease expiry | C-scope (A-model) | verified; getCached promises only the record at acquisition; decisions.md "not linearizable, and not claimed to be", against doc.go | `leasing-linearizable-with-clock` |
| [etcd#19179](etcd-19179.md) | missing delete event on watch at compaction revision | F− (O-fn; A-model) | fix in pin; restoreIntoIndex names-only, store.restore specified only for an empty backend; trigger is a crash mid-compaction | `mvcc-restore-from-backend` |
| [etcd#19296](etcd-19296.md) | proxy watchers hang after the auth token expires | O-pkg (O-path) | token as a ctx value, so the verified streamKeyFromCtx puts all users on one stream; same mechanism as issues/etcd-inproc-watch-shared-auth.md | `inproc-client-auth-identity` |
| [etcd#19441](etcd-19441.md) | watch sync fails when Fragment is false | N | raw-gRPC test client's 4 MiB receive limit; batching is as specified (ebAdd) | — |
| [etcd#19487](etcd-19487.md) | watch response revision below the starting revision | F− (O-fn) | fix in pin; only the unspecified watchableStore.Restore creates the future minRev | `verify-watchable-restore` |
| [etcd#19509](etcd-19509.md) | "Write called after Handler finished" via JSON-gateway watch | F− (O-pkg) | fix in pin; gateway code not translated | `verify-grpc-gateway-handlers` |
| [etcd#19557](etcd-19557.md) | [3.5] learner promotion not persisted to v3store | F− (O-fn) | 3.5-only; at pin PromoteMember does a plain put; nothing specifies the members bucket | `membership-state-model` |
| [etcd#19571](etcd-19571.md) | [3.4] ci not persisted on member deletion | F− (via the applyConfChange axiom) | 3.4-only; on main every commit's hook saves ci; the violated rule is the trust-boundary contract applyConfChange.spec | `verify-apply-conf-change` |
| [etcd#19700](etcd-19700.md) | resolver Metadata uncomparable, grpc panic | F− (O-pkg) | fix in pin; naming packages and grpc balancer not translated | — |
| [etcd#19778](etcd-19778.md) | NewSession's LeaseGrant has no deadline | N (C-live) | WithContext lets the caller cancel; NewSession.spec is partial correctness | — |
| [etcd#20009](etcd-20009.md) | --force-new-cluster start panics (3.6.0) | F− (A-axiom; O-fn, A-model) | fixes in pin; the panic comes from verified applyAll through the applyConfChange axiom, which would have been false on the pre-fix code | `verify-apply-conf-change` |
| [etcd#20059](etcd-20059.md) | 3.5.11 inconsistency after SIGSEGV in rafthttp decode | A-model (O-pkg, N) | a wild pointer breaks the reliable-memory assumption; rafthttp and corrupt.go untranslated | `model-kv-hash` |
| [etcd#20133](etcd-20133.md) | "failed to open snapshot backend" panic (Antithesis) | A-pre (dup of #18055) | same race at the default configuration | `server-apply-snapshot` |
| [etcd#20269](etcd-20269.md) | tocommit panic on learner rejoin after reset | A-model (O-path; N upstream) | the wiped process took the old learner's ID by peer URL | `join-fresh-identity` |
| [etcd#20271](etcd-20271.md) | snapshot db corrupt: "Page expected to be: 5" | F− (A-pre, O-fn; A-model) | fix in pin (applySnapshot holds bemu.Lock, Defragment bemu.RLock); specs admit the race since rnApP fixes snapshot = nil and defrag/OpenSnapshotBackend untranslated | `server-apply-snapshot` |
| [etcd#20273](etcd-20273.md) | lease never expires under rolling restarts | N (A-model) | by design: Promote resets every lease's TTL unless LeaseCheckpoint is on; no upper bound promised | `lease-clock-model` |
| [etcd#20340](etcd-20340.md) | panic "failed to nodeToMember" at restart | F− (O-fn, A-axiom) | fix in pin; PromoteMember reached only through the applyConfChange axiom | `membership-state-model` |
| [etcd#20418](etcd-20418.md) | stale reads caused by process pausing | F (etcd half F+, raft half F−) | same bug as raft#392; etcd fix in pin; a resend with the same id needs a second rdFresh | `readindex-ctx-reuse` |
| [etcd#20426](etcd-20426.md) | "consistent_index isn't equal to snapshot index" | F− (A-axiom / A-pre) | assertion removed in pin; sender site an axiom with post True, receiver site excluded by rnApP's snapshot = nil | `server-apply-snapshot` |
| [etcd#20434](etcd-20434.md) | "update of consistent index not advancing" | A-pre (unsettled; N) | assertion verified, but fires in the snapshot branch rnApP excludes; trigger is an undiagnosed bad snapshot | `server-apply-snapshot` |
| [etcd#20451](etcd-20451.md) | 3.5.6 member out of sync, stale data | A-model (undiagnosed) | applyEntries_kv makes apply deterministic, so the divergence came from a different starting state (restart/snapshot), outside scope | `crash-restart-model` |
| [etcd#20488](etcd-20488.md) | Cache breaks the Resumable guarantee | F+ | fixes in pin; pre-fix Register breaks the demux invariant RegsStart.start_ok; cache_Watch_delivery forbids the observed log | — |
| [etcd#20573](etcd-20573.md) | Antithesis found Watch failure | F+ (diagnosis unsettled; alt N) | watch at revision -1 fixed by #20693 in pin; recvLoop proof gets 0 ≤ startRev only from the fix's branch | — |
| [etcd#20582](etcd-20582.md) | cache returns a different state for the same revision | N | withdrawn: harness took the header revision for the data's; cacheGetOk states exactly that | — |
| [etcd#20655](etcd-20655.md) | fast watch creation breaks reliable guarantee | N | robustness-harness slice race, fixed in the test only | — |
| [etcd#20657](etcd-20657.md) | race between snapshot cleanup and apply (3.5.18) | A-pre (dup of #18055) | same race | `server-apply-snapshot` |
| [etcd#20704](etcd-20704.md) | several correctness bugs in client/v3/leasing | C-scope (C-other) | all 4 cases present at pin; leasing_cached_get_stable claims freshness only while the holder commits nothing; cases 2, 4 new and reproduced | `leasing-cached-read-own-writes` |
| [etcd#20716](etcd-20716.md) | in-process watch deadlocks on a cancellation storm | C-live (O-path) | cycle among four verified loops; partial-correctness specs admit it | `watch-stream-no-cyclic-wait` |
| [etcd#20757](etcd-20757.md) | member promote via follower fails with auth | F− (O-pkg/O-fn) | fix in pin; promoteMemberHTTP/peer handler untranslated | `inproc-client-auth-identity` |
| [etcd#20773](etcd-20773.md) | etcdctl lease comparison panics | F+ (O-pkg) | fix in pin; a verified caller could not meet Compare.spec's premise cmpArgOf .lease for a string | `verify-etcdctl-txn-parse` |
| [etcd#20793](etcd-20793.md) | promotion-not-persisted propagated via snapshot across upgrades | F− (O-fn) | 3.5-only; applySnapshot verified only for a nil snapshot | `membership-state-model` |
| [etcd#20893](etcd-20893.md) | --force-new-cluster keeps learners after a snapshot | F− (O-fn) | fix in pin; GetEffectiveNodeIDsFromWALEntries/CreateConfigChangeEnts names-only | `verify-force-new-cluster` |
| [etcd#20967](etcd-20967.md) | 3.6 upgrade recovers old/duplicate members | F− (O-pkg, A-model; residual hazard) | causes absent at pin; but the members bucket now seeds raft's ConfState at restart | `membership-state-model` |
| [etcd#21105](etcd-21105.md) | etcdutl hashkv panics: no lessor | F+ (O-pkg) | fix in etcdutl (not translated) in pin; NewStore.spec's premise isLessor excludes a nil lessor | — |
| [etcd#21128](etcd-21128.md) | failed Campaign leaves its key; Resign is a no-op | C-err | present at pin, reproduced; Campaign.spec's error case is ∃ st', electionState; Resign.spec states the no-op | `election-key-accountable` |
| [etcd#21178](etcd-21178.md) | tocommit panic on a "fresh" learner after remove/add | A-model (O-path) | the ID had run and acked before; same as raft#197 | `join-fresh-identity` |
| [etcd#21335](etcd-21335.md) | panic: etcdserver: leader changed (Milvus) | N | Milvus panics on a retryable ErrLeaderChanged; requestCurrentIndex.spec allows it | — |
| [etcd#21535](etcd-21535.md) | cache: data race between store.Get and Apply | F+ | fix in pin; pre-fix &s.latest after RUnlock can't get the read-only ownership getSnapshot.spec requires | — |
| [etcd#21536](etcd-21536.md) | cache: Get(WithRev(rev)) can return the wrong value | F+ | fix in pin; store.getSnapshot.spec pins the result to the greatest snapshot ≤ rev | — |
| [etcd#21610](etcd-21610.md) | learner removed after receiving a snapshot | N, unsettled (O-pkg) | log shows a committed RemoveNode; only the MemberRemove RPC proposes one; likely the reporter's tooling | — |
| [etcd#21636](etcd-21636.md) | alarm entries leave the consistent index behind; restart fails | F+ | fix in pin; with the pre-fix defer, applyEntryNormal's post applyThread ⟨m.index, …⟩ fails | — |
| [etcd#21694](etcd-21694.md) | MemberUpdate clears a learner's IsLearner flag | F− (O-fn, C-obs) | fix in pin; UpdateRaftAttributes untranslated, applyConfChange axiom silent on the members map | `verify-apply-conf-change` |
| [etcd#21813](etcd-21813.md) | new watchers added to a disconnected watchBroadcast | O-pkg (O-path) | no stopped state; the client's final Canceled (revision 0) resets nextrev to 1; present at pin | `grpcproxy-watch-relay` |
| [etcd#21830](etcd-21830.md) | 3.7 clientv3.New blocks on DialTimeout | F− (O-fn) | fix in pin; New/newClient/dial not translated | `verify-client-new` |
| [etcd#21966](etcd-21966.md) | IsLocalMemberLearner panics on Status during self-removal | O-fn (A-pre) | still present at pin; Status/IsLocalMemberLearner untranslated; the interceptor path excludes it only by the axiom membership.localKept; = issues/etcd-unary-interceptor-learner-removed.md | `drop-local-kept` |
| [etcd#22065](etcd-22065.md) | proxy serializable Range cache leaks data across auth contexts | O-pkg (O-path) | cache hits keyed only by request bytes, before any auth; present at pin | `grpcproxy-cache-auth` |
| [etcd#22081](etcd-22081.md) | closeRequireLeader pairs keep-alive chans with wrong ctxs | O-fn (C-live) | present at pin, reproduced; client lessor not translated; Session assumes isEtcdLease (KeepAlive isChanAny) | `verify-client-lessor` |
| [etcd#22094](etcd-22094.md) | closeRequireLeader leaves an emptied keepAlive entry renewed forever | O-fn (C-perf, C-live) | present at pin, reproduced; isEtcdLease has no liveness or expiry | `verify-client-lessor` |
| [etcd#22209](etcd-22209.md) | keys_only drops the lease (v3.7 regression) | A-pre (found by the proof) | = issues/etcd-range-keys-only-lease.md; server specs state leaseZ | `range-keys-only-lease-fix` |
| [etcd#22264](etcd-22264.md) | syncWatchers rescans the whole backlog, stalls apply | C-perf (C-live) | present at pin, verified; rangeEvents.spec returns all of [minRev, curRev+1): the spec states the quadratic read | `watch-sync-bounded-scan` |
| [etcd#22340](etcd-22340.md) | missing fsync of the snap directory in SaveDBFrom | F− (O-pkg, A-model) | fix in pin; snap package names-only, no file-system model | `fs-crash-model` |
| [etcd#22417](etcd-22417.md) | leasing: Count not cleared after a cached delete | C-obs | present at pin, reproduced; no invariant ties Count to Kvs | `leasing-cached-resp-count` |
| [etcd#22440](etcd-22440.md) | rafthttp snapshotHandler nil deref on MsgSnap without Snapshot | O-pkg | present at pin, introduced by raft v3.7's pointer Snapshot; rafthttp names-only | `verify-rafthttp-handlers` |
| [etcd#22450](etcd-22450.md) | leader's apply backlog does not recover | C-perf (O-fn, A-model) | present at pin, reproduced; verified timeList.Trigger scans every waiter (no cost model) | `apply-path-cost-bounds` |
| [etcd#22480](etcd-22480.md) | rafthttp peerStatus latches inactive | O-pkg | rafthttp names-only; ActiveSince returns any time | `verify-rafthttp-peer-status` |
| [etcd#22498](etcd-22498.md) | OpenSnapshotBackend renames the db without a directory sync | O-fn (A-model, C-scope) | present at pin; OpenSnapshotBackend names-only, applySnapshot verified only for a nil snapshot | `fs-crash-model` |
| [etcd#22528](etcd-22528.md) | new joiner stuck in "too many requests" in an idle cluster | A-pre (C-live) | present at pin, reproduced; applySnapshot never calls setAppliedIndex; apply thread proved only for batches with no snapshot (rnApP) | `server-apply-snapshot` |
| [raft#11](raft-11.md) | maxUncommittedSize not enforced across terms | C-perf | present at pin, reproduced; NState has no uncommittedSize, increaseUncommittedSize.spec returns a bare ok; etcd never sets the limit | `raft-uncommitted-bound` |
| [raft#43](raft-43.md) | stepWait not used in ProposeConfChange | N (C-err) | documented; the spec gives nodeErr, so a drop comes back nil | `confchange-propose-outcome` |
| [raft#48](raft-48.md) | no leader elected when peers start simultaneously | F− (C-live, A-model) | fix in pin; time-seeded math/rand meets lockedRand.Intn.spec too; no clock or probability | `election-liveness-model` |
| [raft#80](raft-80.md) | conf-change validation false positives | N (C-err) | documented conservative guard; propConfStep with becomeLeaderLog's pci := logLast states exactly the refusal | `confchange-validation-complete` |
| [raft#108](raft-108.md) | "need non-empty snapshot" panic (MemoryStorage) | A-pre (O-path) | reproduced at pin and raft main; Compact without CreateSnapshot violates the MemoryStorage instance's premise, undocumented and unchecked | `raft-compact-needs-snapshot` |
| [raft#119](raft-119.md) | panic at commit 10,001 | N | a nil rc.node race in the user's application | — |
| [raft#138](raft-138.md) | follower learns commit 1 RTT late after drops | N (C-perf) | open enhancement; HeartbeatOk states the Commit ≤ Match cap; lifting it alone breaks heartbeat_commit_le_last | — |
| [raft#148](raft-148.md) | probe from index < Match | F− (C-perf) | fix in pin; MaybeDecrTo's spec states the body, PrOk never relates Next to Match | `raft-progress-match-lt-next` |
| [raft#157](raft-157.md) | invariants gap: committing a stale snapshot | N (O-fn) | the invariant is a conjunct of ownRaftLog; only stableSnapTo/appliedSnap break it transiently | `raft-pending-snapshot-ready` |
| [raft#174](raft-174.md) | 4th node cannot rejoin raftexample cluster | O-pkg (N) | raftexample (deleted upstream) adds transport peers only from flags and ConfChange entries; rafthttp names-only | `transport-tracks-confstate` |
| [raft#197](raft-197.md) | follower panics on a commit-index regression | A-model (N) | the follower lost its persisted log and rejoined under its ID | `raft-durable-acks` |
| [raft#234](raft-234.md) | split brain with async storage writes? | N (A-pre) | the maintainer's argument is the proof's I1+I2; but every spec fixes AsyncStorageWrites=false | `raft-async-storage-writes` |
| [raft#266](raft-266.md) | leader not replaced under simplex partition | N (C-live) | Raft's follower failure detector is leader traffic; CheckQuorum fixed to false by the specs' premise; no liveness spec | — |
| [raft#280](raft-280.md) | Figure 8: leader elected without committed entries? | N | misreading; maybeCommit commits only current-term entries, leader completeness proved | — |
| [raft#354](raft-354.md) | ConfChange silently converted to a no-op | N (C-err) | documented, and stepLeader's spec states exactly the reported outcome | `confchange-propose-outcome` |
| [raft#372](raft-372.md) | EnterJoint without quorum overlap | N | closed invalid; overlap of adjacent configurations is proved | — |
| [raft#392](raft-392.md) | with retries, read index can be stale | F (etcd half F+, raft half F−) | both fixes in pins; raft's specs assume rdFresh, stricter than v3.7's documented contract | `readindex-ctx-reuse` |
| [raft#456](raft-456.md) | TLA+ model permits split brain (no unapplied-config guard) | N (A-pre) | Go and the Lean model have the campaign guard; Go is safe only under A1 (Advance after ApplyConfChange) | `raft-guards-track-applied-config` |
| [raft#515](raft-515.md) | MoreUpToDateCorrectInv in etcdraft.tla is false | N | TLA+ model only; the Lean proof proves leader completeness through the vote table without that invariant | — |
