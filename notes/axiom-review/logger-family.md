# The caller-supplied zap logger family (axiom sweep, 2026-11-07)

Survey of every trust-boundary axiom (`axiom <F>.wp_proof`, 400 in `Proof/`, `RaftWitness/Proof/`,
`PorcupineDag/Proof/`, read in `/shared/etcd-grove-sweep3`) whose Go function logs through a `*zap.Logger`
that a caller supplies (a parameter, or a field set at construction from a caller's argument). The
fault (`notes/axiom-review/zap-zero.md`): `&zap.Logger{}` is non-nil but has a nil `core` (and nil
`clock`), so `Debug/Info/Warn/Error/Check` panic at `logger.go:331` (`log.core.Enabled`), `Panic/Fatal`
at `:339`, `Core().Enabled(..)` and `SugaredLogger.*f` (`sugar.go:349/361`, `s.base.Core().Enabled`)
on the nil interface. `Named`, `WithOptions`, `Sugar` do not touch the core (they only clone), so
storing or wrapping a zero logger is harmless; only a later log call panics.

Go read at the etcd pin `673da07c8fab` (note `.lake/go-src/etcd` is at `249d76bea7`, not the pin). Method:
a go/ast tool (`logreach`, kept out of the repository) (go/ast, same-package call graph, methods resolved by name,
depth 3 and 8) over the 123 etcd-module axioms, flagging logging calls on `lg`/`log`/`zap` receivers
and logger arguments passed across packages; then every hit read by hand, with its Lean spec. The 74
non-etcd axioms outside the standard library, grpc, protobuf and zap (k8s, bbolt, raft, bridge,
probing, clockwork, humanize) were checked by reading their specs and their logger use (below).
Lines: Go `server/...` means `etcd/server/...` at the pin; Lean spec line is the `abbrev <F>.spec`.


## Repaired (premise fixes 6, 2026-11-11)

Every row of the family is repaired; no axiom was added or removed. #9-11 were repaired first, by
`dbe4904326` (2026-11-10, sweep B3-2); the other 24 by premise fixes 6, part A (the Scope's A.2,
`/shared/tmp/premise-fixes-6/scope.md`; the decisions D1-D6 in the Scope's "Decisions"; `notes/decisions.md` gets part A's entry with the stage).
The rule: a logger premise is `zapLoggerOk lg` (`Spec/go_uber_org/zap/Defs.lean`: `lg ≠ null` and
the persistent `zap.loggerRaw lg`) where Go logs through `lg` without a nil check, and
`zapLoggerOrNil lg` (`⌜lg = null⌝ ∨ zapLoggerOk lg`) where Go checks `lg != nil` first or replaces
nil by `zap.NewNop()`. zap's own `Debug`/`Info`/`Warn`/`Error`/`Fatal`/`Check` take `zapLoggerOk l`
(A.1); `Panic` keeps `l ≠ null` (decision D4: on a zero logger it panics with a runtime error instead
of `msg`, which only a `recover` inspecting the value can tell apart). "Text" means the axiom's spec
file changed; "via P" means its text is unchanged and its meaning changed through the predicate P.

| # | Axiom | Fix |
|---|---|---|
| 1 | `monitorFileDescriptor` | text: `⌜lg ≠ null⌝` → `zapLoggerOk lg` |
| 2 | `txn.WarnOfExpensiveRequest` | text: `⌜lg ≠ null⌝` → `zapLoggerOk lg` |
| 3 | `txn.WarnOfFailedRequest` | text: `⌜lg ≠ null⌝` → `zapLoggerOk lg` |
| 4 | `v3rpc.logUnaryRequestStats` | text: `⌜lg ≠ null⌝` → `zapLoggerOk lg` |
| 5 | `storage.NewBackendQuota` | text: `zapLoggerOk lg` added (was nothing on `lg`); its other gaps, a nil `be` and `Cost(nil)`, stay open (D5, `notes/audit.md`) |
| 6 | `auth.newTokenProviderJWT` | text: `zapLoggerOrNil lg` added (Go replaces nil by `NewNop`) |
| 7 | `rafthttp.addPeerToProber` | text: `zapLoggerOrNil lg` added (every use under `lg != nil`) |
| 8 | `auth.NewAuthStore` | text: `⌜lg ≠ null⌝` → `zapLoggerOrNil lg`; its post's `authInv` holds `zapLoggerOk` of the stored logger |
| 9 | `lease.NewLessor` | `dbe4904326`: `⌜lg = null⌝ ∨ zapLoggerOk lg` in the pre and in `lessorCfg` |
| 10 | `lease.lessor.scheduleCheckpointIfNeeded` | `dbe4904326`, via `lessorCfg` |
| 11 | `lease.lessor.Promote` | `dbe4904326`, via `lessorCfg` |
| 12 | `storage.OpenBackend` | via `openPre`: `cfg.Logger' ≠ Loc.null` → `zapLoggerOk cfg.Logger'` |
| 13 | `backend.newBoltLoggerZap` | text: `⌜cfg.Logger' ≠ Loc.null⌝` → `zapLoggerOk cfg.Logger'` |
| 14 | `mvcc.hashStorage.Store` | via `hashStorageOk`: `⌜lg ≠ null⌝` → `zapLoggerOk lg` |
| 15 | `traceutil.Trace.LogWithStepThreshold` | via `ownTrace`: the conjunct `zapLoggerOrNil v.lg'` added |
| 16 | `auth.authStore.AuthInfoFromTLS` | via `authInv`: `⌜lg ≠ null⌝` → `zapLoggerOk lg` (its missing context premise is a separate gap, `notes/audit.md`) |
| 17 | `snap.Snapshotter.SaveDBFrom` | via `isSnapshotter`: `snapLgAddr ss ↦□ lg ∗ zapLoggerOk lg` added (decision D1: `bootOk`'s `isSnapshotter` asserts it) |
| 18 | `membership.RaftCluster.Recover` | text: `(∃ lgc, membership.rcLgAddr c ↦□ lgc ∗ zapLoggerOk lgc)` added |
| 19 | `backend.backend.Snapshot` | via `isBackend`: `lg ≠ Loc.null` → `zapLoggerOk lg` |
| 20 | `Client.roundRobinQuorumBackoff` | via `isClientLogger`: `lg ≠ null` → `zapLoggerOk lg` |
| 21 | `Client.streamClientInterceptor` | via `isClientLogger`, as #20 |
| 22 | `EtcdServer.adjustTicks` | text: `isPkgInit etcdserver` → `... ∗ isServerReqM on s E ρ ∗ srvLoggerOk s` |
| 23 | `EtcdServer.purgeFile` | text: `isPkgInit etcdserver` → `... ∗ isServerReadM on s E γr` (its `srvReadFieldsAtM` holds `zapLoggerOk` of `s.lg`) |
| 24 | `EtcdServer.ensureLeadership` | via `srvReadFieldsAtM`: `⌜v.lg ≠ null⌝` → `zapLoggerOk v.lg` |
| 25 | `EtcdServer.publishV3` | via `srvMonitorPermitM`, which gains `srvLoggerOk s` |
| 26 | `EtcdServer.monitorClusterVersions` | via `srvMonitorPermitM`, as #25 |
| 27 | `EtcdServer.monitorStorageVersion` | text: `srvLoggerOk s` added |

New vocabulary: `zapLoggerOrNil` (`Spec/go_uber_org/zap/Defs.lean`), `srvLoggerOk s := ∃ lg, srvLgAddr s
↦□ lg ∗ zapLoggerOk lg` (etcdserver), `snap.snapLgAddr`. Left out (decision D3): the `lgMu` reader slot
that `s.Logger()` takes in #22, #23 and #25-27; it goes to a later bounds follow-up. Go evidence:
`examples/premisefix/zaplogger` (zero loggers panic, the constructors' loggers are zap loggers, the
family, the examples' loggers). The text below is the survey as written on 2026-11-07, before the repair;
its summaries carry notes on the repair.

## The family (exploitable: the triple is false for a zero logger)

"Indep." = a program reaches the axiom's call with a zero logger without first calling a zap
axiom (so the axiom is refuted on its own, not only through `zap.Logger.*`'s refutation).

| # | Axiom | Lean spec | Go function | Logging call(s) | How the logger reaches it | Premise on it in Lean | Exploitable? | Indep. |
|---|---|---|---|---|---|---|---|---|
| 1 | `monitorFileDescriptor.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/etcdserver/monitorFileDescriptor.lean:27` | `server/etcdserver/metrics.go:215` | `lg.Warn` `metrics.go:226,232,237` | parameter | `⌜lg ≠ null⌝` | yes, when FD usage reaches 80% of the limit (a program can lower `RLIMIT_NOFILE`) or `FDUsage`/`FDLimit` fails | yes (unexported) |
| 2 | `txn.WarnOfExpensiveRequest.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/WarnOfExpensiveRequest.lean:29` | `server/etcdserver/txn/util.go:29` | via `warnOfExpensiveGenericRequest`, `lg.Warn` `util.go:93` | parameter | `⌜lg ≠ null⌝` | yes, `time.Since(now) > d` (any `d`, e.g. 0) | yes (exported) |
| 3 | `txn.WarnOfFailedRequest.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/WarnOfFailedRequest.lean:26` | `server/etcdserver/txn/util.go:40` | `lg.Warn` `util.go:46` (unconditional) | parameter | `⌜lg ≠ null⌝` | yes, always | yes (exported) |
| 4 | `v3rpc.logUnaryRequestStats.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/logUnaryRequestStats.lean:40` | `server/etcdserver/api/v3rpc/interceptor.go:91` | `lg.Core().Enabled` `interceptor.go:94` (nil interface, unconditional); `lg.Debug` `:187`, `lg.Warn` `:203` | parameter (from `newLogUnaryInterceptor`'s `s.Logger()`) | `⌜lg ≠ null⌝` | yes, always | yes (unexported) |
| 5 | `storage.NewBackendQuota.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/storage/NewBackendQuota.lean:39` | `server/storage/quota.go:75` | `lg.Info` `quota.go:80,93,116`, `lg.Warn` `:107`, each in `quotaLogOnce.Do` (first call per process); `:93` guarded `lg != nil` | parameter | **none** (even `nil` panics for `cfg < 0` or `> 0`) | yes, first call in the process | yes (exported) |
| 6 | `auth.newTokenProviderJWT.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/auth/newTokenProviderJWT.lean:36` | `server/auth/jwt.go:127` | `lg.Error` `jwt.go:135` (bad options), `lg.Warn` `:146` (unknown option keys); `nil` replaced by `NewNop` | parameter | **none** | yes, an options map with an unknown key or a bad value | yes (unexported; via `NewTokenProvider`, proved) |
| 7 | `rafthttp.addPeerToProber.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/addPeerToProber.lean:25` | `server/etcdserver/api/rafthttp/probing_status.go:41` | `lg.Warn` `:52` (`p.Status` error; `p` is any `Prober`); goroutine `monitorProbingStatus` `lg.Warn` `:68,82` (unhealthy peer after 5 s, clock drift); guarded `lg != nil` only | parameter | **none** | yes, a prober whose `Status` errs, or an unreachable peer (panic in the goroutine) | yes (unexported) |
| 8 | `auth.NewAuthStore.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/auth/NewAuthStore.lean:111` | `server/auth/store.go:955` | via `refreshRangePermCache` (`store.go:998`), `as.lg.Debug` `range_perm_cache.go:138` (unconditional); `lg.Warn` `store.go:962` (bad cost) | parameter, stored in `as.lg` (and `schema.authBackend.lg`, the same `lg`) | `⌜lg ≠ null⌝` | yes, always | yes (exported) |
| 9 | `lease.NewLessor.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/lease/NewLessor.lean:133` | `server/lease/lessor.go:208` | goroutine `runLoop` (`lessor.go:245`) -> `checkpointScheduledLeases` -> `findDueScheduledCheckpoints`, `le.lg.Debug` `lessor.go:798` (guarded `le.lg != nil` only) | parameter, stored in `le.lg` | `⌜lg ≠ null⌝` | yes: after `SetCheckpointer` and `Promote`, a granted lease whose checkpoint falls due (panic in the loop goroutine) | yes |
| 10 | `lease.lessor.scheduleCheckpointIfNeeded.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/lease/lessor__scheduleCheckpointIfNeeded.lean:31` | `server/lease/lessor.go:753` | `le.lg.Debug` `lessor.go:760` (guarded `le.lg != nil` only) | stored `le.lg`, by `NewLessor` (#9) | **none** (`lessorCfg` holds `lF "lg" lp ↦□ lg`, no fact) | yes, `cp ≠ nil` and remaining TTL > checkpoint interval (any `cp` in the pre) | yes (unexported; via `Grant`/`Checkpoint`, proved) |
| 11 | `lease.lessor.Promote.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/lease/lessor__Promote.lean:32` | `server/lease/lessor.go:480` | via `scheduleCheckpointIfNeeded` (`lessor.go:491,530`), `:760` | stored `le.lg`, by `NewLessor` | **none** (`lessorInv`, `lessorCfg`) | yes, a lease in the map and a checkpointer set (the example in the brief) | yes (exported via `Lessor`) |
| 12 | `storage.OpenBackend.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean:52` | `server/storage/backend.go:75` | deferred `cfg.Logger.Info` `backend.go:84` (unconditional), `:92`; `newBackend` `:39,45` | `cfg.Logger` (parameter's field) | `openPre`'s `cfg.Logger' ≠ Loc.null` | yes, always | yes (exported) |
| 13 | `backend.newBoltLoggerZap.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/storage/backend/newBoltLoggerZap.lean:32` | `server/storage/backend/backend.go:1135` | none in the body (`Named`/`WithOptions`/`Sugar` are safe); the **post** `boltLogger l` claims every `Debugf/Infof/Warnf/Errorf` returns, and `SugaredLogger.log` calls `s.base.Core().Enabled` (`zap sugar.go:349`) | `bcfg.Logger`, wrapped | `⌜cfg.Logger' ≠ Loc.null⌝` | yes: bbolt's `Open` calls `lg.Infof` (fork `db.go:217`) through it | yes (unexported; via `backend.New`) |
| 14 | `mvcc.hashStorage.Store.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/hashStorage__Store.lean:27` | `server/storage/mvcc/hash.go:156` | `s.lg.Info` `hash.go:157` (unconditional) | stored `s.lg`, by `NewHashStorage` (proved, `hash.go:128`) | `hashStorageOk`: `lg ≠ null` | yes, always | yes (exported) |
| 15 | `traceutil.Trace.LogWithStepThreshold.wp_proof` | `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Trace__LogWithStepThreshold.lean:31` | `pkg/traceutil/trace.go:192` | `t.lg.Info` `trace.go:195` (guarded `t.lg != nil` only) | stored `t.lg`, by `newTrace`/`EnsureTrace` (proved, `trace.go:85,102`) | **none** (`ownTrace` says nothing of `lg`; `newTrace`/`EnsureTrace` take any `lg`) | yes, always | yes (exported; `EnsureTrace(ctx, &zap.Logger{}, op)` then `Log`) |
| 16 | `auth.authStore.AuthInfoFromTLS.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/auth/authStore__AuthInfoFromTLS.lean:27` | `server/auth/store.go:1025` | `as.lg.Warn` `store.go:1053`, `as.lg.Debug` `:1061` | stored `as.lg`, by `NewAuthStore` (#8) | `authInv`: `aF "lg" st ↦□ lg ∗ ⌜lg ≠ null⌝` (`InvAuth.lean:1217`) | yes, any `ctx` whose peer is a `credentials.TLSInfo` with a verified chain | no: `NewAuthStore` already logs |
| 17 | `snap.Snapshotter.SaveDBFrom.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Snapshotter__SaveDBFrom.lean:40` | `server/etcdserver/api/snap/db.go:37` | `s.lg.Info` `db.go:85` (success, unconditional), `s.lg.Warn` `:77` | stored `s.lg`, by `snap.New(lg, dir)` in `bootstrap` | `isSnapshotter` (opaque `snapshotterRO`, no logger fact; never produced in Lean, assumed through `bootOk`) | yes, on a successful save | no: comes through `bootstrap`/`NewServer` |
| 18 | `membership.RaftCluster.Recover.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__Recover.lean:63` | `server/etcdserver/api/membership/cluster.go:262` | `c.lg.Info` `cluster.go:286` (per member; `clusterImageOk` puts the local one there), `:296`, `:272`; `onSet(c.lg, …)` (`UpdateCapability`'s `lg.Info`, guarded `lg != nil`) | stored `c.lg`, by `bootstrap` (`NewClusterFromURLsMap`) | **none** (`isRaftCluster` is the mutex and `rcLockInv`; produced only through `bootOk`) | yes, always | no: through `bootstrap`/`NewServer` |
| 19 | `backend.backend.Snapshot.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Snapshot.lean:70` | `server/storage/backend/backend.go:381` | goroutine `b.lg.Warn` `backend.go:408` (snapshot still open after max(30 s, size/100 MB/s)); `b.lg.Fatal` `:388` and `batch_tx.go:302,394` (error paths, excluded) | stored `b.lg`, by `backend.New`/`newBackend` (proved) from `bcfg.Logger` | `isBackend`: `bF "lg" b ↦□ lg ∗ ⌜lg ≠ Loc.null⌝` | yes, a caller that holds the snapshot open long enough (the pre gives a `threadTok` held until `Close`, no time bound) | no: `backend.New`'s bbolt `Open` panics first (#13) |
| 20 | `Client.roundRobinQuorumBackoff.wp_proof` | `Spec/go_etcd_io/etcd/client/v3/Client__roundRobinQuorumBackoff.lean:28` | `client/v3/client.go:491` | the returned closure: `c.GetLogger().Debug` `client.go:497` or `:500` (one always runs); the post `backoffOk bf` says every call returns | stored `c.lg`, by `New`/`newClient` (proved) from `cfg.Logger` (`client.go:394`); also `WithLogger` | `retryClientOk` -> `isClientLogger`: `lg ≠ null` (an invariant) | yes, any call of the backoff | yes (`newClient` with `cfg.Logger` set and `AutoSyncInterval = 0` does not log) |
| 21 | `Client.streamClientInterceptor.wp_proof` | `Spec/go_etcd_io/etcd/client/v3/Client__streamClientInterceptor.lean:28` | `client/v3/retry_interceptor.go:117` | the returned interceptor: `c.GetLogger().Error` `retry_interceptor.go:125` (`getToken` error), `:139` (streamer error with retries on) | stored `c.lg`, as #20 | `retryClientOk` -> `isClientLogger`: `lg ≠ null` | yes, conditional: `getToken` fails (`Username`/`Password` set, which `clientCfgOk` does not exclude, and `Authenticate` errs) or a call option sets `max > 0` and the streamer errs; the post `etcdStreamInterceptor f` is what grpc's `NewStream` axiom relies on | yes (on those paths) |
| 22 | `EtcdServer.adjustTicks.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__adjustTicks.lean:26` | `server/etcdserver/server.go:468` | `lg.Info` `server.go:475` or `:488` or `:491` (one always) | stored `s.lg` (`s.Logger()`), by `NewServer` from `cfg.Logger` | **none: no premise on `s` at all** | yes, always | no (`NewServer` logs `server.go:305` first); but refuted anyway by `&EtcdServer{}` (nil `lgMu`) |
| 23 | `EtcdServer.purgeFile.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__purgeFile.lean:26` | `server/etcdserver/server.go:607` | via `fileutil.PurgeFileWithoutFlock(lg, …)`, `lg.Info` `client/pkg/fileutil/purge.go:49` (unconditional), `:93`; `lg.Fatal` `server.go:618,620` | stored `s.lg`, by `NewServer` | **none: no premise on `s`** | yes, always | no; refuted anyway as #22 |
| 24 | `EtcdServer.ensureLeadership.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__ensureLeadership.lean:47` | `server/etcdserver/server.go:917` | `lg.Debug` `server.go:921` (active member), `lg.Warn` `:930,937` | stored `s.lg`, by `NewServer` | none on its value: `isServerReqM`/`isServerReadM` do not mention `s.lg` (`srvReadFieldsAt` has `v.lg ≠ null`), `srvLgReader` is the lock only | yes, every path but "still leader" | no (`NewServer` logs first) |
| 25 | `EtcdServer.publishV3.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__publishV3.lean:33` | `server/etcdserver/server.go:1828` | `lg.Warn` `:1841,1868`, `lg.Info` `:1858` (one always) | stored `s.lg`, by `NewServer` | none (`srvMonitorPermitM` = `isServerReqM` + id field + permit) | yes, always | no |
| 26 | `EtcdServer.monitorClusterVersions.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__monitorClusterVersions.lean:34` | `server/etcdserver/server.go:2241` | `lg.Info` `server.go:2249` (on `stopping`, always), `s.lg.Error` `:2258`; `serverversion.Monitor`'s logs | stored `s.lg`, by `NewServer` | none (`srvMonitorPermitM`) | yes, at shutdown | no |
| 27 | `EtcdServer.monitorStorageVersion.wp_proof` | `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__monitorStorageVersion.lean:48` | `server/etcdserver/server.go:2264` | `lg.Info` `server.go:2272` (on `stopping`, always); `Monitor.UpdateStorageVersionIfNeeded`'s logs | stored `s.lg`, by `NewServer` | none (`isServerReqM`, `srvSVRes`) | yes, at shutdown | no |

27 axioms. 17 are refutable on their own (#1-15, #20, #21; the cleanest, unconditional ones: #3,
#4, #8, #12, #14, #15, #20, then #2, #5, #11). **(Repaired, 2026-11-11: all 27; #9-11 by `dbe4904326`, the
rest by premise fixes 6, part A; see "Repaired" above.)** Nine take no premise on the logger at all (#5, #6,
#7, #10, #11, #15, #18, #22, #23), and #24-27 say nothing about its value. For #16-19 and #22-27 the
only producer already logs through a zap axiom, so in Go they are reached only after a panic
elsewhere; they are still in the family because their premises do not carry the property, so the
repair must add it to them (or to the predicates they take) for the restatement to be stated, not
only true by a meta-argument about who builds the object. **(Repaired: the predicates now carry it: `authInv` (#16),
`isSnapshotter` (#17), #18's own premise, `isBackend` (#19), `srvLoggerOk`/`srvReadFieldsAtM`/
`srvMonitorPermitM` (#22-27).)**

## Log through a logger, but not exploitable

| Axiom | Spec | Go logging | Why not |
|---|---|---|---|
| `EtcdServer.monitorKVHash` | `EtcdServer__monitorKVHash.lean:32` | `server.go:2288…` | pre pins `CorruptCheckTime = 0`: returns at `server.go:2281` before `s.Logger()` |
| `EtcdServer.monitorCompactHash` | `EtcdServer__monitorCompactHash.lean:32` | `server.go:2320`, `corrupt.go` | pre pins `CompactHashCheck` off: returns at `server.go:2311` |
| `EtcdServer.monitorDowngrade` | `EtcdServer__monitorDowngrade.lean:32` | none before return | `serverversion.NewMonitor` only stores the logger; pre pins `DowngradeCheckTime = 0`, returns at once (its `l` is unconstrained, harmlessly) |
| `snap.Snapshotter.DBFilePath` | `Snapshotter__DBFilePath.lean:33` | `s.lg.Warn` `db.go:107` | only when the file is missing; the pre's `fileHolds` says it exists |
| `schema.MustUnsafeSaveConfStateToBackend` | `MustUnsafeSaveConfStateToBackend.lean:34` | `lg.Panic` `confstate.go:32` | only on `json.Marshal` error, impossible for a `ConfState` |
| `schema.membershipBackend.MustSaveMemberToBackend` | `…MustSaveMemberToBackend.lean:53` | `s.lg.Panic` `membership.go:54` | only on `json.Marshal` error of a `*Member`, impossible |
| `schema.membershipBackend.MustReadMembersFromBackend` | `…MustReadMembersFromBackend.lean:47` | `s.lg.Panic` `membership.go:86,183` | only on undecodable records, excluded by `membersDecode bk` |
| `backend.ValidateCalledInsideApply` / `OutSideApply` / `InsideUnittest`, `backend.VerifyBackendConsistency` | `ValidateCalled*.lean:29`, `VerifyBackendConsistency.lean:29` | `lg.Panic` `verify.go:36,45`, `lg.Fatal` `:54`, `lg.Debug` `:79` | logging only under `ETCD_VERIFY`; already the `ETCD_VERIFY` family (`notes/axiom-review/etcd-verify.md`), where `Panic` fires with any logger; the zero logger adds nothing |
| `features.NewDefaultServerFeatureGate` | `NewDefaultServerFeatureGate.lean:42` | `featuregate` `Set`/`SetFromMap`/`OverrideDefault` (`feature_gate.go:236-316`) | stores `lg` only; `isFeatureGate` covers only `Enabled`, which does not log |
| `NewMaintenance` (client) | `NewMaintenance.lean:27` | `maintenance.go:116` stores `c.GetLogger()` | post `True`: no method contract; the `dial` closure is not run (a call-graph false positive) |
| `newCorruptionChecker`, `v3alarm.NewAlarmStore`/`AlarmStore.restore`, `RaftCluster.SetBackend`, `membershipBackend.MustDeleteMemberFromBackend`, `v3rpc.NewMaintenanceServer`, `NewCluster` | (specs mention a logger) | none | store the logger or do not log |

Outside etcd's modules, nothing is in the family:
- **bbolt** (`Open_kv`, `Put_kv`, ...): logs through its own `bolt.Logger`, which the specs require
  to be a `boltLogger` (`Spec/go_etcd_io/bbolt/Logger.lean:105`); they consume the predicate, and the
  falsity is in its producer `newBoltLoggerZap` (#13).
- **raft** (`DescribeConfChange`, the `String`s; also in `RaftWitness/`): no logging. Raft's own
  `Logger` is an interface whose contract `isLogger` (`Proof/go_etcd_io/raft/v3/InvLogger.lean:46`) is
  a definition; the server's raft logger is `NewRaftLoggerZap(cfg.Logger)` (its contract
  `rnLoggerZapOk` is true: `Sugar` is safe), and `isLogger lok` of it is assumed inside `bootOk`
  (`InvBoot.lean:283`, `InvRestart.lean:403`), false for a zero `cfg.Logger` (`zapRaftLogger.Infof` ->
  `SugaredLogger`). A named premise, not an axiom; it needs the same predicate.
- **k8s**: `klog.*`, `trace.New`/`LogIfLong` log through klog's global logger; `HandleCrashWithLogger`
  takes a `logr` value whose zero value is a no-op (and its spec has no panic in flight). No zap.
- **PorcupineDag**, bridge, probing, clockwork, humanize: no logger.
- Related, not this family: `grpclog.SetLoggerV2.wp_proof` (`{{True}} SetLoggerV2(l) {{True}}`, any
  `LoggerV2`): a `LoggerV2` whose methods panic (e.g. a zapgrpc logger over `&zap.Logger{}`) makes grpc's
  later internal logging (channelz `Info`) panic under the grpc axioms. A separate, interface-level
  question.

## Producers whose premise must carry the new predicate (`zapLogger lg`)

**(Repaired, 2026-11-11.)** Every producer below now carries the predicate (it is `zapLoggerOk`,
not the survey's working name `zapLogger`): `zap.NewNop`'s post gives `zapLoggerOk`; `NewLessor` takes
`zapLoggerOrNil` (`dbe4904326`); `NewAuthStore` takes `zapLoggerOrNil` and its `authInv` holds
`zapLoggerOk`; `openPre` and `newBoltLoggerZap` take `zapLoggerOk cfg.Logger'`; `NewServer` takes
`zapLoggerOk cfg.Logger'` and the server's invariants hold `zapLoggerOk v.lg` in place of
`⌜v.lg ≠ null⌝`; `newLogUnaryInterceptor`, `NewTokenProvider`, `NewHashStorage`, `Transport.Start`
pass it on; `newTrace`/`EnsureTrace` take `zapLoggerOrNil`; `backend.New`/`newBackend` take
`zapLoggerOrNil cfg.Logger'` (D2a), and the frozen mvcc API `New`/`NewStore` take `zapLoggerOrNil lg`
(D2b); `clientCfgOk` and `isClientLogger` hold `zapLoggerOk`; `bootOk`'s `isSnapshotter` carries it (D1), and `RaftCluster.Recover`'s own premise does (#18); the examples' entry specs take `zapLoggerOk`. Raft's
`isLogger lok` of `NewRaftLoggerZap(cfg.Logger)` inside `bootOk` is now true of Go, since
`NewServer`'s pre makes `cfg.Logger` a zap logger.

Axioms (premise today):
- `lease.NewLessor` (`⌜lg ≠ null⌝`) -> `lessorCfg`/`lessorInv` must record it for #10, #11 (and the
  proved `Grant`, `Checkpoint`, which call #10).
- `auth.NewAuthStore` (`⌜lg ≠ null⌝`) -> `authInv`'s `lg` fact (`InvAuth.lean:1217`) for #16.
- `storage.OpenBackend` (`openPre`'s `cfg.Logger' ≠ null`) and `backend.newBoltLoggerZap`
  (`cfg.Logger' ≠ null`): the predicate on `cfg.Logger`.
- `zap.NewNop` (the base producer; `zap-zero.md`).

Proved specs that constrain the logger only by `≠ null` (or not at all) and hand it to a family axiom
(each must be strengthened):
- `etcdserver.NewServer` (`cfg.Logger' ≠ null`, `Spec/.../etcdserver/NewServer.lean:172`): passes it to
  `NewLessor`, `NewAuthStore`, `NewBackendQuota` (through `newQuotaApplierV3`, `v3rpc.newBackendQuota`,
  `NewQuotaKVServer`/`NewQuotaLeaseServer`: `srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝`), `monitorFileDescriptor`
  (from `EtcdServer.Start`), `apply.Apply` (`⌜lg ≠ null⌝`) -> #2, #3; and the server's invariants
  (`srvLgAddr s ↦□ v.lg ∗ ⌜v.lg ≠ null⌝` in `InvStart.lean:84,135`, `InvBuild.lean:247,269`,
  `InvRead.lean:130`, `InvApplier.lean:628`, `InvApplyAll.lean:138`, `InvNet.lean:45`,
  `InvGoAttach.lean:131`), which #22-27 need in their premises (`isServerReqM` does not mention `s.lg`).
- `v3rpc.newLogUnaryInterceptor` (`⌜lg ≠ null⌝`) -> #4.
- `auth.NewTokenProvider` (`⌜lg ≠ null⌝`) -> #6.
- `mvcc.NewHashStorage` (`⌜lg ≠ null⌝`) -> `hashStorageOk` (`HashDefs.lean:39`) -> #14.
- `traceutil.newTrace`/`EnsureTrace` (no premise on `lg`) -> `ownTrace` -> #15 (via `LogIfLong`,
  `LogAllStepsIfLong`, proved).
- `rafthttp.Transport.Start` (`tv.Logger' ≠ null`) -> `Transport.AddPeer` -> #7.
- `backend.New`/`newBackend` (`isBackend`'s `lg ≠ null`, `InvBackend.lean:1257`, `InvBatch.lean:48,81`,
  `BeginCtx.lean:34`, `HooksLoeb.lean:42`) -> #13, #19.
- `clientv3.New`/`newClient` (`clientCfgOk`'s `cfg.Logger' ≠ null`, `InvClientNew.lean:205`;
  `isClientLogger`, `InvClient.lean:46`, whose invariant `WithLogger` may also update) -> #20, #21.
- `bootOk` (assumed, not proved): `isSnapshotter` (#17), `isRaftCluster` (#18), raft's `isLogger lok`.
- The examples' entry specs (`lg ≠ null` / `cfg.Logger' ≠ null`: `examples/lib/etcdstart/*`,
  `examples/lib/cluster3/*`, `examples/etcd/{restart,auth,partition,leasecatchup}/*`): the adequacy
  premises the predicate finally lands in.
