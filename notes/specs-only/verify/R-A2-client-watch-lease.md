# Re-review A2 (client watch 1b; client lease, lifecycle, auth, cluster, maintenance, interceptors 1c)

Reviewer: independent re-review (2026-11-09), worktree `specs-only` at `4a6a9b6b6e`. The specs are those
of `974e05095b`; `4a6a9b6b6e` adds only notes. I diffed against `1aa6fc1337`. Brief:
`reverify-brief.md`. I wrote the verdict on each finding before reading `repair-client-watch.md` and
`repair-client-core.md`. I read them afterwards only to check that N1 is not already addressed. It is
not.

Go sources: `.lake/src/{client,server}` (the pinned fork `a4d2bb17`). Snippets vetted: `go vet
./specreq/{clientv3watch,clientv3lease,clientv3client}/` passes. I reproduced the new issue's test at the pin
(below), in a temporary module outside the repository.

## Verdicts

| batch | verdict |
|---|---|
| **1b** (watch) | **PASS WITH OPEN DECISIONS**: C4 (readiness through a ghost client), C8 (`ctxStreamKey_prin` constrains every `ctxPrin` introduction), C9 (compaction affects only exactness; with A17); the earlier 1.1, 1.2, 1.5 stand. |
| **1c** (lease, lifecycle, auth, cluster, maintenance, interceptors, kubernetes, credentials, internal, client/pkg) | **FAIL**: one new first-tier finding, **N1**: the per-member `TimeToLive` fact is false of the code. Everything else passes, with open decisions C1 (resolver race: auto-sync and `Sync` out of scope), C4, C5 (`via` threaded through the wire contract) and the recorded 1.5 (`ReqRefusedPrincipals`' second half). |

## The original first-tier findings

| # | finding | status | evidence at HEAD |
|---|---|---|---|
| W1 | `wireStep` did not bind the first fragment's header and compaction revision | **resolved** | `ApiWatch.lean:348` `WireSt.frag : Option (WireWatchRespM × List EventM)`. `:396-398`: each later message agrees with the first on `watchId`, `hdr`, `compactRev` and `cancelReason`, and is neither created nor canceled. `:402` keeps the first. `toResp` (`:335-337`) reads exactly these fields, so `m.toResp evs = first.toResp evs`. That matches `watch.go:596-603`, where `cur` is the first message with the events appended, and `sendFragments` copies the fields (`v3rpc/watch.go:634-643`). `run`'s sketch states the step. |
| W2 | joining a stream by key gave no principal fact | **resolved; open decision C8** | `ctxStreamKey` and `ctxStreamKey_prin` (`ApiWatch.lean:448-455`, `:594-608`). `streamKeyFromCtx.spec` gives `ctxStreamKey ctx k` (`streamKeyFromCtx.lean:46-51`). The watcher's lock invariant maps each key to a stream with its opener's `ctxStreamKey ∗ ctxPrin` (`watcher__Watch.lean:32-37`). `printMD_inj` (`Spec/fmt/Api.lean:68`) and `outMD_agree` (`grpc/Api.lean:776`) give the realization. See the second-tier notes S-b and S-c. |
| W3 | the watch chain had no readiness | **resolved; C4** | `watcherHandle w c γ who`. `watcherHandle_watcherAt` takes `clientReady c` (`ApiWatch.lean:590-592`). `NewWatchClient.spec` returns `□ (clientReady c -∗ remoteWatchAt …)` (`etcdserverpb/NewWatchClient.lean`). `NewWatchFromWatchClient` takes the gated stub at a ghost `rc`. `watcher.Watch`, `RequestProgress` and `newWatcherGRPCStream` take `clientReady c`. `Close` does not take it, and it opens no stream. |
| W4 | `watchStep`'s ended branch left `created` free | **resolved** | `ApiWatch.lean:304` adds `m.created = false`. True of the code: every `closeErr` response is `WatchResponse{Header: &pb.ResponseHeader{}, Canceled: true, closeErr: …}`, with `Created` unset. `ReqWatchCreatedFirst` closes. |
| L1 | `NewLease` could not use `NewLeaseFromLeaseClient` | **resolved; C4** | `NewLeaseFromLeaseClient.lean:57-67` takes `cr = c ∨ cr = null`, `□ (clientReady cr -∗ remoteLeaseAt …)` and `□ (∀ ep, clientVia cr ep -∗ remoteVia remote ep)`, and returns `lessorHandle l cr`. `NewLease` passes `cr = c`, using `retryLeaseHandle_remoteLeaseAt` and `retryLeaseHandle_remoteVia` (`ApiLease.lean:413-421`). The in-process client passes `null`, where `epsTok_null` makes the `via` premise vacuous. |
| L2 | the per-member lease clauses had no source | **resolved for `Grant` and `Leases`; C5. For `TimeToLive` the clause now has a source, but it is false: N1** | `viaPre`/`viaFact` (`ApiClient.lean:404-430`) are threaded through `AttemptTriple`, `uiOk_call`, `RemoteCallTriple`'s `V`, `retryLeaseClient.*` (`V = clientVia c`), `remoteLeaseAt_call` (`V = remoteVia v`) and `LeaseRead.Triple` (`ApiLease.lean:250-259`). 2a's `leaseFact` is the server side. |
| F1 | `kubernetes.New` dropped the endpoints token | **resolved** (S-a: a smaller gap is left) | `kubernetes/New.lean:52-53` gives `∃ eps, cfg.Endpoints' ↦*□ eps ∗ epsTok c 1 eps`. The new snippet `ReqKubeStatus` closes, because it built the slice `[ep]`. |
| F2 | `dialOptsOk` had only a `nil` introduction | **resolved** (the proxy's replacing interceptors are excluded: untranslated, stated) | `dialOptsOk_neutral` (`ApiClient.lean:780-782`). 2a's `WithChainUnaryInterceptor`, `WithChainStreamInterceptor`, `WithStatsHandler` and `WithContextDialer` specs each give `dialOptAt v id` under `cliIcPass`/`cliSicPass`/`statsOk`/`ctxDialerOk`. Snippet `specreq/grpc/dialopts.go` (`ReqKubeDialOpts`). |
| F3 | `NewKVFromKVClient` needed `clientConnOk` | **resolved** | Now takes `⌜c = null⌝ ∨ ∃ who', clientBase c who'` (`NewKVFromKVClient.lean:45`). `clientBase`'s realization lists `callOpts` (`ApiClient.lean` header). `ReqInProcClient` closes. |
| F4 | `(*types.ID).String` had no spec | **resolved** | `types/ID__String_ptr.lean` at any fraction, points-to kept, `idStr x`. The pointer forms `URLs.Len_ptr` and `URLs.StringSlice_ptr` were also added (old S4). The rafthttp, membership and etcdserver sketches cite them (`streamReader__dial.lean:6`, `checkClusterCompatibilityFromHeader.lean:6`, ...). |

The second-tier items of the two reports:
- Provability:
  - S1 (the tie's history facts) is stated in `WatchInternal.lean:61-71`.
  - S2 (range membership unconditional) is resolved, C9: `ApiWatch.lean:322-323`. This is sound against the model: `KVHist` keeps every revision's events, and compaction only sets `compacted`.
  - S3 (`clientReady`'s realization) is written in the `ApiClient.lean` header.
  - S4 (resolver) became the issue below.
  - S5 is resolved (`lessor__Close.lean:43`).
- Completeness:
  - S2 (the `ActiveConnection` Users line) is fixed.
  - S7 (interceptor order) is written into `dialOptsOk`'s doc.
  - S1, S3 and S6 are unchanged and were second-tier.

## New first-tier finding

### N1. `lessor.TimeToLive` through a follower promises the follower's lessor view, but a follower forwards `TimeToLive` to the leader

- **Files**:
  - `ApiClient.lean:417-430` (`viaFact`, the `.leaseTimeToLive` case: `∃ j, i ≤ j ∧ σ.leaseAnsAt j rq res ∗ leaseViewLb γ ep j`);
  - `ApiLease.lean:250-259` (`LeaseRead.Triple`), which `lessor.TimeToLive.spec` and `Client.TimeToLive` use;
  - 2a's `leaseFact` (`server/.../v3rpc/Api.lean:325-335`), the claimed source.
- **The code**: `EtcdServer.leaseTimeToLive` (`server/etcdserver/v3_server.go:636-669`) answers from
  its own lessor only `if s.isLeader()`. Otherwise it forwards the request to the leader
  (`:671-676`, `waitLeader`, `leasehttp.TimeToLiveHTTP`) and returns the leader's answer. `LeaseLeases`
  (`:737-738`) answers from the member's own lessor, `s.lessor.Leases()`. W0's own description of
  `leaseViewLb` (`api/v3/State.lean:181-185`) says a member "answers its lease reads (`Leases`;
  `TimeToLive` on the leader)".
- **Why it is false**: through a follower `F` (a client frozen at `F`'s endpoint, `clientVia c F`), a
  `TimeToLive` answer comes from the leader's table `j_L`. The spec turns it into `leaseViewLb γ F
  j_L`. `F` may not have applied that far, because followers apply after the leader. A later `Leases`
  through `F` is then claimed to answer at a table `≥ j_L`, but it answers from `F`'s own, older
  table. Concretely: another client grants lease `G` through the leader. A client frozen at the
  lagging follower `F` polls `TimeToLive(G)` until it finds `G`, then calls `Leases` and panics if
  `G` is missing. With no revocation and no expiry, the specs prove this program panic-free (the tables
  only grow from `j_L`). In a real cluster `F`'s `Leases` can still miss `G`. Even the weaker `i ≤ j`
  is doubtful: a newly elected leader whose commit index lags, or a deposed leader that still answers
  (`batch-W0.md:133`), can answer from a table older than `F`'s `i`. I found this by code reading and
  wrote no Go test. It is a spec bug, not a Go bug (the forwarding is etcd's design), so it belongs in
  `notes/`, not `issues/`.
- **Callers affected**:
  - `ReqGoneNotListed` (`specreq/clientv3lease/member.go`), whose proof uses `TimeToLive`'s view,
    then `Leases`;
  - any per-member lease user (the `leaseexpiry` example is single-member, so it is unaffected).

  Recorded decision A4 ("`Leases`/`TimeToLive` answer from a table the member has reached") states
  the same false premise, so the decision as the user approved it rests on a wrong picture
  (PRINCIPLES, "Explain a finding in plain terms").
- **Suggested fix**:
  - In `viaFact` and 2a's `leaseFact`, give nothing for `.leaseTimeToLive`. At most give
    `∃ j, σ.leaseAnsAt j rq res`, which `kvStep` already gives, with neither `i ≤ j` nor `leaseViewLb γ ep j`.
  - Keep the per-member clause for `Grant` (answered after the member applies it locally) and for
    `Leases` (the member's own lessor).
  - Restate `ReqGoneNotListed`, for example on a single-member cluster, or with `Leases` alone.
  - Correct A4's text in `open-questions.md`.

## Regressions (files changed since `1aa6fc1337`)

About 39 spec files of this area changed:
- watch: 11 files;
- lease: 13 files;
- client, kubernetes, credentials and types: 15 files, plus W0's shared `Api.lean` (its `ctxPrin` doc and `init.spec`).

I also checked 3h's `NewWatchClient`/`NewLeaseClient`. Each still closes from its callees as they
are now, except N1. Specifically:

- **Watch.**
  - `watcher.Watch`: `OpWatch`, `streamKeyFromCtx` (`ctxStreamKey`), `mu`, and the map's invariant per key; a
    joined stream is at `p` by `ctxStreamKey_prin` (the same `who` on both sides);
    `newWatcherGRPCStream` with `clientReady c`.
  - `RequestProgress` and `closeStream`: close.
  - `wgsAt` keeps `∃ c who', watcherHandle w c γ who'` for the teardown.
  - `run`'s fragment case: closes (W1).
  - `watchStep`'s new unconditional event clause: true. `KVHist.eventsAt` (`Model.lean:174`) is never
    erased by compaction, and mvcc reads only records of real revisions.
- **Lease.**
  - `lessor.Close` without readiness: true (`Close` only cancels and waits).
  - `lessor.KeepAlive`: `LeaseResponseChSize` from `init.spec` (`16`, read-only). No program in scope
    writes the variable; I grepped etcd, the examples and Kubernetes.
  - `keepAliveCtxCloser`: the `==` on `&ctx` values is comparable.
  - `Grant`, `Leases`: close through `viaPre`/`viaFact`.
- **Client.**
  - `New`/`newClient` give `epsTok c 1 eps` unconditionally. That is sound only because `cfgOk` now
    forces `AutoSyncInterval = 0`, which it does (`ApiClient.lean:263`).
  - `autoSync` only at `0`; `Sync`/`SetEndpoints` take the exclusive `resolverIdle`, which no caller
    after `New` holds (C1).
  - `New`'s `ErrNoAvailableEndpoints ↦□ err` matches `client.go:87-88`.
  - `init.spec`'s sentinels: plausible.
  - `connOk_unfold` (credentials): plausible as 2a's realization.

  No way to prove `False` found: the new laws `ctxStreamKey_prin`, `epsTok_null`, `clientVia_conn`,
  `retryLeaseHandle_remoteVia`, `dialOptsOk_neutral` and `compactOptAt_rev` are each realizable as
  stated (modulo S-b and S-c).

## Snippets

| snippet | result |
|---|---|
| `ReqWatchCreatedFirst` (changed comment) | ✓ (W4) |
| `ReqWatchRewrite` (assumption dropped) | ✓: the unconditional clause gives the key in the prefix range, so `Key[len(pfx):]` cannot panic |
| `ReqWatchSharedStream` (new) | ✓: `WithRequireLeader.spec` keeps `ctxPrin`; `Client.Watch.spec` per call; the sharing is internal (`ctxStreamKey_prin`) |
| `ReqWatcherClose` (comment) | ✓ |
| `ReqKubeStatus` (new) | ✓: `eps = [ep]` from the snippet's own slice and `↦*□` agreement; see S-a |
| `ReqNewWrapClose` (cites `kvAt_intro`) | ✓ |
| `ReqSync` (removed) | consistent with C1 |
| `ReqGoneNotListed` (unchanged) | provable from the specs as stated, but rests on N1's false clause (it uses `TimeToLive`'s view) |
| the other 40 of the area's snippets | unchanged, and their specs did not move against them; ✓ as in the round's reports (`ReqRefusedPrincipals`' second half waits on 1.5) |

The completeness patterns the round listed are covered:
- Kubernetes `Status` on a `kubernetes.New` client: `ReqKubeStatus`;
- Kubernetes' dial options: `ReqKubeDialOpts`, in `specreq/grpc`;
- the in-process KV: `ReqInProcClient`;
- shared streams: `ReqWatchSharedStream`.

## The new issue `issues/etcd-client-resolver-build-race.md`

- **True**: `go test -race` of its `resolver_build_race_test.go`, at the pin with grpc v1.84.0, reports
  three races. They are between `EtcdManualResolver.Build` (`resolver.go:44,48`, on grpc's serializer
  goroutine) and `SetEndpoints` (`resolver.go:53-54,67`, under `client.go:182`). `Build` takes no lock
  that orders it with `epMu`. `etc/issues-status.py --check` passes.
- **How the specs exclude it** (C1):
  - `cfgOk` requires `AutoSyncInterval = 0`;
  - `autoSync.spec` covers only `0`;
  - `SetEndpoints` and `Sync` take the exclusive `resolverIdle c`, which `newClient` holds only for its
    own `SetEndpoints`, before `dialWithBalancer` (`client.go:444-448`), and gives to no caller;
  - `Client.Dial(ep)` (`Status`) builds a fresh resolver no one updates.

  Kubernetes and the examples never set auto-sync or call `SetEndpoints`; I grepped both. The
  exclusion is sound. Its cost is that `Client.Sync.spec` has no caller that can meet its pre, which C1
  records.
- **Small staleness**: the issue's "Proof" section still says the specs "should exclude a concurrent
  channel wake-up" and points to the repair request, rather than naming `resolverIdle`/C1 as done.

## Second-tier notes (new)

- **S-a. `kubernetes.New`'s post has no "endpoints non-empty" fact.** `New.spec`'s post has the
  disjunction `len ≠ 0 ∨ …`; `kubernetes.New.spec`'s does not. `Maint.StatusTriple` needs `eps ≠ []`.
  A caller that does not know its config slice (Kubernetes' feature checker) cannot get it. The
  snippet can. Fix: copy `New`'s conjunct.
- **S-b. `fmt`'s boundary lacks `printMD md ≠ ""`.** `ctxStreamKey`'s realization maps "no
  metadata" to `""`. `ctxStreamKey_prin` then needs that no printed map is `""`, which is true of Go
  (`map[…]`) but not stated next to `printMD_inj`.
- **S-c (uncertain, W0's).** `ctxPrin` has no cluster index, and `ctxPrin_token` drops the `γ` of
  `tokenUser γ tok u`. `ctxStreamKey_prin`'s realization then needs one user per token across
  clusters. `tokenUser_agree` is per `γ`, and simple tokens are random strings. Harmless for one
  cluster per program; say so, or index `ctxPrin` by `γ`.
- **S-d. Stale text in `New.lean`.** Its Changes section still says "auto-sync with verification off"
  and "`cfgOk`'s dial options may replace the client's interceptor (the gRPC proxy)". Both now
  contradict `cfgOk`/`dialOptsOk`.
- **S-e. `newClient.lean`'s sketch does not say where `resolverIdle c` comes from** for its
  `SetEndpoints`. It is minted with the resolver before dialing, as `ApiClient.lean` says.

## Counts

- **Original first-tier findings**: 10 (W1-W4, L1, L2, F1-F4).
  - 9 resolved;
  - L2 resolved for `Grant` and `Leases`, with N1 open for `TimeToLive`;
  - open decisions involved: C1, C4, C5, C8, C9.
- **New first-tier findings**: 1 (N1).
- **Changed spec files re-checked**: about 39 of this area, plus 3h's `NewWatchClient`/`NewLeaseClient`
  and W0's shared `Api.lean` changes. All close except `lessor.TimeToLive`, `Client.TimeToLive` and
  `retryLeaseClient.LeaseTimeToLive` (N1's clause).
- **New or changed laws checked**: 12. None vacuous; none false except the `TimeToLive` case of
  `viaFact`.
- **Snippets**: 8 changed, added or removed, checked. 7 close; `ReqGoneNotListed` rests on N1. The
  remaining 40 were unaffected.
- **Go bugs**: no new bug. The resolver race is confirmed and correctly filed in `issues/`.
