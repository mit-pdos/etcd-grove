# A6-grpc-boundary: provability (verification round, 2026-11-09)

Reviewer: independent provability reviewer, with the `axiom` skill's mindset on the trust
boundaries (grpc, protobuf's `proto`, `metadata`/`status`/`peer`, net/http). Commit under review:
`1aa6fc1337` (HEAD of `specs-only`). Read-only except this file.

Area: `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/` (115 files: 2a and 2b),
`Spec/google_golang_org/` (61: grpc, its `status`/`metadata`/`peer`/`health`/`credentials`,
protobuf's `proto`), `Spec/go_etcd_io/etcd/api/v3/{etcdserverpb (85), v3rpc/rpctypes, version}`,
`v3lockpb`/`v3electionpb` `Api.lean`, `Spec/net/http/` (16); snippets
`examples/specreq/{v3rpc,grpc,v3rpcwatch,etcdserverpb}/` (31 REQs). Chain checked: the client's
remote contracts (`client/v3/Api.lean` `RemoteKV.*Triple`, `ApiClient.lean` `RemoteCallTriple`,
`AttemptTriple`, `uiOk_call`) → grpc (`ClientConn.Invoke`, `attemptOk_call`) → `etcdContract`
(`etcdUnary`) → generated handlers (`_KV_*_Handler`) → interceptors (`icEtcdOk`) → handlers
(`HandlerTriple`) → 2c's `SrvCallTriple` (`ApiReq.lean`).

The authors' notes were read only after the findings below were written, to mark recorded ones.

## Verdicts

| Batch (in this area) | Verdict |
|---|---|
| **2a** (v3rpc but `watch.go`; grpc, proto, rpctypes boundaries) | **FAIL** (F1, F3, F4, F5, F6, F7, F8, F10; F9 an open decision) |
| **2b** (v3rpc `watch.go`, `ApiWatch.lean`) | **PASS WITH OPEN DECISIONS** (3.8 wire-request scope, 7.3 Goose `default:` binding, A9/I3 reader tokens), sampled; its registration inherits 2a's F4/F9 |
| **3h** (etcdserverpb, v3lockpb, v3electionpb, version) | **FAIL** (F2, F6, F7, F8's field law; F9 = open 7.4) |
| 2f's net/http (in this area by path) | PASS (lightly checked: no first-tier finding) |

Counts: spec files checked 304 (every function triple read; proof plans in batches below), laws
checked ~210 (all of grpc's, proto's, rpctypes', v3rpc's, ApiWatch's, etcdserverpb's and
Realize's; net/http's by reading their statements). Snippets checked 31: 23 close, 4 fail on their
own text (F10), 4 rest on a spec that does not close (F1/F4/F7/F9). Users: not this kind's task.

## First-tier findings

### F1. `LeaseServer.*` and `maintenanceServer.Alarm`: `hdr.fill` on a header the specs allow to be `nil`

- **Step that does not close.** `LeaseServer.LeaseGrant`, `LeaseRevoke`, `LeaseTimeToLive`,
  `LeaseLeases` (and `quotaLeaseServer.*` over them), `maintenanceServer.Alarm` call
  `hdr.fill(resp.Header)` on the reply 2c returned (`lease.go:45-90`, `maintenance.go:266`);
  `fill` panics on a `nil` header (`header.go:51-53`, `panic("unexpected nil resp.Header")`), and
  `header.fill.spec` needs `respHeaderOwn rh` (non-nil). The reply comes from 2c's
  `SrvCallTriple … ClientV3.ansReply` (`EtcdServer__LeaseGrant.lean`, `EtcdServer__Alarm.lean`
  via `reqReply … = ansReply`), whose success is `replyOwn resp b`; 3h's `replyOwn_lease`
  (`Realize.lean:80`) and `leaseResp_header` (`etcdserverpb/Api.lean:817`) give the header as
  `optOwn respHeaderOwn h dq ho` ("some, possibly `nil`"), and `bodyHolds` says "the header's
  fields any". So the handler cannot exclude the panic.
- **Callers affected:** every lease RPC and the client's `AlarmList`/`AlarmDisarm` through the
  member (W0/1c's `RemoteCallTriple` at those methods); snippet `v3rpc/lease-ttl-unknown`'s success
  path.
- **Fix.** Either 2c's lease and alarm specs return a reply with a non-nil header (the code builds
  one: `newHeader()` in the apply), e.g. `ansReplyH res resp err := ansReply … ∗ (∃ h m,
  hdr field ↦ h ∗ respHeaderOwn h (own 1) m)`, or `replyOwn` at the lease/alarm bodies says the
  header is set (a W0/3h law `replyOwn_lease_hdr : replyOwn p b ⊢ … respHeaderOwn h …` for the
  server-built replies). Not recorded.

### F2. `endsDecoded`/`decodedAt`: persistent facts about mutable fields make the laws inconsistent (3h, 2a)

- **The claim.** `endsDecoded t p` is persistent (`endsDecoded_persistent`) and keyed by the
  address only; `endsDecoded_range` (`etcdserverpb/Api.lean:409-412`) reads the *current* field:
  `endsDecoded RangeRequest p ∗ p.RangeEnd ↦{dq} es ∗ es ↦*□ ebs ⊢ … ⌜es = nil ∨ ebs ≠ []⌝`.
  `endsDecoded_range_intro` (`:398-402`) creates it from a field that is `nil` now. The same holds
  of `Proto.decodedAt` (persistent, `Unmarshal.spec`'s post) through `endsDecoded_of_decoded`.
- **Counterexample (sketched to the level the skill asks; not built):**
  ```go
  r := &pb.RangeRequest{Key: []byte("a")} // RangeEnd nil
  r.RangeEnd = make([]byte, 0, 1)         // non-nil, empty
  if r.RangeEnd != nil && len(r.RangeEnd) == 0 { panic("x") } // Go panics
  ```
  Proof: after the allocation, `r.RangeEnd ↦ slice.nil`; `endsDecoded_range_intro` gives
  `endsDecoded RangeRequest r` (persistent); the store writes `r.RangeEnd ↦ es'` with `es'` of
  capacity 1 (≠ `slice.nil`) and `es' ↦* []`; `endsDecoded_range` then gives `⌜es' = nil ∨ [] ≠
  []⌝`, i.e. `False`, so the `panic` branch is dead in the proof. Only 3h's laws are used.
- **Recorded?** A14 records the *scope choice* ("a scope fact: a holder that rewrites a `bytes`
  field may not use it", `Proto/Api.lean` header), but the formal statement is not a scope
  restriction, it is a false universal (PRINCIPLES' second hard rule). Counts as first-tier.
- **Fix.** Tie the fact to the value, not the address: e.g. `endsDecoded_range` as `endsDecodedAt p
  es` (the slice value the decoder stored) so a rewrite to `es'` yields nothing; or carry the
  nil/empty distinction in the model (`rangeReqOwn`'s unfold records `es = nil ↔ endNil` with a
  model field), and make `decOk_call`/`Unmarshal` give the pure model fact. Also drop
  `endsDecoded_range_intro`'s persistence (it should give the fact for the value `es` only).

### F3. grpc `metadata`: `FromOutgoingContext` gives `mdAt` of a `nil` map, `MD.Set` writes it without a premise (2a trust boundary)

- **Evidence.** `FromOutgoingContext.spec` (`metadata/FromOutgoingContext.lean`) returns `mdAt m
  (own 1) md ∗ ⌜ok = false → md = []⌝` on every path; grpc-go v1.84 returns `nil, false` when the
  context has no outgoing metadata (`metadata/metadata.go:331-335`). `MD.Set.spec` takes `mdAt m
  (own 1) md` and no `m ≠ null`; Go's `md[k] = vals` on a `nil` map panics
  (`metadata.go:189-195`).
- **Counterexample (sketched):**
  ```go
  md, _ := metadata.FromOutgoingContext(context.Background())
  md.Set("k", "v") // panic: assignment to entry in nil map
  ```
  Proof: `Context.ctxOk` of `Background()` (Perennial), `outMD_ctxOk` gives some `md`, then the two
  specs; no other axiom.
- **Callers.** etcd's own callers copy before writing (`WithRequireLeader`: `md.Copy()` only when
  `ok`), and the snippet `grpc/metadata-out` copies first, so nothing in etcd's proof is wrong yet;
  the boundary is.
- **Fix.** `FromOutgoingContext`'s post: `(⌜ok = true⌝ ∗ mdAt m (own 1) md) ∨ ⌜ok = false ∧ m =
  null ∧ md = []⌝`, and `Copy`/`Get` accept `m = null` (a separate read-only conjunct), or a law
  `mdAt m (own 1) md ⊢ ⌜m ≠ null⌝` with the nil case outside `mdAt`. Not recorded.

### F4. `newLogUnaryInterceptor` cannot meet `icEtcdOk`: the request is gone when it logs (2a)

- **Step.** The log interceptor calls the handler, then (deferred) `logUnaryRequestStats(…, req,
  resp)` (`interceptor.go:83-93`), which calls `proto.Size(_req)`/`_req.String()`;
  `logUnaryRequestStats.spec` needs `msgAt reqT q dq c` of the request. `icEtcdOk`'s continuation
  (`v3rpc/Api.lean:493-496`) and `HandlerTriple` (`:668-675`) take `msgAt reqT q (own 1) c` and give
  back only `threadTok ∗ T ∗ unaryOut …`: after the handler the interceptor holds no share of the
  request (it cannot keep one: the continuation wants `own 1`). With a non-nil logger (`s.Logger()`,
  always set by 2e) the deferred call is reached.
- **Consequence.** `newLogUnaryInterceptor.spec` does not close, hence `Server.spec` (every chained
  interceptor `icEtcdOk`) does not either, and `Grpc.start.spec`'s `regsOk` has no source.
- **Fix.** Return the request: `HandlerTriple`'s post and `icEtcdOk`'s continuation post gain `∃ c',
  msgAt reqT q (own 1) c' ∗ ⌜depth c' < depthMax⌝` (the content may change: 2c's `LeaseGrant`
  writes the ID, `EtcdServer.LeaseGrant`'s `B`); every handler gives it back (2c's `SrvCallTriple`
  `B`s already return the request). Not recorded.

### F5. `kvServer.Compact`: `AuthAdmin.isPermitted`'s post cannot justify W0's admin-denial answer (2a)

- **Step.** On a denial (`ErrPermissionDenied`, `ErrUserNotFound`: definite, not refusals, not
  token refusals) the handler must take the contract's first way and fire the caller's exclusive
  update with W0's compact denial `∃ a ∈ σ.authTables, ¬ a.admin who ∧ σ' = σ ∧ res = .err
  (a.adminErr who)` (`Model.lean:1019-1022`). `AuthAdmin.isPermitted.spec`'s post is only `⌜err =
  nil ∨ ∃ e ∈ [userEmpty, userNotFound, permissionDenied, invalidAuthToken], srvErrOf err e⌝`: no
  auth table the cluster has had, no `¬ a.admin who`, no `e = a.adminErr who`. The third way needs
  `indefMsg`, false for these descriptions.
- **Also:** the sketch of `kvServer__Compact.lean` is stale ("W0's `kvStep` for `.compact` has no
  such answer"): W0 now has it.
- **Fix.** `isPermitted`'s post on an error: `∃ σ a, etcdLb γ σ ∗ ⌜a ∈ σ.authTables ∧ ¬ a.admin who
  ∧ srvErrOf err (a.adminErr who)⌝` (or the token refusals), from 3d's `IsAdminPermitted` at the
  member's applied auth state. Not recorded.

### F6. Reply depth: missing laws, and a transaction reply can reach `depthMax` (3h, 2a)

- **Step.** `Grpc.unaryOut` (success) needs `⌜depth c < depthMax⌝` of the reply's content.
  `holds_depth.spec` (`etcdserverpb/Api.lean:258-263`) bounds `rangeRespHolds`, `bodyHolds`,
  `chunkHolds`, `compareHolds`, non-transaction `reqHolds`, but not `putRespHolds`,
  `deleteRespHolds`, `compactRespHolds`, `txnRespHolds`: `kvServer.Put`, `DeleteRange`, `Compact`,
  `Txn` (and the quota wrappers) cannot discharge it.
- **Txn is worse.** A reply nests one level deeper than its request (its innermost `RangeResponse`
  holds `KeyValue`s where the request's `RangeRequest` is a leaf). With `checkTxnRequest` at
  `--max-txn-ops = maxTxnOpsMax = 4999`, `L = 4999` nested levels each with one operation are
  accepted (`opCheck`, `v3rpc/Api.lean`); the request's depth is `2L+1 = 9999` (what
  `txnCheck_checked` bounds), the reply's `2L+2 = 10000`, which is not `< depthMax`. So under
  `kvServer.Txn.spec`'s own pre (`kvServerAt`: `maxTxnOps ≤ maxTxnOpsMax`) its post is unprovable
  at that request. (protobuf-go would still decode depth 10000; the spec's strict bound is the
  problem, not the code.)
- **Fix.** Add the depth laws (≤ 2 for the flat replies; for `txnRespHolds`, `depth ≤ txnMsgDepth t
  + 1` or a bound from the request), and lower `maxTxnOpsMax` to `4998` or make `unaryOut`'s bound
  `≤ depthMax` (which `Unmarshal`'s limit actually admits). Not recorded.

### F7. The client → grpc leg does not compose: unrealized slots, and `reqRight` not carried by an attempt

- **Slots without laws.** The client's `connOk` (`client/v3/Api.lean:466`), `unaryArgs`,
  `grpcConnAt`, `grpcCallOptsOk` (`ApiClient.lean:406-414`, "slot, 2a/3h") have **no law** relating
  them to `Grpc.connAt`, `attemptOk`, `callOptOk`, `Proto.msgAt`/`reqModels`. Hence
  `Client.dial.spec` cannot introduce `connOk` from `NewClient.spec`'s `connAt`, and 3h's
  `NewKVClient.spec` (`connOk ⊢ remoteKVAt`), `NewLeaseClient`, `NewAuthClient`, `NewWatchClient`
  cannot eliminate it; `AttemptTriple` cannot be derived from `attemptOk_call` (its `unaryArgs`
  must yield the request's `msgAt`/`reqModels`, the reply holder, the compaction's `r ≠ 0` that
  `etcdUnary` takes, and `R`'s reply facts). Recorded by 3h as "second tier 6, not done"
  (`batch-3h.md`); not an open question; still first-tier for the chain.
- **`reqRight` (MemberAdd/MemberUpdate).** `etcdUnary` takes `reqRight γ rq` (`urlsRight γ urls`,
  single-use) and its second way (token or learner refusal, the update given back) does **not**
  give it back; `AttemptTriple`'s pre has no `reqRight`, and `unaryArgs` cannot hold it (it is
  returned on every error outcome). So `AttemptTriple` is unprovable at those methods, and 1c's
  interceptor, which re-sends after a token refusal, would need the right twice.
  Fix: `etcdUnary`'s second way and `AttemptTriple`'s unfired outcome give `reqRight` back (the
  member did not propose), and `AttemptTriple`/`uiOk_call` carry it in the pre.
- **Fix (slots).** Laws, e.g. `connOk_elim : connOk conn γ who ⊢ ∃ A ui si, connAt conn A (some
  ui) (some si) (Credentials.credMD γ who) ∗ uiOk ui … ∗ siOk si … ∗ □ (∀ ep, A ep -∗ servesAt γ
  ep)`, its introduction from `NewClient`'s post, and `unaryArgs_intro/elim` over `msgAt`,
  `reqModels`, the reply holder.

### F8. `headerFillingRangeStream.Send` and the range-stream records (2a, 3h)

- `Send` dereferences `resp.RangeResponse` and its `Header` (`key.go:84-89`); there is no unfold law
  for `msgAt RangeStreamResponse` / `chunkHolds` (3h states field laws for `RangeResponse` only),
  so the proof can neither read the field nor exclude a `nil` `RangeResponse` (a nil dereference),
  nor fold the filled header back into `msgAt … c'` with `chunkModels c' m'`.
- `rsChunk_hdr_last.spec` ("the chunk with a header is the last one sent") is not realizable
  against `rsSink_send.spec`, which records any chunk after any `ms` (no premise that no chunk of
  `ms` has a header). Fix: `rsSink_send`'s pre `⌜∀ m0 ∈ ms, m0.hdr = none⌝` (2c's `RangeStream`
  puts the header on its last chunk only), and a `chunkOwn_unfold` law in 3h.

### F9. `Server.spec`'s `regsOk` for untranslated handlers (open decision 7.4)

`otherDescs_init` gives the Cluster and Maintenance descriptors' handlers as an unknown `ms`,
`authDesc_init` all but six Auth handlers as `ms'`, `kvDesc_init` the `RangeStream` stream handler
as `ss`: `unaryOk`/`streamOk` of an unknown value is unprovable, so `Server.spec`'s post (`regsOk B
(etcdContract γ ep) …` for every registration) does not close, nor `start.spec` downstream. The
`ClusterServer` replies are untranslated structs too. Recorded as open question 7.4 ("Translate
them?"): counts as PASS WITH OPEN DECISION for that part.

### F10. Snippets that are not provable as written

- `v3rpc/kv.go` `ReqValidationAnswer`: `refusalOrIndefinite` accepts only `NoSpace`,
  `TooManyRequests`, `RequestTooLarge`, the learner's description, and the mapped indefinite
  `NoLeader`, `Timeout`, `Stopped`, `LeaderChanged`, `TimeoutDueTo{LeaderFail,ConnectionLost}`,
  `NotCapable`. The contract admits more: the first way may fire any `EtcdErr.refusal` with
  `firedAns` (`.corrupt`, `.authFailed`, `.memberNotEnoughStarted`, `.memberLearnerNotReady`,
  `.unhealthy`: `Model.lean:373-377`), and the third way any `indefMsg` status, including the mapped
  indefinite `.notLeader`, `.unhealthy`, `.clusterIdMismatch`, `.clusterVersionUnavailable`,
  `.badLeaderTransferee` (`Model.lean:358-366`), which `rpctypes.Error` turns into `EtcdError`s the
  helper rejects: the snippet's `panic` is reachable under the specs. Fix the helper (all refusals,
  all mapped indefinite errors).
- `v3rpc/kv.go` `ReqRangeStream`: `end[len(end)-1]++` panics for `prefix == ""`; add `Assumes:
  prefix non-empty` (or build the end with `clientv3.GetPrefixRangeEnd`).
- `v3rpcwatch/serve.go` `ReqServeWatch`: `RegisterWatchServer(gs, ws)` needs `srvBuild gs B` and the
  service not registered yet (`Server.RegisterService.spec`); `Assumes` says nothing of `gs`.
- `grpc/at-most-once`, `etcdserverpb/kv-stub`, `etcdserverpb/watch-stub`, `v3rpc/serve`,
  `v3rpc/put-then-range`, `v3rpc/lease-ttl-unknown`: their proofs go through F7 (connOk) or
  F1/F4/F9; they close once those do.

## Second-tier findings

- **grpc metadata order** (`Grpc.mdSeen`, `attemptOk_call`/`streamerOk_call`): the specs say the
  server sees `md0 ++ mdc` (context's metadata, then the credentials'); grpc-go sends the per-RPC
  credentials' first (`internal/transport/http2_client.go:628-637`: `authData`, `callAuthData`,
  then the outgoing `md`). With a key in both, `MD.get` order is wrong. Harmless for etcd (both
  tokens name the same user: `ctxPrin_tokenSame`), false of grpc. Fix: `mdSeen (mdc ++ md0) md`.
- **`Proto.Equal.spec`**: `b = true ↔ c = d`; protobuf-go's `Equal` is false on a NaN float field
  even for one message (`Equal(m, m)`), while `msgAt_agree` gives `c = c`. No etcd/raft message
  has a float field, so not exploitable here; restrict to types without floating fields or weaken to
  `b = true → c = d`.
- **`Unmarshal.spec`/`encodes`**: protobuf-go refuses invalid UTF-8 in proto3 strings; nothing
  says `encodes t c bs → marshalOk c`, so the error branch's "no shallow content encodes `bs`"
  is only true under that reading of the opaque `encodes`. State the law.
- **`decOk_call`** claims success unconditionally: true only for clients inside the program's
  `msgsFit` (a foreign client's too-deep transaction is refused by the decoder). It is the closed
  world the header states; say so at `decOk_call` and in `msgsFit`'s docstring.
- **`Grpc.start.spec`** consumes `Http.handlerPool pl n` for good (`GracefulStop` returns only the
  `T`s): a member restarted in the same program needs thread tokens again. Return the pool with
  `drainTok`.
- **`sicEtcdOk`** is opaque with no meaning law, yet `metricsOk_stream.spec` (assumed, grpc-
  prometheus) produces it: the assumption's content is undefined. State it transparently like
  `icEtcdOk` (over `Grpc.streamOk`'s run).
- **`icChain [] ic`**: the docstring says `ic` is then the nil function; no law says so, so
  `handlerBodyWP`'s direct branch is unreachable for a server without interceptors (not etcd's).
- **`LeaseServer.LeaseKeepAlive`**: besides the gate share (recorded 3.6), the leaked loop may call
  `stream.Send` after the run returned (`lease.go:100-110`), which `srvSend_send` permits; grpc-go
  documents `SendMsg` after the handler returns as unsupported. Uncertain whether it can panic in
  v1.84 (not verified).
- **`Grpc` header** lists a law `ownErr_sent` that is not stated (derivable from `ownErr_grpcMsg`
  and `statusErr_sent`).
- **Revision wrap**: `header.fill` replaces a `0` revision; `putReply`'s `W64 rev` is `0` at `rev =
  2^64`. Negligible (mvcc's revision is an `int64`).

## What is good

- **grpc's boundary** (`Grpc/Api.lean`): contents as values (no caller-built wire model), the urpc
  shape (`UnarySpec` carrying the caller's resource), at-most-once per attempt argued from grpc-go's
  transparent retry, own-error messages separated (`grpcMsg`, with rpctypes' `desc_not_grpcMsg`),
  the size workload premise on the connection's only producer, handler runs borrowing the caller's
  thread tokens, `drainTok` returning run resources: sound against everything tried except F3 and
  the order nit. No counted resource comes from nothing (`streamKey` only names ghost state;
  `start` consumes `n` tokens and `n` copies of `T`; `Peer` consumes the variable's points-to).
- **rpctypes' tables** are exact: a script compared `desc`, `code` and `mapped` with
  `api/v3rpc/rpctypes/error.go` (63 descriptions, 57 mapped, no mismatch); `desc_inj` holds.
- **The composition with 2c** (`etcdUnary` → `SrvCallTriple`) closes for the KV methods but F5/F6:
  the handler wraps its `Step who` update into one over `srvStep who tls` and fires the inner one
  through `srvStep_step` (fired answers) or aborts (non-fired answers are refusals with `σ' = σ`,
  W0's `Step`'s first disjunct); outcome 2's update is re-fired as `Step.refuse` or sent by the
  second way; the persistent read update lets `RangeStream` answer `ErrAuthOldRevision` by firing it
  itself.
- `togRPCError`, `ansOutcome`, `indefMsg` and 2c's `srvErrShape` line up (context errors via
  `ctxErr_sent` and `desc_not_grpcMsg`, ASCII descriptions via `fixUtf8_ascii`/`desc_ascii`).
- `GetProgressReportInterval`/`SetProgressReportInterval`: `progressIntervalOk` is exactly what
  `rand.Int63n(interval/10)` and the ticker need (`watch.go:101-118`).
- `txnCheck_checked`'s depth bound for the request is right (`2L+1 ≤ 9999`, plus the raft request's
  level); only the reply is off (F6).

## Proof plans (every spec, batched)

Notation: ✓ closes; ✗ does not (finding); ◐ closes modulo an open decision.

**2a handlers over 2c (`HandlerTriple`, run resource `srvGate s gq`).** Plan for each: decode
`reqModels` to the model request (3h's `*_msgAt`); the gRPC check (`check*Request.spec`, pure
`rangeCheck`/`deleteCheck`/`txnCheck`/`intervalsOk`): an error fired as the model's validation
answer at any state (`Step`'s `kvStep`), status via `rpctypes.init.spec`; `reqPrin_of_md` from the
run's `rpcCtx` and `mdPrin`; the 2c method's `SrvCallTriple` with the update wrapped (see "What is
good"); outcome 1 → first way (`srvReply` → `replyModels`), 2 → second way or `Step.refuse`, 3 →
third way; `togRPCError.spec`; `header.fill.spec`.
- `kvServer.Range` ✓, `quotaKVServer.Range` ✓, `kvServer.Put`/`quotaKVServer.Put` ✗ (F6 depth; F4
  upstream), `DeleteRange` (both) ✗ F6, `Txn` (both) ✗ F6, `Compact` (both) ✗ F5, F6,
  `kvServer.RangeStream` ✓ given F8, `headerFillingRangeStream.Send` ✗ F8.
- `LeaseServer.LeaseGrant`/`LeaseRevoke`/`LeaseTimeToLive`/`LeaseLeases` and `quotaLeaseServer.*`
  ✗ F1; `LeaseServer.LeaseKeepAlive` ◐ (3.6), `leaseKeepAlive` ✓ (`srvRecv_recv`, `LeaseRenew`,
  `srvSend_send`, `kaSpec`'s trivial `dn`).
- `AuthServer.*` (18) ✓ (pass-through; replies are 2c's `ansReply`, no `fill`; `bodyHolds` depth ≤
  3); `ClusterServer.*` (5) ◐ 7.4 (replies of untranslated structs; `MemberAdd`'s `reqRight` passes
  to 2e's `AddMember`), and F7's `reqRight` on the client side.
- `maintenanceServer.Alarm` ✗ F1; `Status`, `Hash`, `HashKV`, `Defragment`, `MoveLeader`,
  `Downgrade`, `Snapshot` ✓ (`etcdLocal`/`snapSpec`: any outcome; headers built locally;
  `Snapshot`'s gate: recorded 3.6(b)); `authMaintenanceServer.*` (10) ✓ (`isPermitted`, then the
  inner method; `etcdLocal`), but `authMaintenanceServer.Alarm` inherits F1.
- Interceptors: `newUnaryInterceptor` ✓ (notCapable/noLeader/invalid version third way, learner
  second way), `newLogUnaryInterceptor` ✗ F4, `logUnaryRequestStats` ✓ given its pre,
  `newStreamInterceptor` ◐ (`sicEtcdOk` undefined, second tier), `monitorLeader`,
  `cancellableContext.*`, `newCancellableContext` ✓, `metricsOk_*` (assumed) ✓.
- Constructors `NewKVServer`, `NewQuotaKVServer`, `NewLeaseServer`, `NewQuotaLeaseServer`,
  `NewAuthServer`, `NewClusterServer`, `NewMaintenanceServer`, `newHeader`, `newBackendQuota`,
  `newHealthNotifier`, `healthNotifier.startServe`, `getServerMetrics` ✓ (field reads of
  `isServer`'s handles, allocation, persist). `Server` ✗ (F4, F9).
- Helpers `checkRangeRequest`, `checkRangeStreamRequest`, `checkPutRequest`, `checkDeleteRequest`,
  `checkTxnRequest`, `checkRequestOp`, `checkIntervals`, `togRPCError`, `isClientCtxErr`,
  `header.fill`, `header.fillWithoutRevision`, `quotaAlarmer.check`, `AuthAdmin.requireAuthInfo`,
  `authMaintenanceServer.{isPermitted,requireAuthInfo}`, `isRPCSupportedForLearner` ✓;
  `AuthAdmin.isPermitted` ✓ as stated but too weak (F5).

**2b (watch).** `watchServer.Watch` ◐ (its sketch closes from `recvLoop.spec`, `sendLoop.spec`,
`swsAt`; the receive goroutine outliving the run and the reader tokens are recorded A9/3.8);
`recvLoop`, `sendLoop`, `close`, `isWatchPermitted`, `newResponseHeader`, `sendFragments`,
`FiltersFromRequest`, `filterNoPut`, `filterNoDelete`, `IsCreateEvent`, `NewWatchServer`,
`Get/SetProgressReportInterval`, `WatchInternal` laws: sampled (Watch, intervals, filters, the
`srvWatch*` slot laws against grpc's halves through `watchRun_open`) ✓/◐.

**grpc (assumed).** Each "why true" checked against grpc-go v1.84 where it matters: `NewClient`,
`Invoke`, `NewStream`, `Close`, `NewServer`, `RegisterService` (fatal on duplicates: an exit, not a
panic), `Serve`, `ServeHTTP`, `GracefulStop` (waits for handlers via `serveStreams`' wait group),
`Stop`, the option constructors, `status.*` (`Error` refuses `OK`; `FromError`'s three views),
`peer.FromContext`, `health.*`, `insecure.NewCredentials` ✓; `metadata.FromOutgoingContext` +
`MD.Set` ✗ F3; others ✓.

**proto (assumed).** `Marshal`, `Unmarshal`, `Size`, `Clone`, `Merge` ✓; `Equal` second tier.
`decodedAt` ✗ via F2.

**rpctypes.** `Error`, `ErrorDesc`, `EtcdError.Code`, `EtcdError.Error` ✓ (tables verified).

**etcdserverpb / v3lockpb / v3electionpb / version.** Getters (31) ✓ (nil-safe reads of the
unfold laws); stubs `kVClient.*`, `leaseClient.*`, `authClient.*`, `watchClient.Watch` ✓ in WP form;
constructors `New{KV,Lease,Auth,Watch}Client` ✗ F7; generated handlers `_KV_*`, `_Lease_*`, six
`_Auth_*`, `_Watch_Watch_Handler` ✓ (WP form over `decOk_call`, `handlerBodyWP`); `Register*Server`
✓; descriptors ◐ 7.4; `endsDecoded_*` ✗ F2; `holds_depth` incomplete (F6); `Realize.lean` laws ✓;
v3lockpb/v3electionpb relation and field laws ✓; `version.Cluster`, `LessThan` ✓ (some value).

**net/http (2f, assumed).** `Serve`, `Listen`, `Listener.Close`, `NewServeMux`, `ServeMux.Handle`,
`NewRequest`, `Request.WithContext`, `Header.{Get,Set,Get_owned}`, `Error`, `StatusText`,
`URL.String`, `Transport.CloseIdleConnections` ✓ (read; the closed-world premise is the
environment's, as reviewed for rafthttp).

## Snippets

| Snippet | Result |
|---|---|
| grpc/at-most-once | ◐ via F7 (then `attemptOk_call`'s at-most-once and k owned) |
| grpc/status-classify, grpc/metadata-out | ✓ |
| v3rpc/validation-answer | ✗ F10 (helper too narrow) |
| v3rpc/put-then-range | ◐ via F6/F7 |
| v3rpc/compact-admin | ✗ via F5 (and "auth on" must mean "stays on") |
| v3rpc/lease-ttl-unknown | ✗ via F1 on the success path |
| v3rpc/range-stream | ✗ F10 (empty prefix), else via F8 |
| v3rpc/serve | ✗ via F4/F9 |
| v3rpcwatch/* (12 protocol, 2 serve) | 11 ✓ (sampled closely: creates-in-order, two-watches, from-start, progress, cancel, filters), serve ✗ F10, interval ✓ |
| etcdserverpb/kv-stub, watch-stub | ◐ via F7 |
| etcdserverpb/merge-range, txn-response-getters, nil-header, compare-key, request-range | ✓ |
| etcdserverpb/sort-names | blocked (7.4, as its header says) |

## Ranked by need of revision

1. `etcdserverpb/Api.lean` `endsDecoded*` with `Proto.decodedAt` (F2: inconsistent laws).
2. `v3rpc/Api.lean` `HandlerTriple`/`icEtcdOk` (F4) and `Server.spec` (F4, F9).
3. The client↔grpc slots and `etcdUnary`/`AttemptTriple`'s `reqRight` (F7; with 1c).
4. `grpc/metadata/FromOutgoingContext.lean`, `MD__Set.lean` (F3).
5. 2c's lease/alarm replies or 3h's `replyOwn` header (F1).
6. `AuthAdmin__isPermitted.lean`, `kvServer__Compact.lean` (F5).
7. `holds_depth`, `maxTxnOpsMax`/`unaryOut` (F6).
8. `headerFillingRangeStream__Send.lean`, `rsSink_send`/`rsChunk_hdr_last` (F8).
9. Snippets `v3rpc/kv.go`, `v3rpcwatch/serve.go` (F10).
10. Second tier: `mdSeen` order, `Equal`, `encodes`/UTF-8, `start`'s pool, `sicEtcdOk`.

No bug in the Go code was found (every panic above is a spec's, not etcd's); nothing to file in
`issues/`.
