# R-A6 (gRPC boundary): re-review after the repairs (2026-11-09)

Reviewer: fresh, independent; read-only except this file. Commit under review: `974e05095b`
(`specs-only` HEAD), against the round's base `1aa6fc1337`. Area: `Spec/go_etcd_io/etcd/server/v3/
etcdserver/api/v3rpc/` (2a, 2b), `Spec/go_etcd_io/etcd/api/v3/{etcdserverpb,v3rpc,version}` (3h),
`Spec/google_golang_org/` (grpc, metadata, peer, protobuf `proto`), `Spec/net/http/`; snippets
`examples/specreq/{v3rpc,v3rpcwatch,etcdserverpb,grpc}`. Priority from the brief: the three
inconsistencies of the first round (persistent `decodedAt` over a mutable field; `proto.Equal` vs a
`nil`/empty range end; `MD.Set` on a `nil` map), attacked against the new `Proto.norm` design.

I wrote the verdicts below before reading `repair-grpc-v3rpc.md` and `open-questions.md`; I read
them afterwards only to mark recorded decisions and to check that the new findings are not recorded.

## Verdicts

| Batch | Verdict |
|---|---|
| **2a** (v3rpc unary handlers, interceptors, grpc / metadata / peer / proto / rpctypes boundaries) | **FAIL**: N1, N2 (in `kvServer.RangeStream`), N3 |
| **2b** (v3rpc watch server) | **PASS WITH OPEN DECISIONS**: 1.5 (in-process client), 3.8 (wire-request scope), 3.6 / integration-X 1 (`LeaseKeepAlive`'s leaked loop, not 2b's own). I sampled it: only the changed files (`ApiWatch`, `recvLoop`, `sendLoop`, `sendFragments`) were read closely |
| **3h** (etcdserverpb, v3lockpb, v3electionpb, version) | **PASS WITH OPEN DECISIONS**: 7.4 (the untranslated handlers' and stubs' bodies; their specs are now stated). N2's fix should add a 3h law |
| net/http (2f's, in this area by path) | PASS (unchanged since `1aa6fc1337`) |

## The original first-tier findings

| Finding | Status at HEAD | Evidence |
|---|---|---|
| P-F1 lease/alarm `hdr.fill` on a possibly-`nil` header | **Resolved** (in 2c) | The lease methods return `srvHdrReply`, and `replyHdrOwn_header` gives `hdrFillable` (`ApiReq.lean:427-452`). The leader's TTL reply goes through `ltlReply_replyHdr`; the code builds `&pb.ResponseHeader{}` (`v3_server.go:650`, `leasehttp/http.go:132`). For `Alarm` the finding did not apply: `maintenance.go:263-265` replaces a `nil` header |
| P-F2 persistent `decodedAt` over a mutable field | **Resolved differently**. The inconsistency is gone, but the new share-based `endsDecoded` breaks one caller (**N2**) | `Content` is now Go values and `norm` is the wire view (`proto/Api.lean`). `endsDecoded` is `∃ dq c, msgAt t p dq c ∗ ⌜endsOk c⌝` (`etcdserverpb/Api.lean:507`). The old counterexample (`endsDecoded_range_intro` on a `nil` end, then a rewrite) now has no persistent fact to carry over. I tried to derive `False` through `endsOk_range_intro`, `holds_norm`, `encodes_fun`/`norm_facts`, `msgAt_split` and `endsDecoded_ro` and did not find one. `endsOk_range_intro` rules out the empty end through `endOf`'s `[0]` |
| (round 1, second inconsistency) `proto.Equal` vs `nil`/empty end | **Resolved** | `Equal.spec`: `b = true → norm c = norm d`, and the converse only under `noFloats t`. `Clone` gives `mergeDst … (norm c)`, which matches `mergeBytesNoZero` (`protobuf@v1.36.12/internal/impl/merge.go:191-196`) |
| P-F3 `FromOutgoingContext` `nil` map + `MD.Set` | **Not resolved: the fix made the boundary inconsistent (N1)** | — |
| P-F4 log interceptor loses the request | **Resolved** | `reqBack` is in `HandlerTriple`'s post and in `icEtcdOk`'s continuation (`v3rpc/Api.lean:520-547, 715-727`). `rpcCtx` is persistent (`grpc/Api.lean:581`), so `logUnaryRequestStats`' pre is met |
| P-F5 `Compact`'s admin denial | **Resolved as stated** (`adminDenied`, W0's `State.adminDenied`, `Model.lean:859-866, 1042-1045`). **But `isPermitted.spec` is still false under an `AuthEnable` race (N3)** | — |
| P-F6 reply depth | **Resolved** (C14) | `holds_depth_resp`, `respOpDepth`/`txnRespDepth`, `depthMax = 10001`. The bound matches protobuf-go's decoder: `opts.depth--` per level from `RecursionLimit = 10000`, so a depth of 10000 decodes |
| P-F7 client→grpc slots, `reqRight` | **Resolved for 2a/3h**; the client-side remainder is client-core's | `unaryArgs_msgAt`, `grpcCallOptsOk_unfold`, `grpcConnAt_of`, `grpcConnVia_unfold` (`Realize.lean`), `connOk_unfold` (`client/v3/credentials/Api.lean:81`). `etcdUnary`'s second way gives `reqRight` back; `AttemptTriple` carries it |
| P-F8 `headerFillingRangeStream.Send`, `rsChunk_hdr_last` | **Resolved** | `chunk_msgAt.spec`; `rsSink_send`'s `∀ m0 ∈ ms, m0.hdr = none`, which holds of `rangeStream` (`v3_server.go:249-266`: only the last chunk has a header) |
| P-F9 untranslated handlers in `regsOk` | **Resolved; open decision 7.4 remains** | Every descriptor names its handlers (`kvDesc_init`, `authDesc_init`, `otherDescs_init`). There are now 26 new WP-form handler specs; their proofs wait for the translation |
| P-F10 snippets | **Resolved** | `refusalOrIndefinite`/`indefinite` cover every `EtcdErr.refusal` and every mapped indefinite error (checked against `Model.lean:348-379` and `rpctypes.mapped`). `ReqRangeStream` returns early on `""`. `ReqServeWatch`'s Assumes now covers `gs` |
| C-F1 stubs/handlers with no spec | **Resolved; open decision 7.4 remains** | `kVClient.RangeStream`, 11 `authClient.*`, 5 `clusterClient.*`, 8 `maintenanceClient.*`, `NewClusterClient`, `NewMaintenanceClient`, and the matching `_*_Handler`s |
| C-F2 Kubernetes' dial options | **Resolved differently** (C16) | Pass-through options as `dialOptAt v id` under `cliIcPass`/`cliSicPass`/`statsOk`/`ctxDialerOk`; snippet `grpc/dialopts.go`. Sound: grpc runs `dopts.unaryInt` first, then the chain, and a pass-through calls its invoker once |
| C-F3 `grpc.Peer` | **Resolved** | `Peer.spec` takes `p ↦ v`; `peer/Api.lean` adds `peerFieldsOk`, `peerVar_inv` and `peerOk_fields`; `Peer.String.spec` is restored |
| C-F4 election/lock registrations | **Resolved differently** (C15) | `etcdContract` has `etcdLocal`/`snapSpec` entries for `/v3electionpb.*` and `/v3lockpb.*`. `regsOk` constrains only registered methods (`grpc/Api.lean:792`) |
| C-F6 dropped stringers | **Resolved** | `SetLoggerV2`, `Peer.String`, `HealthCheckResponse_ServingStatus.String`, `NewLoggableTxnRequest`, `RangeRequest.String`, `AlarmType.String`; `stringerAt` in `Stringer.lean` |

## New first-tier findings

### N1. `FromOutgoingContext.spec` + `mdAt_ownMap.spec` ⊢ `False`: a panicking program can be proved safe (2a, grpc `metadata` boundary)

**Evidence.**
- `FromOutgoingContext.spec` (`Spec/google_golang_org/grpc/metadata/FromOutgoingContext.lean`): the post is `mdAt m (own 1) md ∗ ⌜(ok = false → m = null ∧ md = []) ∧ …⌝` on every path. Its header says "`mdAt` of the `nil` map is still given: it reads as empty".
- `mdAt_ownMap.spec` (`grpc/Api.lean:874-877`, present since before the round) gives `mdAt m dq md ⊣⊢ ∃ mm, ownMap m dq mm ∗ …`.
- Perennial's `ownMap` is a `heapPointsto` (`Perennial/Golang/Theory/Map.lean:327-335`, `ownMap_unseal`), and `heapPointsto_non_null` (`GooseLang/Lifting.lean:246`) gives `⌜m ≠ null⌝`.

So in the `ok = false` branch, `mdAt null (own 1) []` ⊢ `False`. grpc-go returns `nil, false` whenever the context has no outgoing metadata (`grpc@v1.84.0/metadata/metadata.go:331-335`). The assumed spec is therefore false of the library, and its post is contradictory.

**Counterexample** (only the stated specs and Perennial's lemmas):
```go
md, ok := metadata.FromOutgoingContext(context.Background())
if !ok { panic("no metadata") }          // reached in Go
md.Set("k", "v")
```
- `outMD_noMeta`/`outMD_ctxOk` give `outMD ctx []`. Then `FromOutgoingContext.spec`.
- In the `ok = false` case, `mdAt_ownMap`, `ownMap_unseal` and `heapPointsto_non_null` give `False`, so the `panic` is dead in the proof.
- Dropping the `if` and calling `md.Set` on the `nil` map (a Go panic) is "proved" the same way. So the first round's `MD.Set` hole is not closed: it is now reached through `False` rather than through `Set`'s missing premise.

**Who is affected.**
- Every caller's `ok = false` branch is vacuous: `WithRequireLeader`, `withVersion` (`client/ctx.go:29,42`), the lessor's `FromOutgoingContext` loop (`client/lease.go:390`), `streamKeyFromCtx` (`client/watch.go:1103`).
- The snippet `grpc/metadata-out` (`ReqMetadataOut`, "Assumes: ctx carries no outgoing metadata") is proved vacuously. It calls `md.Copy()` and `md.Get` on the `nil` map, which Go allows; the specs give no non-vacuous way to do so.
- Not recorded (`repair-grpc-v3rpc.md` P-F3 reports it "fixed").

**Fix.** Keep `nil` out of `mdAt`, as `FromIncomingContext.spec` already does:
```
{{ … }} FromOutgoingContext ctx
{{ m ok, RET (m, ok); (⌜ok = true ∧ m ≠ null⌝ ∗ mdAt m (own 1) md) ∨ ⌜ok = false ∧ m = null ∧ md = []⌝ }}
```
Then add `nil`-map cases to `MD.Copy.spec` and `MD.Get.spec` (`m = null`: `Copy` returns a fresh empty `mdAt`, `Get` returns `[]`), which `ReqMetadataOut` needs. Alternatively, weaken `mdAt_ownMap` to `(⌜m = null ∧ md = []⌝ ∗ …) ∨ ∃ mm, ownMap …`, with `MD.Set` keeping `m ≠ null`; check that no other law then breaks (`mdAt_persist` and the fractions are harmless at `null`). Restate the file's header either way.

### N2. `EtcdServer.RangeStream.spec` needs the request at `own 1` *and* an `endsDecoded` share: no caller can supply both, so `kvServer.RangeStream.spec` does not close (2a's step; the spec is 2c's; the law fix is 3h's)

**Evidence.**
- `EtcdServer__RangeStream.lean`'s pre: `rangeReqOwn r (DFrac.own 1) rm ∗ EtcdServerPb.endsDecoded RangeRequest.ty r ∗ …`.
- `rangeReqOwn r (own 1) rm ⊣⊢ ∃ c, msgAt … r (own 1) c ∗ …` (`rangeReqOwn_msgAt`). `endsDecoded` is now `∃ dq c, msgAt … r dq c ∗ ⌜endsOk c⌝` (`etcdserverpb/Api.lean:507`), a second share.
- Together that is more than the whole message. No law produces `msgAt` at a fraction above 1: `msgAt_split` only splits or rejoins existing shares. In the intended realization (field points-to) the pre is `False`.
- `kvServer.RangeStream` holds exactly `msgAt r (own 1) c ∗ ⌜norm c = c⌝` (`kvServer__RangeStream.lean`). Its sketch "splits the message (`msgAt_split`) into `rangeReqOwn` and `endsDecoded`", but 2c wants `rangeReqOwn` at `own 1`.
- The full ownership is real: `rangeStream` writes `r.Limit`, `r.Revision` and `r.Key` (`v3_server.go:214-216, 238-240, 268-270`). So `own 1` cannot simply be dropped.
- `Range` and `Txn` take `rangeReqOwn`/`txnReqOwn` at any `dq` and are fine.
- The design note (`etcdserverpb/Api.lean:485-496`: "while it is held nobody can write the fields") assumed no holder writes the message. `RangeStream` does.

**Who is affected.** `kvServer.RangeStream.spec`, hence `_KV_RangeStream_Handler`'s `streamOk` in `Server.spec`'s `regsOk`; the snippet `v3rpc/range-stream`; W0's `RangeStreamTriple` (`kv.GetStream`, Kubernetes' streamed lists). Not recorded.

**Fix.** Give `RangeStream` the end fact as a pure fact about the content it fully owns. For example, the pre `∃ c, msgAt RangeRequest.ty r (own 1) c ∗ ⌜reqHolds c (.range rm) ∧ endsOk c⌝`, with a 3h unfold law `msgAt RangeRequest.ty p dq c ∗ ⌜reqHolds c (.range r) ∧ endsOk c⌝ ⊣⊢ rangeReqOwn p dq r`-with-`⌜es = slice.nil ∨ ebs ≠ []⌝` (the fields unfolded with the end fact). `rangeStream` never writes `RangeEnd`, so the fact read at entry holds throughout. Equivalently, `endsDecoded` could hold a share of the `RangeEnd` field only, not of the whole message.

### N3. `AuthAdmin.isPermitted.spec` is false under an `AuthEnable` race and not provable from `AuthInfoFromCtx.spec` (2a, with W0's `State.adminDenied`)

**Evidence.**
- `isPermitted` is `AuthInfoFromCtx(ctx)` then `IsAdminPermitted(authInfo)` (`v3rpc/auth.go:182-189`). Each reads the auth flag on its own (`auth/store.go:1072-1074, 916-918`).
- 2c's `AuthInfoFromCtx.spec` returns `null` (no error) or a user that is `p` **or `tls`**. It returns `null` whenever auth is off at its read, token or not; `EtcdServer.AuthInfoFromCtx` then falls back to the TLS name (`v3_server.go:1206-1215`).
- `isPermitted.spec`'s denial is `adminDenied σ who e` with the context's `who` (`v3rpc/Api.lean`, `adminDenied`). For `who = some u` with `u ≠ []`, that admits only `userNotFound`/`permissionDenied` *of `u`*.

Two schedules give a denial the spec does not admit:
- **(a)** A root user with a token; auth off at `AuthInfoFromCtx` (`nil`), `AuthEnable` applied, then `IsAdminPermitted` sees auth on and returns `ErrUserEmpty`. `adminDenied σ (some u) .userEmpty` needs `u = []`, so the post is false.
- **(b)** The same with `--client-cert-auth`: the check runs on the certificate's user. That user may be absent or not root while `who` is root, so `ErrUserNotFound`/`ErrPermissionDenied` comes out for a `who` that is an admin.

`kvServer.Compact` must then fire W0's compact denial `σ.adminDenied who e` (`Model.lean:1045`), which no state satisfies. The third way needs `indefMsg`, false for these descriptions, so `kvServer.Compact.spec` is unprovable at that schedule. `authMaintenanceServer.isPermitted` (`Snapshot`, `Hash`, …) has the same shape; check its post.

**Who is affected.** `kvServer.Compact`, `quotaKVServer.Compact`; snippet `v3rpc/compact-admin`, if its "auth on" lets `AuthEnable` race the call. Not recorded. The closest is `nonissues/etcd-compact-admin-check-lagging-member.md`, a different race.

**Fix.**
- Widen `adminDenied` (2a's and W0's `State.adminDenied`) to the principal the check actually read:
  ```
  ∃ w, (w = who ∨ w = tls ∨ (w = none ∧ ∃ j a, σ.authTables[j]? = some a ∧ a.enabled = false)) ∧ <today's body at w>
  ```
  This takes `tls` into `isPermitted`'s post and into W0's compact denial.
- Or state the `AuthEnable`-race denial as a refusal the model allows (`ErrUserEmpty` is already `EtcdErr.refusal`; `Step.refuse` could be fired for it, but `userNotFound`/`permissionDenied` are not refusals).
- Record the behavior in `nonissues/` (found by reading; a spurious `ErrUserEmpty`, or a check of the wrong user, for an administrator's `Compact` while auth is being enabled). This report does not write it (read-only).

## Second-tier findings (new)

- **Stale proof sketches citing names that no longer exist** (2c's files, flagged by the repair as its request 3 and still open):
  - `EtcdServer__Range.lean:55-56`, `EtcdServer__RangeStream.lean:31-32` and `EtcdServer__Txn.lean:22-23` cite `Proto.decodedAt`, `endsDecoded_of_decoded`, `endsDecoded_range_intro`.
  - `kvServer__RangeStream.lean:20` mentions `Proto.decodedAt` as the old form, which is fine.
  - The current names are `endsDecoded_of_canon` and `endsOk_range_intro`.
- **`kvServer__Compact.lean`'s Margin** ("relies on the model answering `adminErr` at any state") predates `adminDenied`.
- **`stringerAt_msg`, `NewLoggableTxnRequest`, `RangeRequest.String`** take no depth bound. protobuf's text marshaling recurses per level like `Marshal`, which the Proto header bounds by `depthMax` for the stack's sake (a fatal error beyond about a million levels). Add `⌜depth c < depthMax⌝` for consistency. Callers hold it: the server's requests are checked or decoded.
- **`norm`'s description does not say what it does to the elements of a repeated `bytes` field.** Decoding gives an empty element as non-`nil` (`consumeBytesSlice`: `append(emptyBuf[:], v...)`, `codec_gen.go:5577`), and `Equal` treats `nil` and empty elements alike. So `norm` must map a `nil` element to a non-`nil` empty one for `Unmarshal.spec`'s `norm c = c` and `Equal.spec` to both hold. Say so in the header (`LeaseTimeToLiveResponse.Keys` is such a field).
- **Unchanged from the first round:**
  - `sicEtcdOk` is still opaque with no meaning law, recorded among the repairs' gaps;
  - `version.LessThan` over any `val`, recorded;
  - `LeaseKeepAlive`'s leaked loop, 3.6.

## Regressions checked (changed files since `1aa6fc1337`)

`git diff --stat 1aa6fc1337 --` over the area: 146 files, 4255+/223−.

- **`proto/` (Api, Equal, Unmarshal, Clone).** Consistent as far as I could attack them: the `False` attempts above, `zero_facts` with `encodes_fun`, and `Clone` with `norm_facts`. True of protobuf-go 1.36.12 except the description gap above.
- **`grpc/Api.lean`.**
  - `unaryOut` sends `norm c`, and `attemptOk_call`/`cliSend_send`/`srvSend_send` deliver `norm`, which matches the codec.
  - `decOk_call` and `srvRecv_recv`/`cliRecv_recv` give canonical contents. `unaryOk` quantifies over any `c`, and `decOk` comes only from grpc's run of a sent `norm c`.
  - `mdSeen (mdc ++ md0)` now matches grpc-go's order.
  - `icChain_nil`, `cliIcPass_call`, `dialAux_persistent` are fine.
  - `GracefulStop` returns `threadToks n`: plausible, given `start` consumed the pool.
- **`metadata/`.** `Copy`, `New` and `Pairs` now return non-`nil` maps, which is correct. **`FromOutgoingContext`: N1.**
- **`peer/`, `Peer`.** Correct against `rpc_util.go:312-331` and `peer/peer.go`. The per-field invariant is fine: grpc's copy runs on the caller's goroutine after the attempt.
- **`etcdserverpb/Api.lean`.**
  - `holds_norm` (the requests' clauses under `endsOk`, which `unaryArgs_msgAt` takes) and `holds_depth_resp` are plausible from the realization.
  - `endsDecoded` and its laws are sound (each law reads the field against the share it holds), but see N2.
  - The descriptors name the generated handlers.
- **`Realize.lean`, `StreamShapes.lean`, `Stringer.lean`, the 26 new handler specs and 30 new stub specs.** I read `_Auth_UserGet_Handler`, `_KV_RangeStream_Handler`, `kVClient.RangeStream`, `authClient.UserGet`, `NewKVClient` and `NewLoggableTxnRequest` in full. The rest follow one template (`git diff` line counts identical per kind), which I checked for the method names and types against `rpc_grpc.pb.go`'s descriptor order.
- **`v3rpc/`.**
  - The `Api.lean` changes (`adminDenied`, `errCode`, `reqBack`, election/lock contracts, `rsSink_send`'s premise) are covered above.
  - `togRPCError` is over `srvErr`/`errCode`, true against `util.go:36-49`.
  - The handlers' one-line changes (sketch notes) are consistent with their callees.
  - 2b's teardown and reader-token notes are consistent with mvcc's `srvReader_mvcc`, sampled.
- **Snippets.** `grpc/dialopts.go` closes from the four option specs and `dialOptsOk_neutral` (1c's). `v3rpc/kv.go`'s changes close, except `ReqRangeStream`, blocked by N2. `v3rpcwatch/serve.go` closes.

## Counts

- Original first-tier findings: 15 (provability 10, completeness 5).
  - 12 resolved.
  - 2 resolved but with open decision 7.4 (P-F9, C-F1).
  - 1 not resolved (P-F3, now N1).
- New first-tier findings: 3 (N1, N2, N3). New second-tier: 4.
- Spec files changed in the area: 143.
  - 47 read in full: proto 4, grpc and metadata 17, peer 3, etcdserverpb `Api`/`Realize`/`StreamShapes`/`Stringer` and 9 handlers/stubs/constructors, v3rpc `Api`, `ApiWatch`, `isPermitted`, `Compact`, `RangeStream`, `togRPCError`, `logUnaryRequestStats`, `newLogUnaryInterceptor`, `Server`, the watch loops.
  - The remaining templated handler, stub and one-line sketch changes were checked by pattern.
- Snippets changed or added: 3 files (5 REQs). Closing: 4; blocked by N2: 1 (`v3rpc/range-stream`). Vacuous because of N1: `grpc/metadata-out` (unchanged file).

No bug in the Go code was found that `issues/` lacks. N3's behavior (an administrator's `Compact` refused, or checked as the wrong user, while auth is being enabled) belongs in `nonissues/` (code reading). N1 and N2 are bugs in this repository's specs (`notes/`).
