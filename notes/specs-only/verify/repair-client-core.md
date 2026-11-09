# Repair, group `client-core` (2026-11-09)

Reports worked from: `A1-client-kv-{provability,completeness}.md` (all), `A2-client-watch-lease-
{provability,completeness}.md` (1c's findings), `A9-apply-txn-lease-auth-completeness.md` F1; the
coordinator's relayed requests from lease-auth and client-watch.

## A1-client-kv, provability

- **F1** (`GetStreamToGetResponse` error post): fixed. The error post has the disjunct
  `⌜err = errVal .compacted⌝` (no `Q`), as `streamAt_recv`. New snippet `ReqGetStreamWhole`
  (`clientv3kv/stream.go`).
- **F2** (`callErr_errorsNew` contradicts `callErr_eof`): fixed as suggested: the law concludes
  `globalAddr context.Canceled ↦□ err ∨ globalAddr io.EOF ↦□ err` (`client/v3/Api.lean`).
- **F3** (`GetStream`'s `io.EOF` test): fixed. `wireStreamAt_recv`'s error branch gives
  `∃ eof, globalAddr io.EOF ↦□ eof ∗ ⌜err ≠ eof⌝`; new law `errorsIs_callErr_eof.spec`
  (`errors.Is(err, eof)` is `false` for a call error other than `io.EOF`'s value; 2a realizes it).
  `kv__GetStream.lean`'s sketch updated.
- **F4** (`Op.WithRangeBytes` at `nil`): fixed: post `rangeEnd := if b = slice.nil then none else
  some k`.
- **F5** (a non-`nil` empty range end): fixed by the reviewer's first option, a scope premise, placed
  where the request is sent: `OpM.emptyEnd` (new, mutual with `anyEmptyEnd`: a `some []` end at any
  depth), `= false` in `KV.GetTriple`, `DeleteTriple`, `DoTriple`, `GetStreamTriple`,
  `Txn.ThenTriple`, `Txn.ElseTriple`; `Cmp.WithRange.spec` takes `e ≠ []` (its post's end is then
  `e`). Why not the transport mode: the client's request messages are modelled by `Wire.endOf`,
  shared with mvcc's reading (txn's `Count` relies on it), so the wire reading cannot be expressed
  without a second message model. I checked every caller in scope: leasing's `WithRange(end)` are
  reached only with a non-empty end (`leasing/kv.go:394`, `txn.go:122`), the gRPC proxy guards it,
  Kubernetes passes `GetPrefixRangeEnd`. New nonissue `nonissues/etcd-client-withrange-empty-end.md`.
  Header paragraph "Range ends" in `Api.lean`; snippet `Assumes:` lines updated (`stream.go`).
- **F6** (no law persisting a built request): fixed: `EtcdWire.protoRest_persist.spec`
  (`api/v3/Wire.lean`: `protoRest t p (own 1) ⊢ |==> protoRest t p discard`). Sketches of the
  `Cmp` constructors, `OpTxn`, `cloneCompare`, `Cmp.GetCompare`, `kv.Do`, `txn.If/Commit` cite it.
- **F7** (compact options keep the revision): fixed: law `compactOptAt_rev.spec`; `kv__Compact`'s
  sketch cites it.
- **F8** (stale "Open" paragraphs): fixed in `retryKVClient__{Range,Txn}.lean`.
- **F9** (`etcdState_revFits` realization): fixed: `State.lean`'s header now puts the bounds in the
  half the program holds (and in each `etcdLb`).
- **N1**: fixed (header names the refusal-and-indefinite exceptions). **N2**: fixed (`ReqAuthRefusal`'s
  `Assumes:` gives `authLb γ lo` at an auth-on index). **N3**: fixed (`putPanics` docstring).
  **N4**: fixed (zap `Api.lean` header, Margin paragraph).

## A1-client-kv, completeness

- **F1** (`GetStream`'s thread token): fixed differently from "give it back": the premise is
  dropped (Perennial's `wp_fork` forks without tokens), in `KV.GetStreamTriple` pre and post; the
  margin is now the leaked goroutine. `kv__GetStream`, `Client__GetStream`, `ReqGetStream` updated.
- **F2** (no `kvAt`/`txnAt` introduction): fixed. `kvAt_intro.spec` (seven triples over a persistent
  `P` ⊢ `kvAt`), `txnAt_intro.spec` (four triples over a state predicate `S` ⊢ `txnAt`); to state
  the latter, `Txn.{If,Then,Else,Commit}Triple` take an optional last argument `T` (default
  `txnAt`). New snippet `ReqKVWrapper` (`clientv3kv/wrap.go`, the latency tracker's shape);
  `ReqNewWrapClose` cites `kvAt_intro`.
- **F3** (`ctxPrin_todo` a second triple): fixed: `ctxPrin_todo.spec : ⊢ ctxPrin dflt
  (GoInterface.ok context.todoCtxVal) dflt`.
- **F4** (unissued token): not fixed: open question 1.5 (`tokenUnissued` is 3d's). Note: an
  introduction of `ctxPrin` at *any* principal would contradict 1b's `ctxStreamKey_prin`; whoever
  decides 1.5 must give a fixed principal there.
- **F5** (`ctx.Value`): fixed. `Spec/context/Api.lean`: `ctxValueIs ctx key v` (persistent),
  `WithValue.spec`'s post gives it, `Value.spec` (returns the recorded value if any),
  `ctxValueIs_child`, `ctxValueIs_other`, and (lease-auth's request) `ctxValueIs_wp` (the WP form
  of `Auth.ctxValIs`). I added a predicate rather than an argument to `ctxValueAt`, which six other
  groups' files use. `lessor__keepAliveCtxCloser`'s sketch cites it.
- **S1** (zap): mostly fixed: new trust-boundary specs `Float64`, `Time`, `Binary`,
  `Logger.Named`, `Logger.With`, `Logger.Sync`. Not done: `Logger.Core`/`Core.Enabled`,
  `WithOptions`, `Sugar` (they need a core/sugared-logger predicate; their callers'
  sketches assume them).
- **S2** (namespace): note only. **S3**: fixed (N3). **S4**: request to grpc-v3rpc below.

## A2 (1c), provability

- **L1** (`NewLease`): fixed differently from the suggestion. `NewLeaseFromLeaseClient.spec` takes
  `∀ cr, cr = c ∨ cr = null →` the remote's contract gated by `clientReady cr` and returns
  `lessorHandle l cr`: `NewLease` passes `cr = c`; the in-process client passes `cr = null` (its
  adapter needs no readiness), which avoids a cycle with `clientBare_assemble` (that law mints
  `clientReady c` but needs `leaseAt` first). Also takes `□ ∀ ep, clientVia cr ep -∗ remoteVia
  remote ep` (L2).
- **L2** (per-member lease view): fixed by threading a member view through the wire contract:
  `ApiClient.lean`: `grpcConnVia cc ep` (slot, 2a), `leaseAnsRes`, `viaPre`, `viaFact`;
  `AttemptTriple` and `uiOk_call` take `via` (pre `viaPre γ (grpcConnVia cc) via`, post
  `viaFact`); `CallTriple` takes an optional extra post `F`; `RemoteCallTriple` an optional member
  condition `V` (default `False`: no per-member form) and `via`; laws `clientVia_conn`,
  `epsTok_null`. `ApiLease.lean`: `remoteVia v ep`, `retryLeaseHandle_remoteVia`,
  `remoteLeaseAt_call` at `V = remoteVia v`; `retryLeaseClient.Lease{Grant,TimeToLive,Leases}.spec`
  at `V = clientVia c`. `LeaseRead.Triple`'s post is now `viaFact`, which also fixes an overpromise:
  it claimed `leaseAnsAt` of a refusal.
- **S3**: fixed (`clientReady`'s intended realization in `ApiClient.lean`'s "Readiness").
- **S4** (resolver race, `issues/etcd-client-resolver-build-race.md`): fixed by the coordinator's
  decision (b): new exclusive `resolverIdle c` (`ApiClient.lean`: no RPC can wake the connection),
  a premise (given back) of `Client.SetEndpoints.spec` and `Client.Sync.spec`; `newClient` holds it
  for its own `SetEndpoints` before dialing and gives it to no caller. `cfgOk` now requires
  `AutoSyncInterval = 0` (the `verifyOff` alternative dropped), so `New`, `newClient` and
  `kubernetes.New` give the endpoints token unconditionally, and `autoSync.spec` covers only the
  interval `0`. Snippet `ReqSync` removed (a note in `clientv3client/cluster.go`).
- **S5**: fixed: `lessor.Close.spec` no longer takes `clientReady c`.

## A2 (1c), completeness

- **F1** (`kubernetes.New` drops `epsTok`): fixed; snippet `ReqKubeStatus`.
- **F2** (`dialOptsOk` intro): partly fixed: `dialOptsOk_neutral.spec` (options that are the
  identity on `Grpc.DialCfg`: keepalive, stats handler, context dialer, `WithBlock`, as 2a states
  them). The interceptor options (Kubernetes' `WithChain*`, the proxy's `With*Interceptor`) need
  2a's model of chained interceptors and specs of the four missing dial options: request below.
  `ReqNewTLS` not changed (it would not be provable yet).
- **F3** (`NewKVFromKVClient` pre): fixed: `⌜c = null⌝ ∨ ∃ who', clientBase c who'`;
  `clientBase`'s description now includes the call options.
- **F4** (`(*ID).String`): fixed: `types/ID__String_ptr.lean`.
- **S2**: fixed (`Client__ActiveConnection` Users line). **S3** (promoted `*kubernetes.Client`
  methods): not done. **S4**: fixed: `types/URLs__StringSlice_ptr.lean`, `URLs__Len_ptr.lean`.
  **S7**: the `dialOptsOk` doc now states the pin's order (the caller's options before the client's
  interceptors, so grpc keeps the client's); the nonissue was checked upstream, not at the pin.

## A9-completeness F1 (`deniedSince`)

Fixed: `State.deniedSince` (`api/v3/Model.lean`) is the three-view form: for one pair, the flag on at
table `jf`, no principal or not root at `jx`, not covered (or inverted) at `jc`, all `≥ lo`. The old
one-state denial is the case `jf = jx = jc`. New nonissue `nonissues/etcd-auth-read-denied-across-views.md`.

## Sentinel errors

`ClientV3.init.spec` gives `ErrNoAvailableEndpoints`, `ErrOldCluster`, `ErrMutuallyExclusiveCfg`
existentially: read-only, pairwise distinct, non-`nil`, none an `errVal`; also `LeaseResponseChSize ↦□
16` (what `lessor.KeepAlive` reads). `New.spec`'s no-endpoint post returns the global's value.
rpctypes' `errVal` stays a fixed value: `EtcdError` is a struct value, not a pointer.

## Other requests handled

- server-boot (A8-completeness F2): `urlsRight` stays keyed by the raw strings a client holds; new
  law `urlsRight_norm.spec` (`State.lean`: for a list `NewURLs` accepts, `urlsRight γ urls ⊢
  urlsRight γ (Types.urlsNorm urls)`), with `Types.urlsNorm_idem` and `Types.urlsNorm_perm`
  (`client/pkg/v3/types/Api.lean`, assumed of `net/url`). Intended realization: the right keyed by
  `urlsNorm` of its strings. `State.lean` now imports `types/Api.lean`. The right is still spent on a
  refusal (`reqRight`'s margin; returning it is server-boot's second tier, not done).

- lease-auth: `Context.ctxValueIs_wp` (done). `AuthReach` from `Reach`: not done. `AuthReach` is
  3d's definition, so the law belongs in `auth/Api.lean`, as a pure consequence of W0's model.
- client-watch: the duplicate `streamKeyOf`/`streamKeyOf_prin` I first added to `Api.lean` was
  removed; theirs (`ctxStreamKey_prin`) stands, and `ctxPrin`'s docstring now states the
  constraint and the intended realization over `Grpc.outMD`. `fmt`: `Fmt.printMD`,
  `mdPrintable`, `printMD_inj` (the pure part; the `Sprintf` triple over the map's heap form is
  requested of 2a). `newClient` sketch: updated to apply `watcherHandle_watcherAt` after
  `clientReady c`.

## Requests to grpc-v3rpc

1. `AttemptTriple` (`ApiClient.lean`) now takes `via` with pre `viaPre γ (grpcConnVia cc) via`
   and gives `viaFact` in outcomes 1 and 2: 2a's proof gets it from the answering member
   (`servesAt γ ep`, `leaseFact`); `grpcConnVia cc ep` is 2a's slot (the connection's resolver holds
   `ep` alone). The stubs (`leaseClient.*`, `cc.Invoke`) must pass `via` through. `NewLeaseClient.spec`'s
   post should also give `□ ∀ ep, grpcConnVia conn ep -∗ ClientV3.remoteVia v ep`.
2. Readiness (W3's analogue for every stub): `NewLeaseClient`, `NewKVClient`, `NewAuthClient`,
   `NewClusterClient`, `NewMaintenanceClient` give `remote*At` over `connOk` at once, but the
   client's interceptor needs `clientReady c` (`uiOk_call`). Gate the post by the readiness of the
   connection's client.
3. Specs of `WithChainUnaryInterceptor`, `WithChainStreamInterceptor`, `WithStatsHandler`,
   `WithContextDialer`, and chained interceptors in `DialCfg`, so that `dialOptsOk` can be
   introduced for Kubernetes' and the proxy's options (A2-C F2).
4. Realize the new laws: `errorsIs_callErr_eof`, `wireStreamAt_recv`'s non-EOF error,
   `callErr_errorsNew`'s `io.EOF` disjunct, and (3h) `EtcdWire.protoRest_persist`.
5. `grpc/ClientConn__Invoke.lean:16` cites "V3rpc's `servesAt_serves`", which exists nowhere
   (A1-C S4).
6. `fmt.Sprintf("%+v", md)` of a `metadata.MD`, as a triple returning `Fmt.printMD md` over the
   map `outMD` gives (client-watch's `streamKeyFromCtx`).

## Requests to client-users

- `KV.GetStreamTriple` no longer takes a thread token (leasing's `GetStream` sketch).
- The KV triples take `emptyEnd = false` (leasing's ends are non-empty).
- `callErr_errorsNew` has an `io.EOF` disjunct: 1d's `Mutex.TryLock`/`Lock`/`Proclaim` and 1f's
  sketches tell their sentinels apart by message from both.
- `ctxPrin_todo` is now an entailment at `context.todoCtxVal` (with `Context.TODO.spec`).
- `Txn.*Triple` take an optional state predicate (leasing's `LTxn` triples may reuse the shape).

## Requests to server-core, rafthttp, server-boot

- Cite `Types.ID.String_ptr.spec` at pointer-receiver calls (`checkClusterCompatibilityFromHeader`,
  `streamReader.dial`, membership, etcdserver); `URLs.StringSlice_ptr`/`URLs.Len_ptr` (`NewServer`,
  `setPeerURLsHeader`).
- 2c's `Range`/`Txn` denial: fire `State.deniedSince` (now three views) from 3d's `checkPost`.
- `raftRequest`: `Context.Value.spec` for `StartTimeKey`.

## New decisions

**Empty range ends are out of scope.** The client's KV specs take `emptyEnd = false` (and
`Cmp.WithRange` `e ≠ []`). The alternative is a transport mode in the client's request model,
because a dialed member reads such an end as one key and an in-process one as every key from the key
on. No caller in scope passes such an end.

**`SetEndpoints` and the resolver's `Build`**: decided by the coordinator, option (b) (above,
A2 S4): `Sync`, auto-sync and a caller's `SetEndpoints` after `New` are out of the top-level
workloads.

**`NewLeaseFromLeaseClient`'s choice of `cr`.** The handle records the caller's client or `null`.
This is the only way I found to serve both `NewLease` (readiness needed) and the in-process client
(whose readiness is minted after its `Lease` field is set).

## Build

`etc/specs-build.sh` OK on everything I touched and its importers in the client and auth: `--dir`
`Spec/go_etcd_io/etcd/api/v3`, `Spec/context`, `Spec/go_uber_org/zap`, `Spec/fmt`,
`Spec/go_etcd_io/etcd/client/pkg/v3/types`, `Spec/go_etcd_io/etcd/client/v3` (with the watch files),
`.../kubernetes`, `.../concurrency`, `.../leasing`, `.../experimental/recipes`,
`Spec/go_etcd_io/etcd/api/v3/etcdserverpb`, `Spec/go_etcd_io/etcd/server/v3/auth`, otel `trace`,
`pkg/v3/traceutil` (771 modules). `server/.../api/v3rpc` was not checked: it imports apply-txn's
`apply/Api.lean`, which failed (`go.Semantics` instance, line 924) while that group was working.
After the last changes (the `SetEndpoints` decision, `urlsRight_norm`): `api/v3`, `types`,
`client/v3` (all of it, with `kubernetes`, `concurrency`, `leasing`, `recipes`) and `auth` rebuilt OK
(613 modules).
Snippets: `go vet` and `gofmt -l` clean for `clientv3kv`, `clientv3client`, `clientv3lease`.

## Second pass (coordinator, `second-pass.md`; grpc-v3rpc's "Requests to client-core")

1. **Compact's admin denial at two tables (P-F5)**: done. `State.adminDenied σ who e`
   (`api/v3/Model.lean`, the shape of `V3rpc.adminDenied`: the flag on at one table, the user empty,
   absent or not root at another); `kvStep .compact`'s denial is `∃ e, σ.adminDenied who e`. (The
   old one-table form also answered `userNotFound` for the empty user; the code answers `userEmpty`.)
2. **`connOk` laws (P-F7)**: done as one unfold law, `Credentials.connOk_unfold.spec`
   (`client/v3/credentials/Api.lean`, since it mentions `credMD`): `connOk conn γ who ⊣⊢ ∃ A ui si
   c, Grpc.connAt conn A (some ui) (some si) (credMD γ who) ∗ uiOk ui c γ who ∗ siOk si c γ who ∗
   □ (∀ ep, A ep -∗ servesAt γ ep)`.
3. **`reqRight` in `AttemptTriple`/`uiOk_call` (P-F7)**: done. Both take `reqRight γ rq`; the
   attempt gives it back in its unfired outcome (3); the interceptor spends it.
4. **otelgrpc gives `statsOk` (C-F2)**: done. New trust-boundary specs
   `Spec/go_opentelemetry_io/contrib/instrumentation/google_golang_org/grpc/otelgrpc/{NewClientHandler,
   NewServerHandler}.lean` (namespace `OtelGrpc`): `Grpc.statsOk h`. The `dialOptsOk` docstrings no
   longer wait on a chain model: 2a's pass-through chains, stats handlers and context dialers are
   neutral on `DialCfg`, so `dialOptsOk_neutral` covers Kubernetes' options. The gRPC proxy's replacing
   `With*Interceptor` stay uncovered.
5. **`clientConnOk` gives `c.conn`**: done, `clientConnOk_conn.spec` (`client/v3/Api.lean`).
6. **Stale `retryKVClient__RangeStream` note**: dropped. 2a's `rangeStreamSpec` carries `lo`.
7. **`Sprintf("%+v", md)`**: done, `Spec/fmt/Sprintf_md.lean` (assumed): `sl ↦*{dq}
   [MD map m] ∗ Grpc.mdAt m dm md` gives `s = Fmt.printMD md` (`printMD_inj` in `fmt/Api.lean`).
8. **`Proto.norm` survival**: W0 has no relation over `Proto.Content`; 3h realizes `Wire.lean`'s
   predicates through its own `*Holds` relations, covered by its `holds_norm` (requests under
   `endsOk`). `Wire.lean`'s header now says so; the client keeps `endsOk` by `OpM.emptyEnd`
   and `Cmp.WithRange`'s premise; `cloneCompare`'s sketch cites `Proto.Clone`'s `norm`.

Second-pass build: `etc/specs-build.sh --dir` `api/v3`, `fmt`, `otelgrpc`, `client/v3` (with
`credentials`, `kubernetes`, `concurrency`, `leasing`, `recipes`), `etcdserverpb`, `auth`: OK (760
modules). `api/v3rpc` not checked: it reaches backend-schema's `storage/schema/Api.lean`, which fails
to parse at line 617 (that group's work in progress). Snippets vet- and gofmt-clean.
