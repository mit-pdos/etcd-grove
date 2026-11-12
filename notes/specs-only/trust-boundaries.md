# The trust boundaries on `examples/etcd/txnlin`'s path, and how to remove them

Research note, 2026-11-10 (specs-only at `ebffb85195`). The question: what must be proved, or replaced
by a justifiable trusted model, for an **axiom-free adequacy theorem of `examples/etcd/txnlin` with
crashes** (one member, one client, `lintest.Run` and porcupine, `top.md` §2 and K6). The answer is
per Go package below, followed by the escalation list (§4).

## 1. Method, and how far to trust the numbers

* **Trusted spec**: a `SpecPlan/Spec/<pkg>/<fn>.lean` whose function has no translated body (its package's
  `Code/<pkg>.toml` `translate` patterns exclude it: names- or types-only), or whose header says
  "trusted"/"assumed" (a `TrustedCode` model or a package Perennial does not translate). A **trusted
  law** is a `def … .spec` in the `Api.lean` of a package whose vocabulary is itself assumed (grpc,
  net/http, proto, WAL, snap, zap, ...). The laws of verified packages (raft's 116, mvcc's 57, ...)
  are obligations the package proves, so they are not counted.
* **On txnlin's path**: a Rapid Type Analysis call graph (`golang.org/x/tools/go/callgraph/rta`) of
  `txnlin.Main` plus every package initializer, with the pinned modules (`examples/go.mod`). It
  walks only through functions **translated with bodies**. A trusted spec counts as on the path when
  it names a function that translated code calls, statically, or dynamically through an interface
  whose concrete types RTA finds live. RTA over-approximates dynamic dispatch, and it misses calls
  made through a names-only function, which is right here: those calls are inside that function's
  trusted spec. Read the per-package counts as ±20%.
* **Totals.** The Spec tree has **536 trusted function specs** for all users (k8s, leasing,
  concurrency, cache, ...). About **239** of them are on txnlin's path. The assumed vocabularies add
  about **172 trusted laws** (grpc 58, net/http 31, proto 14, snap 14, WAL 12, peer 6, semver 5,
  otel/trace 5, fmt 4, v2stats 4, v3alarm 4, leasehttp 4, zap 3, rate 2, bcrypt 1, storage 5).
  Package initializers are a further category (§3.4): 348 generated `PkgInit` modules, and 62 specs
  that state an `X.init.spec`.
* **For comparison**, the old proof's closed theorem (`specs-ref`, `etc/tcb-collections/linkvtxn.txt`,
  no crashes) rested on 605 axioms, none of them `sorry`s: 64 `opaqueInitsOk`, 35 `initFuncsOk`, about
  120 variable-initializer axioms, and the rest function specs and boundary predicates (the same
  packages as below, without the WAL or the snapshotter).
* **What txnlin exercises.** One member of a new cluster. `NewCluster`, no TLS, no auth (token type
  `""`, so the nop provider), auto-compaction off, no peers (rafthttp is constructed but sends
  nothing), `MaxSnapFiles = MaxWALFiles = 0` (purge off), corruption checks off, no downgrade, no
  tracing, `zap.NewNop()`, a disk snapshot every `DefaultSnapshotCount` entries. Under crashes: the
  restart path of `bootstrap` (WAL `Open`/`ReadAll`/`Repair`, `Snapshotter.Load`, backend
  recovery, `RaftCluster.Recover`).

Routes: **(a)** prove from Goose's translation (translate the bodies first if they are names-only
now); **(b)** a trusted model at a narrower interface, which the table names; **(c)** hard: no proof,
and no small or obviously faithful model.

## 2. Per-package tables

Columns: **spec**: trusted function specs in `SpecPlan/Spec/` (all users) / on txnlin's path; **ex.**:
whether txnlin's run actually executes them (yes, start-up only, restart only, or no: present in the
code, branch not taken under its configuration, so the proof needs only that the branch is not
taken, and no spec); **effort**: S, M or L.

### 2.1 etcd's own code that is names-only today (route a)

| package | what | spec | ex. | route | effort | blocking features / notes |
|---|---|---|---|---|---|---|
| `etcdserver` | the server (names-only part) | 34 / 13 | yes | a | **L** | `bootstrap` (789 lines, every start and restart: dirs, backend open/recover, WAL create/open/replay, snapshot load, membership; JSON of members, §2.4); `publishV3`, `monitorClusterVersions`, `monitorStorageVersion` (run once each: version set, schema migration); `adjustTicks`; `monitorFileDescriptor` (reads `/proc/self/fd`, §2.5); `newCorruptionChecker`, `monitorKVHash`/`CompactHash` (off: return at once); `purgeFile` (off); `stopWithDelay` (no). No reflection or unsafe in the package. The HTTP paths (`isMemberBootstrapped`, `GetClusterFromRemotePeers`) are not taken for a one-member new cluster. |
| `storage` (serverstorage) | raft's `Storage` over the WAL and snapshotter | 12 / 10 | yes | a | S | Thin wrappers (`Save`, `SaveSnap`, `Sync`, `Release`, `Close`); proved once the WAL is. `MinimalEtcdVersion` is not taken (downgrade only, `schema.go:69-70`). |
| `storage/wal` | the write-ahead log | 0 fn + 12 laws / all | yes | a, with OsFs (b) and a premise (c) | **L** | Fully names-only (`wal.toml`). The Go is translatable (no reflect, no unsafe; one `filePipeline` goroutine, `file_pipeline.go:55,90`). It needs a directory-aware OsFs and a CRC premise (§4, E4/E5). `walpb.Record` is protobuf (§2.3). crc32 is stdlib with assembly: model it as a pure function. `version.go` walks protobuf descriptors by reflection (`visitMessage`, `version.go:170-190`), but only on downgrade, which txnlin never does. |
| `api/snap` | snapshotter | 7 / 5 | snapshots, restart | a + OsFs (b) | M | `.snap` files (protobuf `snappb`, crc32), `ReadDir`, `Rename` of `.snap.db`; the same OsFs needs as the WAL. |
| `api/membership` | cluster membership | 15 / 11 | yes | a + JSON (b) | M | Plain Go, except `json.Unmarshal(cc.Context, m)` (`cluster.go:376`), run when the bootstrap conf change is applied (§4 E3). |
| `storage/schema` | buckets, members, conf state | 18 / 7 | yes | a + JSON (b) | M | `MustUnsafeSaveConfStateToBackend` = `json.Marshal(*raftpb.ConfState)` (`confstate.go:30`), on the commit after a conf change (`hooks.go:50`); members as JSON (`membership.go:52,101`), read again on restart. |
| `storage/backend` | bbolt wrapper (names-only part) | 17 / 6 | partly | a | M | `Snapshot` (when a snapshot is sent to a follower: no), `Defrag` (no), `Hash` (corruption check: off), `VerifyBackendConsistency` (start-up). bbolt itself is proved (bodies; 2 trusted specs: `Options`, `splitThreshold`). |
| `storage/mvcc` | hashers | 14 / 5 | start-up | a | S | `kvHasher` over crc32 (pure model). |
| `lease` | lessor (names-only part) | 8 / 6 | yes | a | M | `NewLessor`, `Promote`, `Stop`, the checkpoint scheduler: goroutines and timers (Perennial's `time`). |
| `v3alarm`, `v2stats`, `config`, `features`, `api/version`, `txn` (metrics helpers), `leasehttp` | small helpers | 3/3, 6/6, 4/2, 1/1, 2/2, 4/4, 2/1 | yes | a | S | `v2stats.JSON()` uses encoding/json, but txnlin never calls it. `features` goes through `pkg/featuregate` (`atomic.Value` of maps; translatable). `version` goes through semver (§2.4). `leasehttp` is HTTP, never called. |
| `api/v3rpc` | gRPC services (names-only part) | 16 / 3 | partly | a | S | `logUnaryRequestStats` (`proto.Size`, fmt). The cluster and maintenance servers are not called by txnlin. |
| `api/rafthttp` | peer transport (names-only part) | 5 / 4 | constructors only | a + net/http (b) | S for txnlin | `NewRoundTripper`/`newStreamRoundTripper` build `http.Transport`s; `addPeerToProber`/`waitSchedule` run per peer, and there are none. |
| `auth` | auth store (names-only part) | 6 / 5 | no (auth off) | a | S | `newTokenProviderJWT` (golang-jwt: reflection/crypto) is not taken (token type `""`). bcrypt is the opaque `pwHash` (`open-questions.md` 5.7). |
| `api/v3/etcdserverpb` | generated stubs and handlers | 58 / 28 | partly | a | S–M | The `_Auth_*`, `_Cluster_*`, `_Maintenance_*` handlers and client stubs are generated code with no reflection: translate them (`open-questions.md` 7.4). The `*.String()` methods and `NewLoggableTxnRequest` go through `protoimpl.X.MessageStringOf`: give them a trusted "some string" model (they feed logs only). |
| `client/v3` | client (names-only part) | 132 / 12 | partly | a | M | Most of the 132 serve other users (leases, watch, auth, cluster, maintenance). On the path: `dialWithBalancer`/`dial` (into grpc, §4 E1), `Close`, `Sync`/`checkVersion` (off by configuration), `WithRequireLeader`, `NewCluster`/`NewMaintenance`. |
| `client/v3/internal/resolver`, `credentials`, `client/pkg/{types,transport,logutil,verify}`, `pkg/{httputil,idutil,traceutil,adt}` | client and pkg helpers | 3/2, 3/2, 7/4, 2/1, 1/1, 1/1, 1/1, 1/1, 2/1, 1/0 | yes | a | S | The resolver wraps grpc's `manual.Resolver` (`resolver.go:37-49`) and uses `recover()` (`getCC`, `resolver.go:78-85`; Goose supports it); its spec really sits on the grpc model. `logutil.CreateDefaultZapLogger` goes through `zap.Config.Build`, which txnlin passes its own logger to avoid. `idutil` has an unavoidable premise (§4 E6). |

### 2.2 Perennial already models it (cheap)

| package | spec | route | effort | notes |
|---|---|---|---|---|
| `sync`, `sync/atomic`, `time`, `context` (constructors), `strings`, `strconv`, `errors`, `fmt` (`Sprintf`/`Errorf` trusted), `sort`, `slices`, `os` (this repo's `TrustedCode/os.lean` + OsFs), `runtime` (GOOS/GOARCH), `goose-lang/primitive` (prophecies) | Perennial's own (W0's `SpecPlan/Spec/context` 27 laws are realized from `Perennial.Proof.context`) | Perennial | S | Gaps that need Perennial changes, recorded in `open-questions.md` §7: `context.WithValue` is not translated (excluded for `reflectlite` in `stringify`, `Perennial/Code/context.toml`), and grpc's metadata contexts and `WithRequireLeader` need it; a functional `sort.Sort` spec (7.1); slice-length bounds (7.2); `strings.ToLower`, `sort.SliceIsSorted`, `reflect.DeepEqual` (bbolt's local axioms, `notes/perennial-changes.md`). |
| `bbolt`, `bbolt/internal/{common,freelist}` | 2 / 1 | a (done) | — | Proved with bodies, over the OsFs extension (mmap, pread/pwrite, fsync). Its crash argument has the no-checksum-collision premise P1 (`notes/osfs-ext-plan.md` D1/D9). |
| `porcupine`, `lintest`, `etcdstart`, `txnlin` | no specs on this branch | a | **L** (porcupine's checker) | Translated with bodies, nothing trusted. Porcupine's spec (never `Illegal` when a linearization exists) is a substantial proof. It is not a trust boundary, but it is on the critical path. |

### 2.3 Third-party libraries (route b, a trusted model)

| package | what | spec | ex. | route / the narrower interface | effort | blocking features |
|---|---|---|---|---|---|---|
| `google.golang.org/grpc` (+ `internal/transport`, `balancer`, `resolver`, `x/net/http2`) | RPC | 36 / 18 (+58 laws) | yes | **b**: a model of the RPC API (`NewClient`/`Invoke`/`NewStream`, `NewServer`/`RegisterService`/`Serve`, interceptor chaining), the `UnarySpec`/`StreamSpec` contracts of `SpecPlan/Spec/google_golang_org/grpc/Api.lean` as a GooseLang extension or `TrustedCode` over a message-passing network | **L** | §4 E1 |
| `grpc/{status,codes,peer,metadata,health,health/grpc_health_v1,credentials/insecure,grpclog}` | small grpc packages | 6/2, —, 2/1, 10/5, 2/2, 2/2, 1/0, 1/0 | yes | metadata, peer, health: **a** (plain Go: maps, `context.WithValue`, a mutex). status: **b** (it wraps a `spb.Status` protobuf). insecure, grpclog: **b** trivial | S | `status.FromError` uses `errors.As` plus a `GRPCStatus()` interface; health's messages are protobuf. |
| `google.golang.org/protobuf/{proto,internal/impl,runtime/protoimpl,reflect/protoreflect}` + the generated `*.pb.go` of etcdserverpb, mvccpb, authpb, membershippb, raftpb, leasepb, walpb, snappb, health_v1 | protobuf | 6 / 5 (+14 laws) | yes (every WAL record, raft entry and message, backend value, RPC) | **b**: `Marshal`/`Unmarshal`/`Size`/`Clone`/`Equal` over the abstract `Proto.Content` of each message type (the existing `SpecPlan/Spec/google_golang_org/protobuf/proto/Api.lean`), plus the generated packages' init | **L** | §4 E2 |
| `encoding/json` | JSON | — (inside schema/membership specs) | yes | **b**: one encode/decode model per type used (`Member`, `RaftAttributes`, `Attributes`, `ConfState`, the conf-change context) | M | §4 E3 |
| `go.uber.org/zap`, `zapcore` | logging | 32 / 24 (+3 laws) | yes (`NewNop`) | **b**: a logger that has no effect, except `Panic` (panics after the hooks) and `Fatal` (ends the run: `logger.go:350-351`, `WriteThenFatal` even on a Nop core); `Named`/`With` return a logger of the same kind | S | `zap.Any` falls back to `Reflect` (`field.go:490,326`), `runtime.Callers` for callers and stacks, `sync.Pool`, atomics: none of it matters to a model with no effect. A real logger needs the claim "a log line has no effect on the program's state", which is easy to justify. |
| `prometheus/client_golang`, `go-grpc-middleware/providers/prometheus` | metrics | provisional (`ApiBoot.lean:526`; no `SpecPlan/Spec/` dir) | yes (110 `MustRegister` in server `init`s, an observe on every request) | **b**: write-only sinks, plus a registry of names (a `MustRegister` of a taken name panics); the interceptors run the handler once and return its result | M | Float CAS loops (`atomicUpdateFloat`), xxhash (unsafe), the default registry's Go and process collectors (registered in `init`; `Gather` is never called by txnlin). The real work is the per-package `init` facts: names distinct across ~15 packages. |
| `go.opentelemetry.io/otel/{trace,attribute}`, `otelgrpc` | tracing | 2/2, 4/4, 2/1 (+5 laws) | `SpanFromContext` yes (noop span); otelgrpc no (tracing off, `v3rpc/grpc.go:67`) | **b**: a noop tracer; `attribute.*` are pure | S | Global provider through `atomic.Value` and `sync.Once`; never configured (`open-questions.md` 5.9). |
| `Masterminds/semver/v3` | versions | 7 / 6 (+5 laws) | yes (constants: `MustParse("3.6.0")`, ...) | **b**: a pure parse/compare model | S | `regexp.MustCompile` in the package's var init (`version.go:84-85`); regexp is untranslated stdlib. |
| `golang.org/x/time/rate` | rate limiter | 5 / 3 (+2) | no (rafthttp peers only, `peer.go:216`) | b | S | float64 token arithmetic. |
| `golang.org/x/crypto/bcrypt` | passwords | 2 / 2 (+1) | no (auth off) | b (the opaque `pwHash`/`pwMatch`, 5.7) | S | blowfish. |
| `xiang90/probing`, `dustin/go-humanize`, `jonboulle/clockwork` | small helpers | 2/1, —, — | constructors only | a (probing, clockwork: small Go over net/http and time) / b (humanize: float formatting for logs) | S | — |
| `net/http` (+ `net/http/internal/http2`, `net/textproto`, `crypto/tls`) | HTTP | 14 / 7 (+31 laws) | constructors only (no peers; etcdstart serves no peer handler) | **b**: the existing request/response boundary (`SpecPlan/Spec/net/http/Api.lean`), realized as a model over a TCP-like extension | S for txnlin, **L** for multi-member | §4 E7 |
| `net` (`Listen`, `Accept`, `Dial`) | sockets | (in grpc/http specs) | yes | **b**: a connection-oriented network extension (Perennial's Grove has `Listen`/`Connect`/`Accept`/`Send`/`Receive`; its Net extension is a toy) | M | — |
| `hash/crc32`, `hash/fnv` | checksums | — | yes (WAL, snap, mvcc hash; bbolt meta) | **b**: pure functions (FNV-64a is already modeled in Lean for bbolt) | S | crc32 dispatches to SSE4.2/CLMUL assembly. |

### 2.4 Environment premises (hypotheses of the adequacy theorem, not axioms)

These stay as hypotheses whatever is proved, and each is a fact about the world: `ServerStorage.diskOk`,
`Wal.crashInScope` (`Recs.crashScopeOk`), OsFs's environment (a local ext4/xfs, sector-atomic
writes, `RLIMIT_FSIZE`), `addrFree` (one reserved string per socket), `Grpc.msgsFit` (no message over
`2^48`: `issues/grpc-codec-alloc-before-size-check.md`), `EnvCfg.leaseExpiry = false` (no lease
granted by txnlin, so it is vacuous here), the handler-pool bound (`open-questions.md` 5.5), bbolt's
P1. E5 and E6 add two, and E4 decides the shape of the crash premises.

### 2.5 OsFs extension work the path needs (trusted, this repository's)

The extension models regular files of a fixed domain, and opening any other path is stuck
(`GooseLang/Ext/OsFs/Impl.lean` header; D4: no directory fsync primitive). txnlin with crashes also
needs:

* directories: `MkdirAll`, `ReadDir`/`Readdirnames` (`fileutil/read_dir.go:44-54`), `Remove`,
  `Rename` (`wal.go:286,306,329,875`; the snapshotter's `.snap.db` rename), creation with `O_EXCL`,
  and directory fsync (`wal.go:225,879`);
* `fallocate` (`fileutil/preallocate_unix.go:27`, at `wal.Create` and in the file pipeline) and OFD
  locks (`fileutil/lock_linux.go:66,87`, `FcntlFlock(F_OFD_SETLK[W])`; a trivial model, as bbolt's
  D7 `Flock`);
* paths outside the data directory: `/proc/self/fd` (`pkg/runtime/fds_linux.go:31-45`, read every 10
  minutes by `monitorFileDescriptor`, `etcdserver/metrics.go:215-240`) and `getrlimit`. An arbitrary
  count or an error is a faithful model;
* the crash relation of all of the above: E4.

## 3. Cross-cutting

1. **Package initializers.** Every package in the closure runs its initializer before `Main`
   (`isPkgInit`). A names-only package's variable initializers become trust points: in the old tree,
   64 `opaqueInitsOk`, 35 `initFuncsOk` and about 120 `X_init` axioms. To remove them, translate the
   initializers and prove them against the models above: `prometheus.NewCounterVec` and
   `MustRegister` (metrics), `status.Error(codes.X, …)` (rpctypes' error vars), `errors.New`,
   `regexp.MustCompile` (semver), and the generated pb packages' `file_*_init` →
   `protoimpl.TypeBuilder.Build()` (protobuf: E2). This follows from the models chosen and needs no
   new kind of trust, but it is a large amount of work.
2. **Crashes kill the client too.** txnlin's client and server share one process, so after a crash
   only the history before the crash and the restarted member's durable state survive. What the
   porcupine check means across a crash (which Main is the recovery procedure; whether operations
   pending at the crash are linearized) has to be stated before the adequacy theorem can be.
3. **Untranslated but unexercised code** (JWT, TLS, the v2 store, discovery, `v3discovery.JoinCluster`,
   downgrade's descriptor walk, `rate`, the corruption checker's HTTP and JSON) needs no model. The
   proof needs only that txnlin's configuration does not take the branch, which every spec above can
   state as a premise the configuration discharges.

## 4. Escalation list (concrete examples)

**E1. grpc-go: a large trusted model, at the RPC API (route b, L).** Translating it is not an
option. `internal/transport` (`http2_client.go`, `http2_server.go`) is an HTTP/2 implementation over
`golang.org/x/net/http2`'s framer and hpack, with flow control, a loopy writer
(`controlbuf.go:595`, 3 `select` loops), keepalive pings, GOAWAY handling, and 6–7 `select`s per
file. The client side is a resolver → balancer → subconn graph with callback serializers (etcd asks
for `round_robin` through a JSON service config, `client/v3/internal/resolver/resolver.go:44`).
`RegisterService` checks the implementation by reflection (`server.go:780-781`). Handlers run on
per-stream goroutines (`server.go:1095-1107`) through `md.Handler(srv, ctx, df, interceptor)`
(`server.go:1284`). A model needs only what txnlin reaches: unary calls on one in-process
connection, interceptor chains, deadline propagation, metadata, and status errors. The
questionable part is the faithfulness claim the whole linearizability argument hangs on (K4,
at-most-once): **an attempt runs its handler at most once**. In grpc-go that rests on a two-sided
HTTP/2 argument. The client retries an attempt transparently only when the stream was
"unprocessed" (`stream.go:800-818`: `cs.firstAttempt && unprocessed`), and "unprocessed" is set on
`RST_STREAM(REFUSED_STREAM)` or on a GOAWAY above the stream id (`http2_client.go:1296-1302`, also
`:821`, `:1447`). The server sends `REFUSED_STREAM` only before dispatch (`http2_server.go:552-557`,
the `maxStreams` check). The model would also assume that keepalive closures and connection
failures surface as indefinite errors, that a deadline reaches the server as a context deadline,
and that there is no service-config retry policy. **Decision needed**: accept a trusted grpc model of
this shape (it is the shape of the current `Grpc` specs: Grove's urpc, with a resource attached to
each call), and say what it must cover beyond txnlin (streams: Watch, LeaseKeepAlive; multiple
endpoints; TLS).

**E2. protobuf-go: a model per message type (route b, L, questionable without a generator).**
protobuf-go is reflection and `unsafe` throughout. A generated message's `ProtoReflect` reaches its
state through `protoimpl.X.MessageStateOf(protoimpl.Pointer(x))` (`etcdserverpb/rpc.pb.go:801-812`).
Field access is by `unsafe.Pointer` offset (`internal/impl/pointer_unsafe.go:18-47`). Each type's
coders are built lazily by reflection over struct tags behind an atomic flag and a mutex
(`MessageInfo.init`/`initOnce`, `internal/impl/message.go:66-95`; `fieldInfoForScalar` uses
`reflect` and `offsetOf`, `message_reflect_field.go:252-275`). Each pb package's initializer runs
`protoimpl.TypeBuilder` over a raw descriptor. A Lean model of `proto.Marshal`/`Unmarshal`
(`proto/encode.go:105`, `decode.go:61`) is feasible, but its meaning must be the wire format **of
each message type**: about 150 types in etcd, raft and the WAL, including the presence rules that
`Proto.norm` encodes. txnlin needs it for every WAL record (`walpb.Record`), raft entry, message and
hard state, `InternalRaftRequest`, `mvccpb.KeyValue` in the backend, and every RPC. Written by hand,
these models are a large trusted surface in which a wrong field number or presence bit goes
unnoticed. **Proposal to decide**: a trusted generator (like Goose) from the `.proto` descriptors to
Lean content types and encoders. The trust would then be "protobuf-go implements proto3's wire
format for these descriptors", which the protobuf conformance suite tests. The `String()` methods
(prototext, through reflection) get a "some string" model.

**E3. encoding/json on exercised paths (route b, M).** `encoding/json` is reflection
(`decodeState.value(reflect.Value)`, `$GOROOT/src/encoding/json/decode.go:364`; `Marshal`,
`encode.go:204`). txnlin's run hits it three times:

* `schema.MustUnsafeSaveConfStateToBackend` = `json.Marshal(confState)` of a **protobuf-go**
  `*raftpb.ConfState` (`storage/schema/confstate.go:30`), on the backend commit after each conf
  change (`storage/hooks.go:50`, translated, so this is the boundary);
* `json.Unmarshal(cc.Context, m)` of the member when the bootstrap `ConfChangeAddNode` is applied
  (`membership/cluster.go:376`; its context comes from `json.Marshal` at `bootstrap.go:549`);
* the members in the backend (`schema/membership.go:52,101`), read again by `RaftCluster.Recover`
  on every restart.

A per-type model (encode, and `Unmarshal ∘ Marshal = id` on these five types) is small. It is still
a model of reflection keyed to struct tags and to which fields are exported. On `ConfState` that
means: skip `state protoimpl.MessageState`, `sizeCache` and `unknownFields`. Every new type needs a
new model. The alternative is a general reflection model in Perennial (large). Not a hard blocker;
listed because it is a new kind of trusted model.

**E4. Directory crash semantics (route c until chosen).** The WAL creates its directory as
`member/wal.tmp` and renames it into place, with a parent fsync (`wal.go:306`, `:225`). It renames
a cut segment's temp file (`:875`, then a dir fsync at `:879`). The snapshotter renames `.snap.db`
onto the backend's path. bbolt creates the backend file with no directory sync. Whether
`EtcdServer.disk_crash` is **true** depends on the crash model chosen for directory entries
(rename atomic but not durable without a dir fsync; a create not durable until synced).
`top.md` K6 records three open items: `nonissues/etcd-backend-name-lost-restart-panic.md` (the
first boot's backend name may vanish, and a later restart panics),
`nonissues/etcd-member-dir-not-synced.md` (`member/` is never synced), and open question D7. No
proof can settle this. It is a choice of trusted OsFs semantics plus either a premise or a fork fix,
and the user has to make it before the WAL's crash laws can be proved.

**E5. The WAL's torn-tail detection rests on CRC-32 (route c: an environment premise).** After a
crash, `ReadAll` tells a torn last record from corruption only when the record's CRC fails and the
data looks torn: `rec.Validate(d.crc.Sum32())`, then `isTornEntry` → `io.ErrUnexpectedEOF`
(repairable), otherwise `ErrCRCMismatch` (fatal) (`storage/wal/decoder.go:133-150`). After a
`Repair` truncates, the segment's later bytes are rewritten in place. A crash during the rewrite can
then mix new and old non-zero sectors. That is correctly refused only if the chained CRC never
matches by accident. A deterministic model cannot prove this; it is the analogue of bbolt's P1 (a
no-checksum-collision premise). It should be stated as part of `Wal.crashInScope`, explicitly.

**E6. Request-id freshness across a restart (route c: a premise about time).**
`idutil.NewGenerator(memberID, time.Now())` seeds the 40-bit suffix from milliseconds, shifted by 8
(`SpecPlan/Spec/go_etcd_io/etcd/pkg/v3/idutil/Api.lean`). Ids are fresh across a crash only if the previous
run issued fewer than 256 ids per millisecond of its life (`nonissues/etcd-request-id-restart-reuse.md`,
`open-questions.md` 5.6). With crashes this is on txnlin's path: the wait registry and the apply
thread key results by id. It can only be a premise about the clock and the request rate.

**E7. net/http, deferred (route b, L when needed).** txnlin needs only its constructors. Any
multi-member result needs the request/response boundary (`SpecPlan/Spec/net/http/Api.lean`) realized over a
TCP model. Translating `net/http` is out of reach: persistent-connection goroutines
(`persistConn.readLoop`/`writeLoop`), the bundled HTTP/2 (`net/http/internal/http2`, 88 functions
reached), textproto, mime, TLS.

## 5. Ranking

* **Cheap (modeled already, or a small model)**: Perennial's stdlib; zap (Nop); otel (noop); grpclog,
  insecure, status, peer, metadata, health; semver, rate, bcrypt, humanize, probing, clockwork;
  crc32/fnv; the generated `String()` methods; `/proc` and locks in OsFs; `context.WithValue` in
  Perennial; bbolt (done).
* **Medium**: etcd's names-only code outside `bootstrap` (membership, schema, lease, alarm, v2stats,
  backend snapshot/hash, mvcc hashers, the pb handlers, the client's dial, the storage wrapper, the
  snapshotter); prometheus (sinks plus a name registry); encoding/json per type (E3); OsFs
  directories, rename, fallocate (the mechanics; the crash model is E4); the package-initializer
  proofs.
* **Large**: `bootstrap` + the WAL with crashes; the grpc model (E1); the protobuf model or generator
  (E2); porcupine's checker proof (not trusted, but on the critical path); net/http (E7: not needed
  by txnlin).
* **Escalation (needs the user)**: E1, E2 (shape and trust of the two big models); E3 (accept
  per-type reflection models); E4 (directory crash semantics, plus the backend-name and `member/`
  sync choice); E5 and E6 (two new explicit environment premises).

Counts of txnlin's ~239 on-path trusted function specs by route: **(a) ≈ 158** (etcd's own
names-only code, the generated pb stubs and handlers, and grpc's plain-Go metadata, peer and health),
**(b) ≈ 81** (grpc core 18, zap 25, proto 5, net/http 7, semver 6, otel 7, rate 3, bcrypt 2, status
2, raftpb `String` 3, sort 1, ...). No spec count is in **(c)**: the (c) items are semantics and
premises (E4, E5, E6), and the internals of grpc-go and protobuf-go, which only route (b) can reach.
The trusted laws (~172) follow their packages: grpc 58 and net/http 31 go with E1/E7, proto 14 with
E2, WAL 12 and snap 14 with E4/E5.
