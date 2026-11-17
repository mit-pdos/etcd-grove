# Porting dsverify-lab onto etcd-grove's network semantics (plan, for review)

Plan, 2026-11-17, **nothing here is built**. The user's request: port dsverify-lab's network kits to
etcd-grove's network semantics (`GooseLang/Ext/Tcp`, v3.2), copying what we need from dsverify-lab
into etcd-grove, so that there is **one general-purpose model of `net/http` and gRPC** (and
`net/rpc`, the codecs) used both by etcd and by the dsverify examples.

Sources read (2026-11-17): dsverify-lab at GitHub `master` `348a866` (the local clone's `master`,
`c9a88f9`, is older and has none of the network work: `git fetch` first); here, `lean` at
`3e38269e20`; `notes/net-tcp.md`, `notes/net-tcp-dsverify-{survey,final}.md` (the two semantics
compared, 2026-11-14/15), `notes/specs-only/tcp-extension-design.md` (option B, accepted 2026-11-12),
`notes/robustness.md`. dsverify-lab paths below are relative to its root (`D/`), Lean ones to
`D/harness/lean/Harness/`.

## 1. What each side has

| | dsverify-lab (`348a866`) | etcd-grove (`lean`) |
|---|---|---|
| TCP semantics | `GooseLang/Ext/NetConn/Impl.lean` (393 lines): global listeners with pending lists, two streams per connection, a break cuts both, `Write` one step, only Read/Accept wait, no crashes (`crash := id`) | `GooseLang/Ext/Tcp/Impl.lean` v3.2 (609): plan address → host, per-direction cuts, `Write` Go's loop of steps (D15), every op may stutter (D22), node-local crashes, `CloseWrite` |
| `net` | `TrustedCode/net.lean` (631), `Code/net.toml`; errors a model-only `connError` in a real `*OpError` (refutable by a type assertion: survey S1); `"tcp4"`, socket options (`SetKeepAlive*`, `Set{Read,Write}Buffer`) | part `NetTcp/` (`NetTcp/TrustedCode/net.lean`): Go's real error values (`poll.ErrNetClosing`, `*os.SyscallError`, ...); `"tcp4"` and socket options **not modeled** (panic / names only) |
| specs over it | `Specs.lean` (1891), `Spec/net` + `Proof/net` (2500): Hoare triples over `addrProto a P Q`, `sendTok`/`recvTok`, `connEnd`, `newConnResult`, `connErr code err` | `Ghost.lean`, `Specs.lean` (1159): logically atomic over `tcpEnd`/`tcpDir`/`tcpPend`/`tcpLis`; proved stream protocol `wire/Stream.lean` (`dirInv`, `sentLb`) |
| evidence | `harness/netsem` (Go per decision), `harness/conform` (uncertified Python checker; found F1-F3) | `examples/net/semantics/` (`doc.go`, ~45 rows), `Tests.lean` (68), conformance checker with verdicts certified in Lean (`nettcp-replay`) |
| net/rpc | Go model, `rpcmodel/src/net/rpc` (518 lines, own framing after Go's CONNECT handshake), codec + dispatch generated per kit (`kitgen/rpcgen.py`); `Proof/net/rpc` 5318 lines, 0 axioms | none (etcd does not use it) |
| net/http | Go model, server + `ReadResponse` subset (`rpcmodel/src/net/http`, 324 lines); `Proof/net/http` 1418, 0 axioms | 34 axioms over opaque `httpProtoAt`/`respReader`/... (`Proof/net/http/Axioms.lean`, `Boundary.lean`); option B's model sketched only |
| gRPC | Go module `google.golang.org/grpc` with v1.84's API, **unary only** (`rpcmodel/grpc`, 769 Go lines), own framing multiplexed by sequence number on one connection; `Proof/grpc` 5619 lines, 0 axioms; differential tests against real grpc (`grpcdifftest`) | ~93 axioms (`Proof/google_golang_org/grpc/`: `Invoke`, `NewStream`, `grpc.start`, option constructors, ...) over opaque `grpcAddrIs`/`grpcConn`/stream mono lists; unary and streaming; option B's model sketched only |
| codecs | protobuf: per-kit generated plain marshal code (`kitgen/pbgen.py`, `harness/pbcodec`) proved against `PbCodec`; JSON: `jsongen.py` + `harness/jsoncodec`; gob: names-only plus a model for swift | protobuf: `pbEncC` + per-type registration axioms (`InvProto.lean`); E2 decided (b): a trusted per-type model generated from `.proto` files (not built); E3: a trusted per-type JSON model (not built) |
| statement | `SafeDist nodes cfg` (`SafeDist.lean:236`), `NetConfig.WellFormed` (decidable), over `goose_dist_adequacy` (no crashes); `driver_dist_safe` (`Driver.lean:589`); goal checked by `goal-check.sh`, `goal-axioms.sh` | `<ex>_crash_safety` over `goose_dist_crash_adequacy`, premise `PlanWellFormed` (`Deploy.lean`); `Robustness/` (`Robust`, `StreamNet`) not yet instantiated |
| deployment test | `harness/rig` (one netns per node, veth, tc/iptables faults) | `examples/lib/robust` (namespaces behind a router, netem, kills, dm-flakey), `examples/net/internal/proctest` |
| build | plain `lean` + `LEAN_PATH` (`build.sh`), Perennial `4c8617a`, Lean v4.34.1, module system (yes), roots `Harness.*`; goose with a GOROOT symlink farm (`rpcmodel/goroot.sh`) and `go.model.mod` replaces | Lake, Perennial `e9e6351d9`; `etc/goose.py` projects, parts, `-lean-root` |

Verified dsverify network kits (each `theorem goal : SafeDist (clientNode :: serverNodes) <kit>Cfg`):
paxos-net-3 (raw TCP), craq-net-2 (net/rpc over http, gob), epaxos-net-1/-2 (raw TCP + bufio, master
net/rpc), gryff-net-2 (raw TCP + bufio, net/rpc), quepaxa-net-2 (gRPC unary + protobuf, raw TCP
clients), rabia-net-1 (raw TCP + gogoproto), vsr-net-1 (raw TCP + JSON). Running: epaxos-star-net-1,
swift-net-1. The kits' full proofs are not in the lab repository (`theorems/<run>/` keeps `Goal.lean`
and `axioms.txt`); they are in the runs' homes on the experiment machines (`fk-lean1`, `fk-lean2`).

The point of the plan: the two halves fit. etcd-grove has the stronger semantics (Go's errors, the
`Write` loop, crashes, certified conformance) and a design for the models but no models; dsverify-lab
has proved, axiom-free, differentially tested models but over a weaker semantics, with a known
unsound point (S1) and no crashes. And etcd's gRPC/http trust base (~130 axioms over ghost state that
is not built) is exactly what proved models over TCP would replace.

## 2. Decisions to take first (the user's)

**Q1. The mechanism for models: patches of the real packages, or substitute packages?**
Option B (accepted 2026-11-12, U2) writes each model as a patch of the real grpc-go / Go `net/http`
source, keeping every type and option (etcd's translated code and its dependencies, `otelgrpc`,
grpc-gateway, the prometheus interceptors, typecheck against the real API). dsverify-lab substitutes
whole hand-written packages (a GOROOT symlink farm, `go.mod` replaces), with only the API its kits
reach. **Recommendation: patches** (`etc/model-patches/<project>/*.patch`, applied by `etc/goose.py`,
with an overlay for the standard library), for all of grpc, net/http, net/rpc, encoding/json and gob;
dsverify's model code becomes the content of the patches' added files (framing, transport, dispatch),
and its differential tests stay. A substitute package cannot serve etcd: its dependency closure
names far more of grpc's API than any kit.

**Q2. gRPC's wire: one stream per connection (option B's U3) or dsverify's sequence-numbered
multiplexing on one connection?** One stream per connection removes stream ids, multiplexing and the
connection pool from the trusted model, lets cmux's `HTTP2()` matcher see the real 24-byte preface,
and makes "at most one dispatch per attempt" a per-connection fact. dsverify's proofs (5.6k lines,
unary) assume its multiplexing and would be adapted. **Recommendation: one stream per connection**;
the unary proofs carry over at the level of `ClientConn.Invoke.spec`/`handlerOk`, and the streaming
half is new work etcd needs anyway (watch, lease keep-alive). net/rpc keeps dsverify's framing (one
connection, sequence numbers: that is net/rpc's own protocol shape, and only kits use it).

**Q3. Where the shared code lives, given dsverify's isolation.** dsverify runs must not see
etcd-grove (`D/README.md`, "How it is isolated"). The shared layer (TCP extension, `net`, the models,
their specs and proofs, the codecs' generators, `SafeDist`) must therefore be a **self-contained unit
importing only Perennial**, which dsverify-lab can take as a Lake dependency or a copied tree without
any etcd content. Options: (a) a part of this repository, say `GoNet/` (modules `GoNet.*`), with an
export script and a leak check (no `etcd`/`raft` module, path or name in the exported tree); (b) a
separate repository; (c) Perennial (its `Ext/Net` is a toy; a real TCP extension and `net` model are
general-purpose, but grpc and net/http models of third-party code are less clearly Perennial's, and
Perennial changes go by its own review). **Recommendation: (a) now, developed here where etcd's
proofs exercise it, with (c) proposed for the TCP extension and `net` once stable** (an entry in
`notes/perennial-changes.md`).

**Q4. Crashes in the kits' statement.** Most kits keep no durable state, so they are not safe under
crash *and restart*; `goose_dist_crash_adequacy` restarts nodes. **Recommendation:** `SafeDist` over
`tcpExt` with `goose_dist_adequacy` (no restart) for the existing kits, as today; a process's death
without restart is already a cut for its peers (D10/D11), so crash-stop of a server is covered by
modelling the server's `main` as possibly exiting (a later strengthening). Crash-restart statements
(over `goose_dist_crash_adequacy`, and later `Robust`) only for kits with durable state.

**Q5. How the kits' proofs are ported.** **Recommendation:** keep the kit-facing spec statements
(Section 3, phase 3) so that each kit's proof ports by changing imports, and re-run a kit as a
continuation run (dsverify's `continue/seed.sh` pattern) only where a statement had to change. The
runs' proofs must first be collected from the experiment machines (phase 0).

## 3. The plan

Each phase lands on `lean` by `etc/land.sh` and records its decisions in `notes/decisions.md`; a
change to the trusted semantics adds its Go example in `examples/net/semantics/` in the same commit
(CLAUDE.md, extensions).

### Phase 0: inventory and copies (small)

- Fetch dsverify-lab, pin the commit we copy from (`348a866` or later) in this note.
- Copy, **as reference material, not built**, into `old/dsverify/` (as `old/bbolt/`, with a README
  naming the commit): `harness/lean/Harness/{GooseLang/Ext/NetConn,TrustedCode/net.lean,Spec/net,
  Proof/net,Proof/grpc,Proof/encoding,Proof/jsoncodec,NetLib.lean,SafeDist.lean,Driver.lean,
  DistLemma.lean}`, `harness/rpcmodel/{grpc,protobuf,src,difftest,grpcdifftest}`,
  `harness/{pbcodec,jsoncodec,kitgen,netsem,rig}`, `notes/{grpc-model,conform,harness-m2-netconn,
  harness-m2a}.md`. Their licence: same authors; say so in the README.
- Collect the verified net runs' work trees (`runs/<run>/home` on `fk-lean1`/`fk-lean2`, the tagged
  `final` commits) into `/shared/dsverify-lab/runs/` here (not into this repository: they are the
  lab's).
- List the `net` API every kit and every model calls (a grep of the kits' patched sources, plus
  etcd-grove's conformance tracer run on the rig), and diff it against `NetTcp`'s modeled set.
  Already known: `"tcp4"` (3 uses), `SetKeepAlive`/`SetKeepAlivePeriod` (7 each), `SetReadBuffer`
  (10), `SetWriteBuffer` (7).

### Phase 1: close tcpExt's gaps for the kits (semantics change, reviewed)

From the comparison (`net-tcp-dsverify-final.md`, "What one admits and the other excludes") and phase
0's list:
1. **`"tcp4"`**: accept it as `"tcp"` with Go's `Net` field `"tcp4"` in errors (dsverify's unsound
   point 2 avoided); evidence row in `doc.go`.
2. **Socket options** (`SetKeepAlive`, `SetKeepAlivePeriod`, `SetReadBuffer`, `SetWriteBuffer`,
   `SetNoDelay`, `SetLinger` if reached): `nil` on an open end, `ErrClosed`-kind error on a closed one,
   no state; keepalive's effect is already covered by cuts. Measured rows.
3. **Go's write lock**: concurrent `Write`s on one end do not interleave (`fd_unix.go:366`). Either
   model it (a lock bit in `TcpEnd`, a `Write` loop holding it) or show the kits never write
   concurrently; needed if a kit's protocol relies on whole frames from concurrent writers.
4. **Wildcard `Listen` with one IP per node** (the rig gives every node its own IP, and kits listen
   on the same port on every node): D21 (`ListenAt`, `Impl.lean:446`) requires the port to be the
   plan's only address with that port, because on one machine a wildcard listener takes every local
   address (`TestAddressAliases`). A kit listening on `":p"` on every node would panic. Make the
   deployment's kind part of the plan (one machine, or one network namespace per host): per host,
   the wildcard resolves to (this node's host, `p`), with the port unique per host only; measured on
   the rig's namespaces (dsverify's `node_identity_netns_test.go` is the evidence to port).
5. **The deployment premise**: map `NetConfig.WellFormed` onto `PlanWellFormed` (dsverify forbids
   127/8, we forbid ephemeral ports); move the kits' configured ports out of 32768-60999 if any are
   there.
Each with its `Tests.lean` example, a conformance run, and the soundness skill (`axiom`) over the
changed rows.

### Phase 2: the shared unit, `GoNet/` (layout and build)

- Create the part (Q3), importing only Perennial: move `GooseLang/Ext/Tcp`, `NetTcp/{Code,
  TrustedCode,GeneratedProof,ManualProof,Spec,Proof}/net`, `wire/` (the proved stream library) and the
  conformance checker into it; the NetTcp examples stay where they are and import it. `etc/goose.py`
  gets the part's projects; `etc/tcb-collections/gonet.txt`; `etc/api/gonet.txt` (the importable
  list, interfaces generated).
- An export script (`etc/export-gonet.sh`) that writes the part as a standalone Lake package (its own
  `lakefile.toml`, Perennial pinned as here) and a leak check that fails on any etcd/raft name; the
  check runs in `etc/gates.sh`.
- dsverify-lab's build (plain `lean`, Perennial `4c8617a`) moves to Lake with the exported package as a
  dependency and our Perennial pin; its `Harness/` keeps only what is lab-specific (`clients`,
  `recorder`, `check`, `models`, porcupine, `driver`, `kitgen`).

### Phase 3: the kit-facing net specs over tcpExt (proved, no trust)

dsverify's kit proofs reach the network only through exported specs (`D/notes/conform.md` L315-337:
the F1-F3 change re-checked every run with no proof change). So prove **those statements** over
tcpExt, in `GoNet/Proof/net/Compat*.lean`, from the logically atomic specs and `wire/Stream.lean`:
`addrProto`, `addrTok`/`addrUnset`, `addr_set_proto`/`addrs_set_proto`, `sendTok`/`recvTok`/`sentLb`,
`connEnd`/`connFresh`, `newConnResult`, `connErr`, and the Hoare triples of `Spec/net/*`. Where a
statement does not hold of the stronger semantics, change it and record which kits it touches:
- `connErr code err`: dsverify's codes (none, EOF, timeout, closed, broken, fail) become tcpExt's
  kinds (`closed | timeout | sys`, EOF separate); the code is existential in the kits' uses, check.
- Facts dsverify's model gives and tcpExt does not: a `Dial` succeeds only with an open listener; a
  read error only after the bytes are drained; no interleaved concurrent writes (phase 1.3). Find which
  kit proofs use them (none expected).
- The plain-Hoare specs are weaker than ours; where a kit shares a connection between threads they may
  not be enough, and the atomic specs are the fallback.
First client: dsverify's `netprobe` (`netprobe_safeDist`), then the `bufio` connection lemmas
(`Proof/bufio/Net.lean`), which the raw-TCP kits use.

### Phase 4: one set of models, over tcpExt (trusted Go code, proved specs)

Order by who needs what; each model is a patch (Q1) with dsverify's tests kept as differential tests
against the real library, and a "not modelled" panic outside its scope.
1. **Codecs, one generator for both projects.** dsverify's `pbgen.py` (per-type plain protobuf
   marshal code, byte-exact against protobuf-go v1.36.12, its `PbCodec` class proved per type) is the
   E2 (b) model etcd decided on: adopt it as `etc/pbgen.py` for etcd's and raft's `.proto` files,
   replacing `pbEncC` and the per-type registration axioms when etcd switches (phase 6). Same for JSON
   (`jsongen.py`, `jsoncodec`) as E3's model. gob: dsverify's names-only + generated codec, net/rpc's
   only user.
2. **net/rpc** (kits only): dsverify's model as a patch of Go's `net/rpc` (overlay), its proofs
   (5.3k) ported over phase 3's specs; `rpcgen.py` moves with it.
3. **net/http**: start from dsverify's server and `ReadResponse` (enough for net/rpc's CONNECT and
   craq), then grow to option B §4.4 (client `Transport.RoundTrip` with the program's dialer, resends,
   `ServeMux`, `Flusher`, `Shutdown`) for rafthttp and etcd's peer handlers. Spec vocabulary: the
   per-address protocol of dsverify's `RpcWorld` and of our `HttpNet`/`Proto` (`Boundary.lean`), merged
   into one, so that `Boundary.lean`'s statements become theorems.
4. **gRPC**: option B §4.3 with Q2's wire. Unary first from dsverify's model and proofs
   (`ClientConn.Invoke.spec`, `handlerOk`, `GrpcWorld`, status codes, contexts via Perennial's
   `context`), checked against quepaxa-net's use; then what etcd needs beyond it: streams
   (`NewStream`, `GenericClientStream`/`ServerStream`, the two-queue protocol of `InvGrpcStream.lean`
   as a proved fact), interceptors, metadata, resolvers and idleness, `GracefulStop`/`Stop`,
   `WaitForReady`, transparent retry only when not dispatched. The kit-facing statements stay those of
   dsverify (Q5); etcd's `InvGrpc*` vocabulary is re-derived on top (phase 6).
5. Whatever else the kits use that is a model of a library (dsverify's `log`, `log/slog`, `sync.Map`,
   `math/rand`, zerolog, go-redis, gogoproto, `cmap`, `gods`, `uuid`): stays lab-side (not network,
   not etcd's), except where etcd-grove has a translation of the same package already; then one copy,
   here.

### Phase 5: the statement and the kits

- `GoNet/Statement/SafeDist.lean`: dsverify's `SafeDist` over `tcpExts` with `PlanWellFormed` (Q4),
  `driver_dist_safe` restated; the goal template, `goal-check.sh` and `goal-axioms.sh` updated (the
  permitted axioms: Lean's, Perennial's, the exported package's trusted definitions; no new axiom).
- Port the kits in order of transport difficulty, each checked by the lab's `verify.sh` and the
  comparator: paxos-net-3 (raw TCP), vsr-net-1 (JSON), rabia-net-1, epaxos-net-1/2, gryff-net-2
  (bufio, net/rpc master), craq-net-2 (net/rpc over http), quepaxa-net-2 (gRPC). A kit whose proof
  ports with import changes is done; otherwise a continuation run with the new harness.
- Run the rig (`harness/rig`) on the ported kits with etcd-grove's tracer and certified checker
  (`examples/net/conform`), as `D/harness/conform` did with its uncertified one.

### Phase 6: etcd onto the same models (option B, its own stage)

Out of scope for the port, but the reason for doing it this way: the main tree's names-only `net`
becomes `GoNet`'s, the gRPC and net/http axioms (~130, `Proof/google_golang_org/grpc/`,
`Proof/net/http/Axioms.lean`) become theorems over the models, rafthttp's dialer and etcd's
`client/pkg/transport` wrappers run as translated code (option B §3), the single-process closed
theorems become distributed (`goose_dist_crash_adequacy`, one node per member). It needs streams,
cmux and the HTTP client from phase 4 and is planned on its own, from `tcp-extension-design.md` §5-7.

## 4. Sizes and risks

- Phase 1: small (days); phase 2: mostly moves and scripts (days); phase 3: 2-4k Lean lines; phase 4
  for the kits' subset (codecs, net/rpc, http server, unary gRPC): porting ~12k Lean lines of dsverify
  proofs to the new specs and patches, weeks; phase 4's etcd part (streams, client http, the rest of
  grpc) is option B's estimate (60-110k Lean lines in all, `option-a-cost.md`); phase 5: per kit,
  from hours (import changes) to a continuation run.
- Risk: a kit proof uses a fact of `NetConn` that tcpExt does not give (phase 3's list). Mitigation:
  find them before porting the models, by checking phase 3's statements against every kit's proof.
- Risk: patches of the real packages are harder to write than substitute packages, and dsverify's
  agents read the model code. Mitigation: the patches' added files are dsverify's code; the kit-facing
  specs do not change.
- Risk: the isolation leak (Q3). Mitigation: the export's leak check in the gates.
- Risk: two moving targets (dsverify's runs keep landing on `NetConn`). Mitigation: freeze the lab's
  harness for new kits at phase 5's start; running runs finish on the old harness.
