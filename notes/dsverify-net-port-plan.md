# Porting dsverify-lab onto etcd-grove's network semantics (plan)

Plan, 2026-11-17, revised 2026-11-18 with the user's decisions (Section 2), and 2026-11-19 (phase 4: a
library of laws, not second specs); being implemented. The user's request: port dsverify-lab's network kits to
etcd-grove's network semantics (the net extension, v3.2; today `GooseLang/Ext/Tcp`, renamed in phase 1), copying what we need from dsverify-lab
into etcd-grove, so that there is **one general-purpose model of `net/http` and gRPC** (and
`net/rpc`, the codecs) used both by etcd and by the dsverify examples.

**Handoff (2026-11-21): `notes/dsverify-net-handoff.md`** is the current snapshot (done, open, traps).

Sources read (2026-11-17): dsverify-lab at GitHub `master` `348a866` (the local clone's `master`,
`c9a88f9`, is older and has none of the network work: `git fetch` first); here, `lean` at
`3e38269e20`; `notes/net-tcp.md`, `notes/net-tcp-dsverify-{survey,final}.md` (the two semantics
compared, 2026-11-14/15), `notes/specs-only/tcp-extension-design.md` (option B, accepted 2026-11-12),
`notes/robustness.md`. dsverify-lab paths below are relative to its root (`D/`), Lean ones to
`D/harness/lean/Harness/`.

## 1. What each side has

| | dsverify-lab (`348a866`) | etcd-grove (`lean`) |
|---|---|---|
| network semantics | `GooseLang/Ext/NetConn/Impl.lean` (393 lines): global listeners with pending lists, two streams per connection, a break cuts both, `Write` one step, only Read/Accept wait, no crashes (`crash := id`) | `GooseLang/Ext/Tcp/Impl.lean` v3.2 (609): plan address → host, per-direction cuts, `Write` Go's loop of steps (D15), every op may stutter (D22), node-local crashes, `CloseWrite` |
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
is not built) is exactly what proved models over the net extension would replace.

## 2. Decisions

The user's (2026-11-18):
- **Names.** The extension is *the net extension*, not a "TCP extension": its names say `net`, not
  `tcp` (phase 1 renames what exists).
- **Home.** The net extension stays in etcd-grove until further notice (not Perennial, not a
  separate repository).
- **Kits.** We do not launch dsverify-lab runs (no continuation runs, no `experiment.sh`): the kits'
  proofs are ported here by editing them; what a port cannot do by editing is recorded for the user.
- "Implement the plan": the recommendations below are taken as decided, each recorded in
  `notes/decisions.md` when its phase starts, open to revision.

**Q1. Models are first-class Go packages** (the user's decision, 2026-11-20, superseding "models
are patches of the real packages"; `notes/decisions.md`, "Models are first-class Go packages").
Option B (accepted 2026-11-12, U2) keeps every type and option of the real grpc-go / Go `net/http`
(etcd's translated code and its dependencies, `otelgrpc`, grpc-gateway, the prometheus interceptors,
typecheck against the real API); dsverify-lab substitutes whole hand-written packages with only the
API its kits reach, which cannot serve etcd. So each model is a Go package in `models/` that starts
from the real library's source and keeps its API, real code wherever goose takes it, with the hard
core replaced (dsverify's model code is the replacement's source: framing, transport, dispatch) and
the places changed marked `MODEL:`; its difference from the library is computed, not stored
(`models/diff.py`); dsverify's differential tests stay. A standard-library model builds by
substituting its files for the toolchain's (`models/goroot.py`: an overlay for `go build`/`go test`,
a GOROOT of links for goose; a goose project's `std_models`).

**Q2. gRPC: one stream per connection** (option B's U3), not dsverify's sequence-numbered
multiplexing: no stream ids, multiplexing or pool in the trusted model; cmux's `HTTP2()` matcher sees
the real 24-byte preface; "at most one dispatch per attempt" is a per-connection fact. dsverify's
unary proofs (5.6k lines) are adapted at the level of `ClientConn.Invoke.spec`/`handlerOk`. net/rpc
keeps dsverify's framing (one connection, sequence numbers: net/rpc's own protocol shape).

**Q3. The shared code is a part of this repository, `Net/`** (modules `Net.*`), importing only
Perennial and the net extension. dsverify runs must not see etcd-grove (`D/README.md`, "How it is
isolated"), so the lab consumes an **export** of the part (`etc/export-net.sh`: the part, the
extension and their scripts as a standalone Lake package, with a leak check failing on any etcd/raft
module, path or name, run in `etc/gates.sh`). The home stays here.

**Q4. No restart in the kits' statement.** Most kits keep no durable state, so they are not safe
under crash *and restart*: their statement has no crashing machine, over `goose_dist_adequacy`;
a process's death without restart is already a cut for its peers (D10/D11). Crash-restart
statements (`goose_dist_crash_adequacy`) only for kits with durable state. (The statement itself is
`Robust [] nodes g bound`, this repository's, not the lab's `SafeDist`: the user's decision,
2026-11-19; phase 4.)

**Q5. Kit proofs port by editing.** The kit-facing vocabulary is kept (phase 4, as a library of
laws over the canonical `net` specs, not as second specs: revised 2026-11-19) so that each kit's
proof ports by changing imports, names and its `net` call sites (the canonical spec with the law's
update); where a statement must change, the port edits the proof here. A kit whose port needs more than editing (a new invariant, a real proof gap) is listed
for the user, who decides whether the lab reruns it.

## 3. The plan

Each phase is a branch landed on `lean` by `etc/land.sh`, with its decisions in `notes/decisions.md`;
a change to the trusted semantics adds its Go example in `examples/net/semantics/` in the same commit
(CLAUDE.md, extensions), and waits for the user's review before landing.

### Phase 0: inventory and reference copies

- dsverify-lab pinned at GitHub `master` `348a866` (fetched 2026-11-17).
- Copy, **as reference, not built**, into `old/dsverify/` (with a README naming the commit, as
  `old/bbolt/`): `harness/lean/Harness/{GooseLang/Ext/NetConn,TrustedCode/net.lean,Code/net.toml,
  Spec/net,Proof/net,Proof/grpc,Proof/encoding,Proof/jsoncodec,Proof/bufio,NetLib.lean,SafeDist.lean,
  Driver.lean,DistLemma.lean}`, `harness/rpcmodel/{grpc,protobuf,src,difftest,grpcdifftest}`,
  `harness/{pbcodec,jsoncodec,kitgen,netsem,netprobe}`, and the notes `grpc-model.md`, `conform.md`,
  `harness-m2-netconn.md`, `harness-m2a.md`.
- The kits' proofs: the lab repository keeps only `theorems/<run>/{Goal.lean,axioms.txt}`; the
  proofs are in the runs' homes on the experiment machines (`fk-lean1`, `fk-lean2`). Locate them
  (read only) and record where; copying them is phase 6's.
- The `net` API the kits and the models call, against the net extension's modeled set. Known:
  `"tcp4"` (3 uses), `SetKeepAlive`/`SetKeepAlivePeriod` (7 each), `SetReadBuffer` (10),
  `SetWriteBuffer` (7).

**Phase 0's findings (2026-11-18, read-only inventory):**
- *Not modeled here, used by kits:* `"tcp4"` (go-vsr `pkg/network/tcp.go:38,69`); `SetKeepAlive`,
  `SetKeepAlivePeriod`, `SetReadBuffer`, `SetWriteBuffer` (rabia `internal/tcp/tcp.go:49-61`, through a
  `*net.TCPConn` assertion); the pure address helpers `SplitHostPort`, `ParseIP`, `net.IP`'s
  `To4`/`String`/`Equal` (go-vsr `pkg/ipv4port`; names-only in both models, the run rewrote them);
  `Dial("udp")` (swiftpaxos `latency.go:235`, which the kit already requires off the path).
- *Concurrent writes:* every kit and model serializes its writes on a connection (a mutex, or one
  writer goroutine), so none visibly relies on Go's write lock; one suspect, quepaxa's
  `connectToClient` (the 4-byte handshake written unlocked after the writer is published), unknown in
  the run's fork. The lab's one-step `Write` made the question invisible; under our `Write` loop a
  proof keeping `sendTok` in an invariant would break. Decision: model Go's write lock (phase 2.3): it
  is Go's behavior, and it removes the risk.
- *Addresses:* node `i` at `10.77.0.(10+i)`, ports 7000-9006 (none ephemeral, none loopback); the two
  kits listening on wildcards (epaxos, gryff) use a distinct port per node, so D21 already holds:
  phase 2.4 is not needed for the kits (kept as an option for later).
- *The proofs:* `theorems/<run>/` keeps 1-12 Lean files per run (the goal, results); the proof trees
  are `runs/<run>/home/work/<proj>` at tag `final` on the experiment machines (paxos-net-3 `dbb8647`,
  craq-net-2 `ac82100`, epaxos-net-1 `0e71508`, epaxos-net-2 `eeb7fa7`, gryff-net-2 `c03461d`,
  quepaxa-net-2 `7a689be`, rabia-net-1 `4fc8d6b`, vsr-net-1 `fa054c9`), not reachable from this
  machine (`fk-lean1`/`fk-lean2` do not resolve; no ssh configuration). **Resolved 2026-11-20:** the lab
  now keeps one current proof per system in `examples/<system>/` (dsverify-lab `master`, `9cbb866`:
  `goal/`, `proof/` at the run's tag `final`, `fork/`, `harness/`, `src/`, `SOURCE.md`; its
  `examples/README.md` lists the runs and axioms): paxos (`paxos-net-3`), craq (`craq-net-2`), vr
  (`vsr-net-1`), rabia (`rabia-net-2`), epaxos (`epaxos-net-2`), quepaxa (`quepaxa-net-2`), gryff
  (`gryff-net-2`), swiftpaxos (`swift-net-1`), all on Perennial `4c8617a9e`, each with its own copy of
  the harness it was seeded with (the lab's "merging the harness copies into one shared library comes
  later": the port is that merge). They must never be visible to a lab run (its "Never in a run's
  view"); etcd-grove is never mounted in a run, so copies here are fine.
- *Spec facts:* the lab's exported specs do not expose "a `Dial` succeeds only with an open listener"
  or "a read error only after the bytes are drained" (`Specs.lean:1702-1706`, `:1829-1835`); the
  visible kit files use only `addrProto`, `addrTok`, `addrUnset` (and the `G` variants) of the net
  vocabulary.

### Phase 1: the rename (no change of meaning)

`tcp` names become `net` names; Go's own identifiers (`TCPConn`, `TCPListener`, `tcpsock`,
`mptcpStatus*`, `tcpConnWithout*`) and the measured Go tests' names stay.
- `GooseLang/Ext/Tcp/` → `GooseLang/Ext/Net/`; namespace `Perennial.Tcp` → `Perennial.Net`;
  `tcpExt`/`tcpExts`/`tcpGF`/`tcpExts_hasTcp`/`tcp_semantics`/... → `netExt`/`netExts`/`netGF`/
  `netExts_hasNet`/`net_semantics`/...; `TcpGlobal`, `TcpLocal`, `TcpConn`, `TcpEnd`, `TcpDir`,
  `TcpErr`, `TcpStatus`, `TcpStep`, `IsTcpStep`, `TcpGS` → `Net...`; ghost `tcpEnd`, `tcpDir`,
  `tcpConnAt`, `tcpPend`, `tcpPlan`, `tcpLis`, `tcpLisAt`, `tcpFresh`, `tcpNames` → `net...`;
  `wp_tcp_*` → `wp_net_*`. Perennial's toy `Perennial.netExt` (`Ext/Net`) has a different full name;
  check no module opens both.
- The part `NetTcp/` → `Net/` (lean_lib `Net`, modules `Net.*`); goose project `nettcp` → `net`;
  `lake exe nettcp-replay` → `net-replay`; `etc/tcb-collections/nettcp.txt` → `net.txt`;
  `NETTCP_*` environment variables → `NET_*`; `etc/gen-init.py`'s `NT_*` tables; CLAUDE.md, the
  scripts, `examples/net/**` (docs, `conform/check/mapping.py`), `Robustness/Stream.lean`'s comments.
- Notes keep their file names (`net-tcp*.md` are history); `notes/net-tcp.md` gains a line on the
  rename. Check: `etc/goose.py --check`, `lake build Net Robustness`, `etc/gates.sh`, the replay of the
  certified conformance samples, `etc/tcb-report.py --check` with the collection renamed (same axioms).

### Phase 2: close the net extension's gaps for the kits (trusted, reviewed)

From `net-tcp-dsverify-final.md` ("What one admits and the other excludes") and phase 0's list:
1. **`"tcp4"`**: as `"tcp"`, with Go's `Net` field `"tcp4"` in errors; evidence row in `doc.go`.
2. **Socket options** (`SetKeepAlive`, `SetKeepAlivePeriod`, `SetReadBuffer`, `SetWriteBuffer`, and
   `SetNoDelay`/`SetLinger` if reached): `nil` on an open end, a `closed`-kind error on a closed one,
   no state; keepalive's effect is already covered by cuts. Measured rows.
3. **Go's write lock**: concurrent `Write`s on one end do not interleave (`fd_unix.go:366`). Model it
   (a lock in the end's state held across a `Write`'s loop of steps): decided after phase 0.
4. **Wildcard `Listen` with one IP per node.** D21 (`ListenAt`, `Impl.lean:446`) requires the
   wildcard's port to be the plan's only address with that port, because on one machine a wildcard
   listener takes every local address (`TestAddressAliases`); kits listening on `":p"` on every node
   would panic. Make the deployment's kind part of the plan (one machine, or one network namespace per
   host): per host, the wildcard resolves to (this node's host, `p`), unique per host; measured in
   namespaces (dsverify's `node_identity_netns_test.go` is the evidence to port).
   (Not needed by the kits: phase 0.)
5. **The address helpers** `SplitHostPort`, `ParseIP`, `net.IP` (pure Go code): translated, not
   modeled.
6. **The deployment premise**: `NetConfig.WellFormed` onto `PlanWellFormed` (dsverify forbids 127/8;
   we forbid ephemeral ports): the kits' configured ports out of 32768-60999 if any are there.
Each with its `Tests.lean` example, a conformance run, and a soundness review (the `axiom` skill)
of the changed rows.

**Phase 2's state (2026-11-19, branch `net-gaps`, v3.3, approved by the user and landed on `lean`
2026-11-19; `notes/decisions.md`, "The net extension v3.3"):** done: 1 `"tcp4"` (D23),
2 socket options (D24: `SetKeepAlive`, `SetKeepAlivePeriod`, `SetNoDelay`, `SetLinger`,
`SetReadBuffer`, `SetWriteBuffer`, specs and proofs `Net/{Spec,Proof}/net/TCPConn__Set*.lean`),
3 Go's write lock (D25; `Conn.Write.spec` unchanged, the lock inside its proof; the contiguity fact
for clients left to phase 4), 5 in part (`IP.To4` translated; `SplitHostPort`, `ParseIP`,
`IP.String`, `IP.Equal` names only, why in `notes/net-tcp.md`, "Address helpers"). Not done: 4
(not needed by the kits, phase 0), 6 (the kits' ports, phase 6). Evidence:
`examples/net/semantics/{tcp4,sockopt,writelock}_test.go`; conformance: the checker transcribes the lock, a probe mode
`concwrite` with a certified sample; review: `notes/axiom-review/tcp-semantics.md`, v3.3.

### Phase 3: the export

`etc/export-net.sh` and its leak check (Q3); the part's API list `etc/api/net.txt` and generated
interfaces. dsverify-lab's own build moving onto the export (Lake, our Perennial pin) is the lab's
change, proposed to the user, not made here.

### Phase 4: the kits' network vocabulary as a proved library of laws (no trust)

**Redesign (2026-11-19, the user's rule "a single canonical spec for each function", 2026-11-18;
`notes/decisions.md`, "The kits' network vocabulary: a library of laws").** The first version of
this phase proved the lab's Hoare triples of `net`'s functions (`Spec/net/*`) over the net extension,
as second specs. That is dropped: `Net/Spec/net/*` stay the only specs of `net`'s functions, and the
phase is a **library**, `GooseLang/Ext/Net/Proto.lean` (neutral path and names: nothing of etcd, so
phase 3's export carries it), giving the lab's vocabulary as predicates over the extension's ghost
state with **laws**: for each operation, the update its canonical spec takes, built from the
vocabulary, and what the caller has after it. A kit proof calls the canonical spec with the law's
update; phase 6 ports each kit's call sites by editing (`wp_apply net.TCPConn.Write.wp_proof ...`
becomes `wp_apply net.Conn.Write.wp_proof ...` with `writeP`/`write_acc`). The pure facts of a
direction (`DirOk` and its laws, `setMap`, `ndot_mask`) moved from the examples' `wire/Stream.lean`
and `wire/Addr.lean` to `GooseLang/Ext/Net/Stream.lean`, which `wire` imports (the seven examples
build unchanged but for qualified names).

**The library** (`Proto.lean`, 1450 lines, no axiom, no `sorry`):
- Vocabulary: `Proto GF := Nat → List w8 → IProp GF`, `protoPrefix`, `ProtoPrefixClosed`;
  `addrTok a` (persistent: the plan entry), `addrUnset a` (the address's empty pending set),
  `addrProto a P Q` (persistent), `sendTok cn s P W`, `recvTok cn s P R`, `recvTokL` (its protocol
  fact one step later), `connEnd`, `sentLb`, `connFresh` (timeless, exclusive), `connIs`, `lisInv`
  (a listener shared between threads); the global names `[NetProtoGS]` and `regCtx`, made by
  `netProto_alloc`.
- Built on: a registry invariant (`regInv`, timeless: each connection's ends and directions with
  `DirOk`), and per address an invariant with the protocols as parameters of its statement
  (`addrInvP a γa P Q`: the pending set, the acceptors' deposits, each connection's protocol facts),
  so a reader's protocol fact costs one later (an invariant's), not two (an invariant's and a saved
  predicate's): `recvTokL` and `recvTokL_later`/`recvTok_L`.
- Laws: `addrs_start` (the extension's start resources: every plan address `addrUnset`),
  `addr_set_proto`, `addrs_set_proto`, `addrTok_listenAt`; `dial_au`, `accept_au`,
  `accept_shared_au`, `writeP`/`writeP_init`/`write_acc`, `read_au`, `close_au`, `closeWrite_au`,
  `deadline_au`, `sockopt_au`, `lisClose_au`, `lisInv_alloc`; `connFresh_excl`, `recvTok_proto`,
  `recvTok_proto_closed`, `protoPrefix_closed`, `sendTok_sentLb`, `recvTok_sentLb`,
  `sendTok_sentLb_prefix`, `sendTok_connIs`, `recvTok_connIs`.
- No canonical spec changed. `Conn.Write.spec` does not expose the write lock's contiguity (D25):
  `sendTok` is exclusive and travels in the writer predicate, so no other writer appends between a
  `Write`'s steps in the ghost state, and phase 0 found no kit writing one end from two threads
  without a lock. Added: `Conn.SetReadDeadline.spec` and `Conn.SetWriteDeadline.spec` (the models
  were there, with no spec; the lab's rpc/http/gRPC models call them), proved as `SetDeadline`'s.

**Coverage against the lab's use** (the visible kit files use only `addrProto`, `addrTok`,
`addrUnset` and their `G` variants; the lab's rpc/http/gRPC, bufio and netprobe proofs use the rest;
counted by grep over `old/dsverify/harness/lean/Harness/Proof/`):

| the lab's | here |
|---|---|
| `addrProto a P Q`, `addrProtoG` | `addrProto a P Q` (same shape; `cn : Nat`, not `cid : w64`) |
| `addrTok a`, `addrTokG` (exclusive; `Listen` needs it) | `addrTok a` (persistent); `Listen.spec` needs `ListenAt`: `addrTok_listenAt` with the node's host |
| `addrUnset a`, `addrUnsetG` | `addrUnset a`, from the start: `addrs_start` (the kits' bridge, `robust_of_distBoot`) |
| `addr_set_proto` (`==∗`), `addrs_set_proto` | `addr_set_proto`, `addrs_set_proto` (`={E}=∗`, with `regCtx`) |
| `sendTok`, `recvTok`, `connEnd` | the same; a `Read` gives `recvTokL` (`recvTokL_later`, or a credit) |
| `connFresh`, `connFresh_excl` | the same (timeless, `⊢ False`) |
| `sentLb`, `sendTok_sentLb` (no visible use) | `sentLb`, `sendTok_sentLb`, `recvTok_sentLb`, `sendTok_sentLb_prefix` |
| `recvTok_proto`, `protoPrefix`, `ProtoPrefixClosed`, `protoPrefix_closed`, `recvTok_proto_closed` | the same |
| `newConnResult` (`Dial`/`Accept`'s post) | `Dial.spec`/`Listener.Accept.spec`'s post (`isConn c cn s a ∗ Qok cn`) with `Qok` from `dial_au`/`accept_au`/`accept_shared_au` (`connEnd ∗ connFresh`) |
| `connErr`, `opErr`, `opResult` (codes) | the specs' `resErr`/`ReadErr` (kinds `closed`, `timeout`, `sys`; EOF a `ReadRes`) |
| `ownTCPConn c cid side` | `connAt t cn s a la ra`/`isConn c cn s a` (`Net/Proof/net/Base.lean`) with `connIs cn` |
| `ownListener l lid a`, `listening` | `isListener`/`lisAt` with `netLisAt`, and `netLis` (owned) or `lisInv` (shared) |
| `nodeIp ip` | the machine's host in `DistBootWp` (`Net/Statement/DistBridge.lean`) |
| `net.TCPConn.Read.wp_proof` | `net.Conn.Read.wp_proof` + `read_au` |
| `net.TCPConn.Write.wp_proof` | `net.Conn.Write.wp_proof` + `writeP`, `writeP_init`, `write_acc` |
| `net.TCPConn.Close.wp_proof` | `net.Conn.Close.wp_proof` + `close_au` |
| `net.TCPConn.Set{,Read,Write}Deadline.wp_proof` | `net.Conn.Set{,Read,Write}Deadline.wp_proof` + `deadline_au` |
| `net.TCPConn.Set{ReadBuffer,WriteBuffer,KeepAlive,KeepAlivePeriod}.wp_proof` | `net.TCPConn.Set*.wp_proof` + `sockopt_au` |
| `net.TCPListener.Accept.wp_proof` | `net.Listener.Accept.wp_proof` + `accept_au`/`accept_shared_au` |
| `net.TCPListener.Close.wp_proof` | `net.Listener.Close.wp_proof` + `lisClose_au` (shared) |
| `net.Dial.wp_proof`, `net.DialTimeout.wp_proof`, `DialNet` | `net.Dial.wp_proof`/`DialTimeout.wp_proof` (`tcpNet nw`) + `dial_au`, `addrProto_tok` |
| `net.Listen.wp_proof`, `ListenWild`, `ListenNet` | `net.Listen.wp_proof` (`ListenAt`: an address itself or a wildcard, D21) + `addrTok_listenAt` |
| `isConnP`, `isListener`, `connEnd_isConnP`, `listening` (no visible use) | `connIs`, `sendTok_connIs` |
| `ownSlice_take_acc` (`NetLib.lean`, netprobe) | not ported (a slice lemma: Perennial's, or the kit's) |
| `safeDist_of_wp`, `safeDist_of_bootAt`, `NodeBootWpAt`, `addrs_set_proto` (`SafeDist.lean`) | `Net/Statement/DistBridge.lean`: `robust_of_distBoot`, `robust_of_distProto`, `DistBootWp` (the statement `Robust`, below) |

The facts `NetConn` gives and the net extension does not: "a `Dial` succeeds only with an open
listener" and "a read error only after the bytes are drained". The lab's exported specs do not
state either (`Specs.lean:1702-1706`, `:1829-1835`: `wp_Dial`'s post is `connEnd ∗ connFresh` or
`True`, `wp_Read`'s says only that an error comes with no bytes), so no lab proof can use them:
confirmed, none of `Proof/net/{rpc,http}`, `Proof/grpc`, `Proof/bufio`, `netprobe` mentions a
listener's state in a dial or a stream's drained state in a read error. The third, no interleaved
concurrent writes, is the write lock (above).

**bufio over a connection.** Here `bufio`'s `Reader` is translated with its bodies (project `etcd`,
`Code/bufio.toml`, for the WAL) and specified over `io.readerStream` (`Spec/bufio/Reader__Read.lean`,
`Proof/io/ReaderStream.lean`); the lab's `readerOk_conn` becomes "a connection end with
`recvTokL` is an `io.readerStream`". Not written: `io.readerStream` needs `sint.Z n = len ys` of the
count, and `Conn.Read.spec` gives `sint.nat n` only, because Perennial's `copy` spec
(`wp_slice_copy`) does (an empty read could return a negative count, as far as the specs say:
`notes/perennial-changes.md`, 2026-11-19). With `copy`'s spec stating `sint.Z` (Perennial), or a
local `copy` lemma here, `ReadOut` states `sint.Z` and the law is about 100 lines. The module lives
in the main tree (namespace `EtcdGrove`), which phase 3's export must then take or move. The
`Writer` is not translated: adding it is `Writer`, `NewWriter{,Size}`, `(*Writer).{Write,
WriteByte,WriteString,Flush,Available,Buffered}` in `Code/bufio.toml`, a regeneration of project
`etcd`, and a rebuild of `Code/bufio.lean`'s importers (4860 modules, the main tree:
`etc/importers.py --count`); its spec and proof are the lab's `Proof/bufio/Writer.lean` (706 lines)
over a writer contract like `io.readerStream`.

**The statement: `Robust`** (the user's decision, 2026-11-19: `SafeDist` replaced by this
repository's `Robust`; `notes/decisions.md`, "The kits' statement is `Robust`"). A kit's theorem is

    DistDeploy plan hosts nodes g → Robust [] nodes g bound

`Robust` (`Robustness/Statement.lean`, unchanged) with every machine in `stable` (none crashes, Q4),
under the **kit deployment premise** `DistDeploy` (`Net/Statement/DistDeploy.lean`, trusted, generic
over any extensions with the net extension, no etcd name): the plan is well formed
(`PlanWellFormed`, D20) and is the network's plan, the network has no connection, machine `i` is
on `hosts[i]` (its net-extension local state) with no listener. `Robust`'s own premise (each
machine a fresh Go process, `Fresh`) is not repeated. `Robust` does not state the main thread's
result (the lab's `SafeDist` did: `#()`); a kit's check is a panic.

The bridge (`Net/Statement/DistBridge.lean`, proved): `distNsteps_of_crash_nil` (with no boot
program, `DistCrashNsteps []` is `DistNsteps`), so `goose_dist_adequacy` proves `Robust [] …`;
`robust_of_distBoot` (from every plan address `addrUnset` and the ghost state's plan, a share per
machine and its boot WP `DistBootWp`, under any ghost state whose Go context is `Robust`'s `lctx`)
and `robust_of_distProto` (the library's names made first). The bridge covers the all-stable case
only (`notes/robustness.md`, "Next"). Not vacuous: `echo_dist_robust`
(`Net/Proof/github_com/mit_pdos/etcd_grove/examples/net/echo/RobustLinked.lean`) is the three-node echo
system in this form (plan `[(SrvAddr, "h")]`, `PlanWellFormed` by `decide`, every machine on `"h"`),
through `robust_of_distBoot`, closed, `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`;
its proof keeps echo's own protocol (`echoInvs`), so the bridge serves a program that does not use
the library too. (It also follows from `echo_crash_robust` by `Robust.of_all_crashing`: a run with
no crashing machine is a run in which every machine may crash.) `Net/Statement/SafeDist.lean` and
`echo_safeDist` (this phase's first statement) are deleted.

**Open, for phase 6:** a kit proof using the library end to end (dsverify's `netprobe` is the
first client, once its proof is copied here); the bufio laws above.

### Phase 5: one set of models, over the net extension (trusted Go code, proved specs)

Each model a first-class Go package in `models/` from the real library's source (Q1), dsverify's
tests kept as differential tests against the real library, a "not modelled" panic outside its scope.
1. **Codecs, one generator for both projects.** dsverify's `pbgen.py` (per-type plain protobuf
   marshal code, byte-exact against protobuf-go v1.36.12, `PbCodec` proved per type) is the E2 (b)
   model etcd decided on: `etc/pbgen.py` for etcd's and raft's `.proto` files too (used by etcd in
   phase 7). The same for JSON (`jsongen.py`, `jsoncodec`, E3). gob: names-only plus the generated
   codec, net/rpc's only user.

   **Done (2026-11-19).** *Where.* The shared Go code is the Go module `models.lab` in
   `models/` (its own `go.mod`; `toolchain go1.27.3`, `etc/goose.py`'s `GO_TOOLCHAIN`, with the go
   line at 1.27 so that the examples' module, on go 1.27, can import it: a dependency's go line above
   the main module's makes Go rewrite the importer's module graph): `models.lab/pbcodec` and
   `models.lab/jsoncodec`, dsverify's `harness/pbcodec`, `harness/jsoncodec` with their comments
   made neutral (no kit, no harness path) and pbcodec's protowire tests no longer behind a build tag
   (the module requires protobuf-go v1.36.12 for its tests only). The path names neither etcd-grove
   nor dsverify-lab: the part is exported to the lab (Q3), whose runs must not see this repository,
   and a kit's generated codec imports it by that path in both places (`notes/decisions.md`, "Shared
   Go runtime under a neutral module path"). Translated by goose project `models` into the part
   `Net/` (`-lean-root models.lab=Net`: `Net/Code/models_lab/{pbcodec,jsoncodec}.lean`, with
   their bodies, nothing trusted); their `Init.lean` from `etc/gen-init.py` (`NET_PKGS`).
   *Generators.* `etc/pbgen.py` and `etc/jsongen.py` (now `models/protobuf/pbgen.py`, `models/json/jsongen.py`), from `harness/kitgen/`: generic (a [protobuf]
   or [json] table in any toml file, `SECTION.toml OUTDIR --pkg NAME`), the registration with the
   protobuf/encoding-json model optional (`--register`: those models are later items), `--check`;
   jsongen gained its command line (kitgen called it as a module). What they generate is unchanged
   but the helpers' import path and the messages. Use in each script's docstring.
   *What is proved* (`Net/Proof/models_lab/`, `Results.lean`; TCB collection
   `etc/tcb-collections/models.txt`, no axiom of ours): `jsoncodec`'s `IsSpace`, `AppendRaw`,
   `AppendBool` (dsverify's `wp_IsSpace`, `wp_AppendRaw`, `wp_AppendBool`, now `X.spec` +
   `X.wp_proof`), both packages' `wp_initialize'` (generated), and, new, both `(*Error).Error`
   (`Error.Error.spec`, of an error kept for good, `↦□`) with `Error_is_error` and `Error_errAny` (over the `Error()` spec, a premise, as vocabulary files import specs only; linked in `Results.lean`) (a kept `*pbcodec.Error` or
   `*jsoncodec.Error` is `errAny`: what a program's proof of `marshalOk`/`unmarshalOk` needs of its
   generated codec's errors). The codec vocabulary: `pbcodec/Codec.lean` (`PbCodec`, `marshalOk`,
   `unmarshalOk`, from `Proof/grpc/Pb.lean`), `jsoncodec/Codec.lean` (`JsonCodec`, `jsonValid`,
   `marshalOk`, `unmarshalOk`, `scanOk`, `scanFn`, from `Proof/encoding/json/Defs.lean`),
   `Errors.lean` (`errAny`). Left to the protobuf and encoding/json models' items: `kitCodecOk`,
   `codecSet`, `codecFns`, `kitFn`, `PbKit`/`JsonKit`, the registries' `SetCodec`/`getCodec`/`Marshal`/
   `Unmarshal`/`Valid` specs (`Pb.lean`'s proofs, `Proof/encoding/json/{Codec,Valid,Raw,Stream}.lean`,
   `json.lean`), which are about the models, not the codec. The pbcodec helpers' own specs (varints,
   tags, `SkipField`, `ValidUTF8`) were proved per kit in the runs (`codec.helpersOk`), not in the
   harness, and are not here yet: a kit port proves them (or they move here when the first port
   needs them).
   *Statement changes* (each a rename; the bodies are dsverify's): `google_golang_org.protobuf.proto.
   {PbCodec, marshalOk, unmarshalOk}` → `models_lab.pbcodec.*` (the protobuf model's namespace
   keeps what is about the model); `encoding.json.{JsonCodec, jsonValid, marshalOk, unmarshalOk,
   scanOk, scanFn}` → `models_lab.jsoncodec.*`; `encoding.json.isSpaceB` merged into
   `jsoncodec.spaceB` (the same definition; `jsonValid` uses it); `scanFn` names
   `models.lab/jsoncodec.Scan` (was `dsverify.lab/harness/jsoncodec.Scan`); `net.rpc.errAny` →
   `models_lab.errAny` (net/rpc's port will use it); `dsverify_lab.harness.jsoncodec.wp_X` →
   `models_lab.jsoncodec.X.wp_proof : X.spec` (the same triples); jsoncodec's `wp_initialize'` is
   gen-init's (Perennial's form, at `HeapGS HasLC.hasLC`, where dsverify's was at any `hlc`).
   *Evidence* (`go vet`, `go test` in `models/` and `examples/models/`): pbcodec against
   protowire and `unicode/utf8`, jsoncodec against `encoding/json` (dsverify's tests); the
   generated protobuf codec of `models/internal/pbdifftest` (dsverify's grpcdifftest messages
   `pb` and `xpb`: every supported field kind, packed repeated scalars, negative enums, two-byte
   tags, recursion) byte-exact against protobuf-go v1.36.12's `proto.Marshal` and its `Unmarshal`
   (value and error-or-not, on encodings and their mutations); the generated JSON codec of
   `models/internal/jsondifftest` (dsverify's difftest types plus a named basic type and an
   `any` field) against `encoding/json`, byte for byte, and its scanner on validity and value ends;
   and the generated protobuf codec of 16 of **etcd's message types**
   (`examples/models/pbetcd`: `etcdserverpb` Range/Put/DeleteRange/LeaseGrant requests and
   responses, `LeaseTimeToLiveResponse`, `WatchCreateRequest` (a repeated enum), `WatchResponse`,
   `Member`, `MemberListResponse`, `ResponseHeader`; `mvccpb.KeyValue`, `Event`) byte-exact against
   protobuf-go v1.36.12 (the version `examples/go.mod` pins) at the examples' etcd pin.
   *What the generator cannot handle in etcd's `.proto` files* (`--from-pb` then, the core's refusals now; E2 (b)
   needs them): **all of raftpb** (proto2: every scalar and enum field has explicit presence, a
   `*T` in Go, written when non-nil even if zero; proto2 enums are closed, an unknown value goes to
   the unknown fields instead of the field; proto2 `bytes` fields keep presence (`Data`, `Context`);
   `ConfState.{Voters,Learners,VotersOutgoing,LearnersNext}` are unpacked repeated scalars; proto2
   strings are not UTF-8-checked); `etcdserverpb.Metadata` (proto2, the same); the **oneofs**
   `RequestOp.Request`, `ResponseOp.Response`, `Compare.TargetUnion`, `WatchRequest.RequestUnion`,
   so also every message reaching them (`TxnRequest`, `TxnResponse`, `InternalRaftRequest` through
   `Txn`). Maps, floats, groups and extensions: none in etcd's messages. (`--from-pb` drafts a oneof's
   holder as an empty message; the refusal lines say why.) Extending pbgen to proto2 presence,
   closed enums, unpacked repeated fields and oneofs is E2 (b)'s work, with the same tests.

   **The generator as trusted code (2026-11-19, branch `pbgen-trust`; the user's decision,
   `notes/decisions.md`, "Trusted generated code: the generator is the trusted artifact").** What is
   trusted is the generator, not each codec: running a program with `proto.Marshal`/`Unmarshal`
   replaced by the code pbgen emits behaves as with protobuf-go v1.36.12, for every schema pbgen
   accepts (nothing in Lean fixes the wire format: a proof proves its codec meets the `PbCodec` it
   chooses, and the closed statement does not mention it). Renamed with the rest of `netmodels/` the
   same day (`models/`, Go module `models.lab`, Lean `models_lab`; the user's naming, `models/README.md`).
   - *Input.* `[protobuf] imports = {alias = "go/path"}`, `roots = ["alias.GoType", ...]`: the root
     message types only. pbgen writes a throwaway `main` in the target's Go module that imports the
     roots' packages and `models.lab/pbdesc`, runs it (`go run`), and reads its JSON: from the
     descriptors protoc-gen-go registered (`protoregistry`, the ones protobuf-go runs on) the roots'
     closure of messages and enums, each field's kind, cardinality, packedness, presence, oneof, map,
     options; from the Go structs each field's Go name and type (by its `protobuf:"..,N,.."` tag).
     No field list is written by hand (`--from-pb` and the field tables are gone). The per-type code
     derived for the two existing inputs is identical to what the hand-written tables gave.
   - *The subset and the refusals* (`models/protobuf/pbgen_core.py`, `Schema`; exit 2, every reason,
     naming message and field, nothing written): accepted are proto3 messages with implicit-presence
     scalars (int32 int64 uint32 uint64 sint32 sint64 fixed32 fixed64 sfixed32 sfixed64 bool string
     bytes), open proto3 enums, singular and repeated messages, packed repeated scalars and enums,
     repeated strings and bytes, all in protoc-gen-go's open struct API. Refused: proto2 and editions
     files; proto3 `optional`; oneofs; maps and map entries; groups; float, double; `[packed=false]`;
     required; defaults; weak and lazy fields; extension ranges, MessageSet; closed enums or enums of
     non-proto3 files; strings without UTF-8 enforcement; a message or enum without a registered Go
     type; a field without an exported Go field of the expected type (the opaque API); exported Go
     fields that are no field's (a oneof holder); colliding aliases or generated names.
   - *The trusted core* (`pbgen_core.py`: 601 lines, 526 non-blank; 118 the doc: the claim, the subset,
     and per field kind the encoding emitted, with the encoding spec's section names and protobuf-go
     v1.36.12's file:line for each choice in the spec's latitude: field order, zero-value omission,
     nil elements, packed acceptance, UTF-8 checks, the recursion limit, unknown fields, the
     error-or-not cases; ~80 the kind tables and field model; ~175 the schema check and refusals;
     ~225 the emitter). Untrusted: the command line, input and dump runner (`pbgen.py`, 203 lines),
     the test generator (`pbgen_testgen.py`, 945 lines, mostly the Go test text). Trusted with the
     core: `models/pbdesc` (Go, 312 lines, ~150 of code), which states the facts the core decides on,
     each read directly off `protoreflect` or `reflect` (it decides nothing; a wrong fact would also
     show in the random-schema test and in the generated shape test). The core's documented deviations: unknown fields checked and dropped (protobuf-go keeps
     them and re-marshals them: a program forwarding a message decoded from a peer with a newer
     schema differs; between peers of one schema none arise), error values not modeled, what comes
     with an error (the review's), slice capacities and aliasing (the review's), only
     Marshal/Unmarshal with default options.
   - *Evidence about the generator.* `models/internal/pbgenrand` (`go test`): random proto3 schemas
     (1-4 messages per file, nested messages and enums, one or two files per schema, cross-file and
     recursive references, empty messages, every scalar kind, enums with negative and extreme values,
     repeated fields, field numbers 1, 15/16, 2047/2048, 18999/20000, 2^18, 536870911 and random
     ones, field names protoc-gen-go must rename (`reset`, `string`, `descriptor`, ...), Go package
     names that collide with each other or with the codec's identifiers), built as
     `FileDescriptorProto`s and compiled by the real protoc-gen-go v1.36.12 (built from the module
     cache and run as a plugin: no protoc here), pbgen run on them (its dump included), and the
     codec checked against protobuf-go by the generated regression test (Marshal byte for byte and
     nil-or-not; Unmarshal of real encodings, mutations, every field number with every wire type,
     error-or-not and value; recursion limits; panics). Seedable (`PBGEN_RAND_SEED`), sized
     (`PBGEN_RAND_SCHEMAS`, `PBGEN_TEST_SCALE`): the gates run 24 schemas (~20 s); by hand, seed 7,
     200 schemas, scale 1: 782 message types, 3207 fields, 2,320,869 encodings equal and 27,615
     Marshal errors agreed, 325,642 mutated decodes equal and 354,358 errors agreed, all passing
     (212 s). `TestRefusals`: one schema per unsupported construct (proto2 with required, default,
     group, closed enum, extension range; editions; proto3 `optional`; oneof; map; float, double;
     unpacked; lazy; a proto3 message reaching a proto2 one; the opaque API), each refused with
     message and field named. The per-type tests of `models/internal/pbdifftest` and
     `examples/models/pbetcd` stay as regression tests.
   - *The gate* (`etc/gates.sh`, section `models`): `pbgen.py --check` on every input (the derived
     dump included), and every `protobuf.toml` of the tree (but `old/`) must be one the gate checks.
   - *Review* (`notes/axiom-review/pbgen.md`): an independent reviewer given only the core, the
     encoding facts and protobuf-go's source, asked for an accepted schema and value on which the
     emitted code and protobuf-go differ. Found none on decoded values, encoded bytes or
     error-or-not; three observable differences, now documented deviations of the core: the
     message's contents after a failed Unmarshal (a packed record cut short keeps the values before
     the bad one), the partial bytes protobuf-go's Marshal returns with its error (the codec: nil),
     slice capacities and aliasing (protobuf-go pre-sizes). Suspected and closed: a dump against
     other `.pb.go` files than the program links (pbgen runs it in the codec's own module).
   - *jsongen*: reworked to the same standard (2026-11-20, branch `models-json`; below).

   **jsongen as trusted code, and the encoding/json model's Go half (2026-11-20, branch
   `models-json`; not landed: the Lean half comes later).**
   - *The real library.* Go 1.27.3's encoding/json as built by default: GOEXPERIMENT jsonv2 is on, so
     the package is the `v2_*.go` files, the v1 API over encoding/json/v2 with `DefaultOptionsV1()`
     (found here: dsverify's notes and tests assumed the v1 implementation, `decode.go`/`encode.go`,
     which only GOEXPERIMENT=nojsonv2 builds). Where they differ for the subset: v2 limits an
     encoding's nesting to 10000 (v1 does not), and its Decoder is jsontext's (buffer, read sizes).
     `notes/decisions.md`, "The encoding/json model is of Go 1.27.3's default build".
   - *Input.* `[json] imports = {...}`, `roots = ["alias.T", ..., 'struct { ... }']`: the root types
     only (what the program passes to Marshal/Unmarshal/Encode/Decode or holds in an `any`; T covers
     *T). jsongen writes a throwaway main in the codec's module that calls `models.lab/jsondesc`
     (Go, 181 lines: reflection's facts, kind, fields with `Tag.Lookup("json")`, the JSON hook methods
     by name on T and *T, RawMessage/Number identity; decides nothing) and reads its JSON. The
     hand-written `[json.types]` table is gone (`--dump`/`--print-dump` as pbgen).
   - *The subset* (`models/json/jsongen_core.py`, 787 lines: 143 the doc, ~290 the schema check and
     refusals, ~350 the emitter): bool, string, every int and uint size (64-bit int/uint), named or
     not; slices (not of a uint8 kind: base64); named structs (an unnamed struct only as a root, its
     code outside Goose, as before); `any` fields and elements (encoded by dynamic type; decoding into
     one panics); json.RawMessage; tags `-`, a name of ASCII letters, digits and `!#$%()*+-./:;=?@[]^_{|}~`
     and space (or empty: the Go name), options `omitempty` and `string` (on integers). New against
     the old jsongen: signed integers, uint16/uint, omitempty, ignored and unexported fields,
     recursive slices, the encoder's nesting limit (an error past 10000, RawMessages counted by
     `jsoncodec.Nesting`), empty arrays into non-nil slices (a new empty slice), top-level basic
     roots. Dropped: user MarshalJSON/UnmarshalJSON (refused now; the vsr kit fork has none).
   - *The refusals* (exit 2, every reason, naming type and field; `TestRefusals`, 43 cases): floats,
     complex, chan, func, uintptr, arrays, maps (any key), pointers but at the root, interfaces with
     methods, `any` as a root, slices of a uint8 kind, embedded fields (also pointers), unexported
     fields with a json tag, names with `<>&`, quotes or non-ASCII, non-ASCII Go names used as names,
     tag options other than omitempty/string (omitzero, inline, `-,`'s empty one, repeated), `string`
     on non-integers, duplicate or case-fold-equal JSON names, json.Number, any of MarshalJSON,
     UnmarshalJSON, MarshalText, UnmarshalText, AppendText, MarshalJSONTo, UnmarshalJSONFrom on T or
     *T, unexported/generic/main types, packages without an alias.
   - *Found by the new tests, fixed* (all in trusted code that had passed the old per-type tests): (1)
     `jsoncodec.QuotedUint` returned a type error for a `,string` field whose string has an escape
     (`"7"`), which the real Unmarshal decodes (7): a real behavior the model did not have (now a
     NotModelled panic, as for any escape; `QuotedInt` the same); (2) the v2 encoder's nesting limit
     (above); (3) the real Decoder reads twice at the end of a stream when a number inside an
     unfinished array or object is completed by io.EOF (`endsInNumber`); (4) `fmt` prints a real
     RawMessage through jsontext.Value's `String` (the model's RawMessage has it now).
   - *Evidence about the generator* (`models/internal/jsongenrand`): random Go packages (structs of
     every accepted field kind and tag form, named basic, slice and recursive slice types, `any`,
     RawMessage, names with punctuation and names the generated code uses, an unnamed root), jsongen
     on each (its dump included), the generated test against the real encoding/json: Marshal of
     random values (T, *T, nil *T; strings sometimes outside the plain subset: a NotModelled panic is
     accepted only where the real output has an escape or a non-ASCII byte), the model's Unmarshal
     (Valid, then the codec) of real encodings and 13 kinds of mutation (case, delimiters in keys,
     escapes, signs, numbers at every limit, unknown and repeated members, cuts, nesting) into every
     type, fresh and pre-filled (error-or-not and the value, also after an error; a syntax error
     leaves the real target unchanged). Gates: 6 packages (~20-45 s). By hand, seed 100: 80
     packages, 2202 types, 1,888,674 encodings equal, 56,450 errors agreed, 36,756 NotModelled;
     93,085 decodings equal, 73,719 errors agreed, 58,938 syntax errors agreed, 14,258 NotModelled;
     all passing (200 s). Regression codecs: `models/internal/jsondifftest` (the old types plus a
     struct of every field form), `models/internal/jsonvsr` (go-vsr's messages, below).
   - *The model* (`models/encoding/json/`, module `models/encoding/go.mod` never built;
     `goroot.py`'s STD_MODELS; `goroot.py` and `diff.py` copied unchanged from `models-rpc-http`
     in a commit of their own): the default build's `v2_*.go` with every exported name (Marshal,
     Unmarshal, Valid, the error types, Number, HTMLEscape as Go's code; Encoder, Decoder,
     RawMessage, Token, Delim, Options and its 14 functions), reflection and v2 replaced by the
     program's Codec (`model.go`: Marshal, Unmarshal, Scan; `SetCodec` once; the generated
     `RegisterJSON` under tag netmodel/goose), the Decoder over jsontext's buffer exactly (64 bytes,
     its growth and compaction, so every Read asks for the real length at the real moment; framing
     by `jsoncodec.Scan`; jsontext's read-ahead before a top-level `,`/`:` error, and the second
     io.EOF read above), the Encoder as Go's (one Write per value, sticky write errors). Not
     modelled (a NotModelled panic): MarshalIndent, Indent, Compact, SetIndent with an indent,
     Token, More, DisallowUnknownFields, v2's options, RawMessage's IsValid/Format/Compact/Indent/
     Canonicalize; not part of it: RawMessage.Kind, Number's MarshalJSONTo/UnmarshalJSONFrom.
     `diff.py encoding/json --stat`: against the default build's files (v2_*.go, 1780 lines) +493
     -621 (`model.go` 124 added, `v2_stream.go` +292 -151, `v2_inject.go` removed); the v1
     implementation's 9 files (4278 lines) count as removed (`+493 -4900` in all). Goose takes the
     whole package (checked by hand on a GOROOT of links, `goroot.py farm`: 3587 Lean lines) once
     `type Delim rune` is spelled `int32` (`notes/perennial-changes.md`); not committed (the Lean half).
   - *Evidence about the model* (`models/internal/jsonstreamtest`, `run.sh`, in the gates): the same
     tests in the real build and the model build (overlay; it needs a go1.27.3 outside the module
     cache: `~/sdk/go1.27.3` or a copy in `.lake/`), both reproducing the real build's golden
     transcripts (every Read's length and result, every Decode's value, error class, InputOffset and
     Buffered length, every Write's bytes): go-vsr's `wire.Encode`/`wire.Decode` (an Encoder and a
     Decoder per message: the first decoder's read-ahead is lost, as in vsr) and one Decoder per
     stream, over net.Pipe and over scripted readers with chunk sizes 1..100000, the 12 vsr messages
     (one of 300 log entries, past the 4 KiB buffer), the stream cut at every byte with io.EOF or a
     read error, 35 malformed streams (stray delimiters, bad literals and numbers, nesting at 10000),
     the Encoder over a failing writer, and 3000 random streams (by hand: 40,000, identical).
   - *vsr.* `models/internal/jsonvsr`: go-vsr's `events`, `log` and `wire` (the dsverify fork at
     `215992d`, Apache-2.0) and their codec: everything vsr-net sends and receives is in the subset
     (the frame's unnamed struct as a root, outside Goose; the kit fork's Goose-translated code must
     name it); `Logs`' MarshalJSON/UnmarshalJSON (upstream go-vsr, not the fork) would be refused.
   - *For the Lean half*: specs of `Marshal`, `Unmarshal`, `Valid`, `NewEncoder`/`Encode`,
     `NewDecoder`/`Decode` over the registered codec (dsverify's `Proof/encoding/json/{Codec,Valid,
     Raw,Stream}.lean`, `json.lean` and `JsonKit` are the start; its Stream spec was over the old
     buffer policy and needs the jsontext one, or a spec abstract in the read lengths); a goose
     project with `std_models` (from `models-rpc-http`) and names-only `reflect`, `strconv`,
     `strings`, `bytes`, `sync` where Perennial lacks them (the error types hold `reflect.Type`);
     `jsoncodec`'s new helpers (`AppendInt`, `Int`, `QuotedInt`, `Nesting`, `noEscape`; translated,
     `Net/Code/models_lab/jsoncodec.lean` regenerated, not built here) and per-kit proofs of the
     generated codec against `JsonCodec`.
2. **net/rpc** (kits only): Go's `net/rpc` as a model, dsverify's codec and dispatch in place of
   gob and reflection, its proofs (5.3k lines) ported over phase 4's specs; `rpcgen.py` with it.

   **The Go half done (2026-11-20, branch `models-rpc-http`; the Lean half lands with it).**
   *The models.* `models/net/rpc/` and `models/net/http/` are Go 1.27.3's sources (committed
   unmodified first, then changed; the places marked `MODEL:`; `models/diff.py net/rpc --stat`:
   4 files, +392 -281 lines, of which 325 the new `codec.go`; `net/http`: 7 files, +201 -257,
   162 the new `textproto_model.go`). Every exported name stays. *net/rpc*: kept as Go's code: the
   Client (pending calls, sequence numbers, `input`, `send`, `Go`, `Call`, `Close`), `NewClient`,
   `NewClientWithCodec`, `Dial`, `DialHTTP`, `DialHTTPPath` (its CONNECT handshake through
   `http.ReadResponse`), the Server's request loop (`ServeCodec`, `ServeRequest`, `readRequestHeader`,
   the free lists, `sendResponse`), `Accept`, `ServeHTTP` (Hijack), `HandleHTTP`, Register's checks
   and messages. Replaced (reflection and gob: goose takes neither): `suitableMethods`, `reflect.New`
   and `Value.Call` by the program's generated `Codec.Receiver` (per method `NewArg`, `NewReply`,
   `Call`); gob's client and server codecs by the model's frame codec (`codec.go`: each gob message,
   a header or a body, one length-prefixed frame, so a cut stream gives gob's errors: `io.EOF`
   between messages, `io.ErrUnexpectedEOF` within one; sticky write errors as gob's bufio.Writer);
   the `sync.Map` of services by a map under a mutex (no `sync.Map` spec in Perennial); the debug
   page not modelled (panics). *rpcgen* (`models/net/rpc/rpcgen{,_core,_testgen}.py`, the trusted
   core 569 lines with its doc: the claim, the subset, the refusals, the encoding, gob's merging
   decode rules cited to `encoding/gob`'s source): input only the receiver types (and extra types),
   the methods and every type's structure dumped by reflection (`models.lab/rpcdesc`, which copies
   net/rpc's `suitableMethods`); refusals (exit 2, naming type, field or method) of floats, complex,
   arrays, interfaces, channels, functions, uintptr, embedded fields, pointer elements, pointers to
   pointers, structs with no exported field, recursive and unnamed struct types, unnameable types,
   types with gob/encoding marshaler methods; decoding reproduces gob's merging into a non-zero
   reply (fields not sent keep their value, slices reuse their backing array, maps keep their
   entries). Over-approximations (panics, "documented deviations"): decoding a value of one type into
   another type (gob matches fields by name), encoding a nil or unlisted value, decoding into a nil
   pointer; the model's errors on malformed input are its own (no model peer sends any). *net/http*:
   kept as Go's code: the whole server (`Serve`, `conn.serve`'s keep-alive loop, the background read
   that cancels a request's context when the client goes, `Hijack`, the 400/431/501/505 answers, the
   response writer with Content-Length or chunked framing, sniffing, `Date`), ServeMux and patterns,
   the handlers, `Request`/`Response` and their Write methods, the Client's code, transfer.go's
   framing for Content-Length and to-EOF bodies. Replaced: the HTTP/1.x head parser (net/textproto's
   `ReadLine` and `readMIMEHeader`, as `readRequest`, the server and `ReadResponse` call them) by
   `textproto_model.go` (textproto's results and its `ProtocolError` messages; panics on a header
   continuation line and a header name with a space); not modelled (panic): chunked bodies, TLS and
   unencrypted HTTP/2 serving, the Transport's round trip (the client is item 3's). For goose: four
   declarations it refused changed (two body-less linkname declarations dropped, `readMIMEHeader`'s
   linkname, a struct copy between two memory places through a local, a local type renamed): with
   them goose takes all of net/http with its bodies (4.4 MB of Lean), so the configuration
   (`Net/Code/net/http.toml`) translates types, names and the model's parser only for now.
   *Build.* `models/goroot.py`: an overlay for `go build`/`go test` (`-tags netmodel` for the
   programs' generated registration), a GOROOT of links for goose (its go/packages reads files from
   disk: an overlay in GOFLAGS type-checks the real files); `etc/goose.py`'s project option
   `std_models` and project `models-net` (into `Net/Code/net/{rpc,http}.lean`; `--check` of the
   affected projects net, models, models-net, kv, putget unchanged/up to date). *Evidence*
   (`models/internal/rpcdifftest/run.sh`, in the gates: the same tests against the real packages and
   against the models): dsverify's net/rpc tests (calls, server errors, lookup errors, concurrent
   calls, Close, a broken connection, at-most-once under random cuts, dial errors, the CONNECT
   handshake by hand, Register/HandleHTTP errors) plus gob's merging through a call, `Go`, and
   faults with exact outcomes: the server's response cut after every byte count (outcomes: `ok`,
   `io.ErrUnexpectedEOF`, "reading body EOF", "reading body unexpected EOF", the same set in both),
   the request cut likewise (`ServerError("EOF")`, `ServerError("unexpected EOF")`, ...), a
   connection reset (a `*net.OpError` holding ECONNRESET), the server closing mid-call; the codec's
   generated test against real gob (zero and non-zero targets); the generator's random-type test and
   its refusals (`models/internal/rpcgenrand`); and the net/http model's transcripts
   (`models/internal/httpdifftest`): 49 raw request exchanges with a server (keep-alive, pipelining,
   Expect, HEAD, chunked responses, Flush, Hijack with buffered bytes, CONNECT, the malformed cases'
   400/431/501/505) and `ReadRequest`/`ReadResponse` on 2011 heads and seeded mutations, against
   golden transcripts the real build writes (the model may answer "not modelled" for an entry, never
   another value; 1-2% of the mutations are). The tests found three discrepancies of the first parser
   (textproto's `trim` is spaces and tabs only; it quotes the line with the name canonicalized), and
   rpcgen's random test a package alias the generated tests' locals shadowed: all fixed.
   *For the Lean task*: specs of `Client.Call`/`Go`/`Close`, `DialHTTP(Path)`, `NewClient`,
   `Server.Register(Name)`, `ServeConn`/`ServeCodec`, `ServeHTTP`, `HandleHTTP`, the frame codec
   (`readFrame`, the client and server codecs) over the net extension's `Conn`, and the generated
   Codec's laws (`Encode`/`Decode` round trip on a zero target; `Receiver`'s methods as the
   receiver's), replacing dsverify's `Proof/net/rpc`; for net/http: `ListenAndServe`/`Serve`,
   `Handle`, `ServeMux.ServeHTTP` on an exact path, `ReadResponse` on a CONNECT answer, and the
   server's connection loop to the point of a hijack (dsverify's `Proof/net/http`); the
   translation's missing imports (`go/token` for `token.IsExported`; `bufio` is the main tree's).
   **The Lean half, first part (2026-11-20, branch `models-rpc-http-lean`, on `models-rpc-http`
   merged with `lean`; not landed yet: *Landing*, below).**
   *Compiles* (`lake build Net`, 2295 jobs): `Net/Code/net/{rpc,http}.lean` and their
   `GeneratedProof`. `Net/Code/net/http.toml` widened to what net/rpc's HTTP path runs, with
   bodies: `ReadResponse`, `Handle`, `ServeMux.{Handle,register,registerErr,ServeHTTP,Handler,
   findHandler,matchOrRedirect}`, `Serve`, `ListenAndServe`, `Server.{Serve,ListenAndServe,
   newConn}`, `conn.{serve,readRequest,hijacked,hijackLocked}`, `response.{Hijack,Header,
   WriteHeader,Write,write}`, `serverHandler.ServeHTTP`, `DefaultServeMux` (the rest names only:
   an untranslated function is an `opaque` constant, so a body calling one is stuck, which a proof
   must rule out or specify). Its imports are the packages those bodies call: Perennial's, the main
   tree's names-only `bufio`, `net/url`, `path`, `crypto/tls` (lean roots `bufio=`, `net/url=`,
   `path=`, `crypto/tls=` of project models-net), and two new names-only translations in the part:
   `net/textproto` and the vendored `golang.org/x/net/http/httpguts` (`vendor=Net`). goose imports a
   vendored package by its import path but names it by its package path, so
   `Net/{Code,GeneratedProof}/golang_org/x/net/http/httpguts.lean` are hand-written one-line
   forwarding modules (`notes/perennial-changes.md`, 2026-11-20). **`go/token.IsExported` is
   modelled, not translated** (its body reads `unicode`'s case tables, which nothing translates):
   `Net/Code/go/token.toml` (`trusted = ["IsExported"]`), `Net/TrustedCode/go/token.lean`: exact on
   a name whose first byte is ASCII (`'A'..'Z'`, Go's `IsUpper` fast path), `false` on `""`, and a
   **choice point** (`ArbitraryInt`'s low bit) on a non-ASCII first byte; tested against Go by
   `models/internal/rpcdifftest/isexported_test.go` (documented in `models/README.md`).
   *Proved* (`Net/Spec/net/rpc/`, `Net/Proof/net/rpc/`, one canonical spec each; `Results.lean`
   links them, `#print axioms` Lean's three; TCB collection `etc/tcb-collections/models-net.txt`,
   baseline not yet run): the wire (`Base.lean`: `frameOf`, `strEnc`, `reqHdr`, `respHdr`, their
   injectivity), `putU64`, `getU64`, `putString`, `putFrame`, `getString`; `readFull` over
   `net.Conn.Read.spec` (accessor style, as the examples' `wire.ReadFull`; errors `readErr`: `io.EOF`
   only between frames, `io.ErrUnexpectedEOF` within one, the `Read`'s `*OpError`), `readFrame`;
   the codec registry (`Codec.lean`: `CodecSpec` with `enc`/`dec`, `codecIs`, `codecInv` half of
   `codec`'s points-to under `codecMu`, `codecUnset` the other half, `codecSet` persistent) with
   `SetCodec` and `getCodec`; the client codec's `ReadResponseHeader`.
   *Statement changes vs dsverify* (`old/dsverify/.../Proof/net/rpc/`): the wire is two frames per
   message (header, body: Go's two gob messages), so dsverify's `msgOf` becomes `reqHdr`/`respHdr`
   with the body in its own frame; `RpcCodec` loses `call` and `methods` (the dispatch is net/rpc's
   own code through the `Receiver`'s `Method`s, whose obligations are still to state), keeping
   `enc`/`dec` as `CodecSpec` (a record the program's proof chooses, not a type class); the
   registry is `codecSet` from `SetCodec` (dsverify: a package fact); the readers take a reader
   predicate and accessor (as `wire.ReadFull`) rather than `recvTok` directly, so a reader of the
   library (`GooseLang/Ext/Net/Proto.lean`, `read_au`) and an invariant-held reader both apply.
   *What remains* (in order; nothing below is stated yet, and nothing has an axiom or `sorry`):
   1. the codecs' other methods: `clientCodec.{WriteRequest,ReadResponseBody,Close}`,
      `serverCodec.{ReadRequestHeader,ReadRequestBody,WriteResponse,Close}` (over
      `net.Conn.Write.spec` with the library's `writeP`/`write_acc`, `putFrame`, `getCodec`,
      `encOk`/`decOk`; the sticky `werr`);
   2. the protocol vocabulary, from dsverify's `Proto.lean`/`Defs.lean` over the library: `RpcWorld`
      (address → service → `MethodSpec`), per-connection ghost state (requests, the reader's count,
      answers) and `reqProto`/`respProto` over the two-frame wire; the `Receiver` obligations
      (`NewArg`, `NewReply`, `Call` meet the `MethodSpec`: `rcvrOk`);
   3. the Client (`send`, `input`, `Go`, `Call`, `Close`, `NewClient`, `NewClientWithCodec`, `Dial`;
      `Call.done`'s `select` on a buffered channel, the `pending` map, `reqMutex`/`mutex`) with
      dsverify's `Client.Call.spec` (at most one run of the handler, `ServerError(msg)` exactly one,
      `errAny` otherwise). `input` calls `err.Error()` on a body read's error, which can be the net
      extension's `*OpError`: its `Error` is the trusted model's arbitrary string
      (`Net/TrustedCode/net.lean`, `OpError.Error.impl`), so a law `resErr (some k) … err ⊢ errAny
      err` (dsverify's `opErr_errAny`) is the first step;
   4. the Server (`register`, `Register(Name)`, `readRequestHeader`, `readRequest`, the free lists,
      `sendResponse`, `service.call`, `ServeCodec`, `ServeConn`, `ServeRequest`, `Accept`).
      `readRequestHeader` calls `err.Error()` on a header read's error (the same law);
   5. the package initialization of `net/rpc` (`isPkgInit`: `DefaultServer`, `codecMu`/`codecUnset`,
      `errFrame`, `ErrShutdown`): `etc/gen-init.py` over its import closure, which reaches
      `net/http`'s many untranslated initializers, each a trust-boundary axiom there
      (`opaqueInitsOk`); to keep the TCB axiom-free, `net/http`'s initializers the closure needs must
      be translated first (or the facts stated from the model's own variables only);
   6. `DialHTTPPath`: `http.ReadResponse` over a `bufio.Reader` of the connection (the reader's
      read-ahead: the CONNECT answer is all the server writes before the client's first request,
      a protocol fact `respProto` must carry), then `NewClient`;
   7. net/http: `ReadResponse` (the model's head parser, `readTransfer` for a CONNECT answer),
      `Handle` and `ServeMux` exact-path dispatch (Go 1.22 patterns and the routing tree),
      `Serve`/`ListenAndServe` and `conn.serve` up to a hijack (`context.WithCancel`/`WithValue`,
      the `connReader`'s background read and its abort on `Hijack`, `sync.Pool` bufio readers and
      writers, `recover` in the deferred handler, the TLS type assertion, `readRequest`'s URL
      parsing through `net/url`, names only today), `response.Hijack`; then `ServeHTTP` and
      `HandleHTTP`. This is Go's real server, not dsverify's 324-line one: its proof is the largest
      item (dsverify's `Proof/net/http` is 1.4k lines for a server without background reads,
      contexts or pools).
   *Landing.* The first attempt stopped at the disk floor (7.2 GB free); after the coordinator freed
   disk: merged with `lean` and `origin/lean`, full `lake build` (22523 jobs) green,
   `etc/tcb-report.py --collection etc/tcb-collections/models-net.txt --check --update`: 10 roots,
   no axiom of this repository or Perennial, no `sorry` (the baseline is empty), then `etc/land.sh`
   (its gates). Also checked: `etc/goose.py --check --project models-net`, `go test` of
   `TestIsExportedASCII`. That landing failed in the gates' `models` section: the fault test
   (`rpcdifftest`, a stream cut at every byte) saw `ErrShutdown` from real net/rpc, outside its
   expected set. Checked 2026-11-21 that the model produces it too (both builds, about one run in
   20: when the cut precedes the call's registration, the client's reader shuts the client down
   before `send` runs; the model's `Client` is Go's code), so not an under-approximation: the test
   now allows it (not required). Merged with `origin/lean` again (`50e9626bd2`); landing waits for a
   full build, stacked with the grpc and JSON Go halves (`models-grpc-land`, `models-json-land`).
3. **net/http**: (the model's Go is item 2's: the server and `ReadResponse` are Go's code over the
   model's head parser) then option B
   §4.4 (client `Transport.RoundTrip` with the program's dialer, resends, `ServeMux`, `Flusher`,
   `Shutdown`) for rafthttp and etcd's peer handlers; one per-address protocol vocabulary merging
   dsverify's `RpcWorld` and our `HttpNet`/`Proto` (`Proof/net/http/Boundary.lean`).
4. **gRPC**: option B §4.3 with Q2's wire. Unary first from dsverify's model and proofs
   (`ClientConn.Invoke.spec`, `handlerOk`, `GrpcWorld`, status codes, contexts over Perennial's
   `context`), checked against quepaxa-net's use; then what etcd needs: streams (`NewStream`, the
   generic stream wrappers, `InvGrpcStream.lean`'s two queues as a proved fact), interceptors,
   metadata, resolvers and idleness, `GracefulStop`/`Stop`, `WaitForReady`, transparent retry only
   when not dispatched.

   **Go half done (2026-11-20, branch `models-grpc`; the Lean half next).** Under the user's
   decisions of 2026-11-19/20 (a model is a first-class Go package in `models/`, its diff from the
   real library computed; one stream per connection, Q2; the trusted claim: every behavior of
   grpc-go v1.84.0 over Linux TCP, as the program observes it, is one of the model's), the model is
   `models/grpc`, the Go module `google.golang.org/grpc` with v1.84.0's API, unary *and* streams:
   grpc-go's source of the packages the examples reach, with the root package's transport and
   connection management replaced (`models/README.md`, "The grpc model": what is kept, what
   replaced, the over-approximations, what is outside the model). A model build replaces the module
   with `models/grpc/gomodel.py DIR GOARGS...` (a temporary `-modfile`: the module's go.mod plus the
   `replace`; the normal build never sees it). *Kept as grpc-go's code*: every subpackage the
   programs use (status, codes, metadata, peer, credentials, resolver and its dns/passthrough/
   manual resolvers, encoding and its proto codec, keepalive, health, reflection, mem, ...), and in
   the root package the options and their constructors, `invoke`, the interceptor chains, the
   generic stream wrappers, the client stream's attempts, commit, replay buffer and transparent
   retry (`shouldRetry`'s unprocessed case, first attempt only, as grpc-go), `SendMsg`/`RecvMsg`/
   `Header`/`Trailer`/`CloseSend`/`finish`, the server stream, `processRPC`, `handleStream`'s
   lookup and its Unimplemented texts, `Serve`'s loop, the connection set, `GracefulStop`/`Stop`,
   the message framing and size checks (`parser.recvMsg`, `encode`, `msgHeader`, `recv`), the header
   helpers (`model_http_util.go`: `http_util.go` verbatim). *Replaced* (the `model_*.go` files,
   2.3k lines): the HTTP/2 transport by `model_transport.go` over `model_wire.go` (preface, header
   blocks of grpc-go's own header fields (a stream written only after the server's preface arrived, as grpc-go waits for SETTINGS; found by `examples/etcd/partition`'s blackholed bridge, `TestBlackhole`), made and read by grpc-go's `createHeaderFields`,
   `operateHeaders`, `writeHeaderLocked`, `writeStatus`, `writeEarlyAbort`, `handleRSTStream`
   adapted from hpack; gRPC messages; RST_STREAM codes: REFUSED_STREAM for an undispatched stream,
   CANCEL at the server's deadline); the balancers, subchannels, picker, idleness manager by
   `model_clientconn.go` (the program's resolver built on leaving idleness, every reported address,
   a dial and an insecure handshake per attempt, fail-fast and wait-for-ready, idleness when quiet
   at the model's choice); `service_config.go`'s parser by the round-robin config only. *Removed*:
   channelz, stats handlers, binary logging, tracing, server workers, retry policies, the
   subchannels' health-check streams; the packages no longer reached (`internal/transport`, the
   balancers, `internal/idle`, the delegating resolver, ...: 18). Choice points `modelChoose`/
   `modelChooseN` (`model_choose.go`). The computed diff against v1.84.0 (the reached packages):
   16 files of the root package differ, +2724 -3807 lines (`models/diff.py grpc --stat`; the five `model_*.go` files added,
   2464 lines; `balancer_wrapper.go`, `picker_wrapper.go`, `resolver_wrapper.go` and the two
   `clientconn_disconnect_reason` files removed; `clientconn.go` +94 -1217, `stream.go` +54 -849,
   `server.go` +87 -456, `service_config.go` +14 -231, `rpc_util.go` +3 -4, `dialoptions.go` +2 -3),
   and 18 packages dropped whole. *What etcd and the kits reference that had to be kept*: all of
   the API (nothing was dropped from an exported surface the examples use): `ServeHTTP` (etcd's TLS
   path; now a `NotModelled` panic), `WithBlock`, `Dial`/`DialContext`, `ErrClientConnTimeout`,
   `PickFirstBalancerName` (a literal now), the `Peer`/`Header`/`Trailer`/`WaitForReady`/
   `MaxCall*` call options, `ServiceRegistrar`, `UnknownServiceHandler`, `GetServiceInfo`,
   `NewContextWithServerTransportStream`, `SetSendCompressor`/`ClientSupportedCompressors` (over
   the model's server stream), `WithResolvers`, `resolver/manual`, `serviceconfig`, `health`,
   `reflection`, `stats` (types only). *Evidence*: `models/internal/grpcdifftest` (`run.sh`, in
   the gates' models section): 31 tests, each unchanged against grpc-go and the model: unary and
   the three stream kinds, metadata both ways (reserved keys as grpc-go's transport adds them,
   `-bin` values, trailers-only responses whose trailer holds the content type), status messages
   (percent-encoding, non-ASCII), `SendHeader` twice, unknown services and methods, malformed
   names, `UnknownServiceHandler`, deadlines (the client's and the server's RST_STREAM: both
   messages accepted), cancellation seen by the handler, size limits with grpc-go's texts, an
   unreachable server, `WaitForReady` until a server starts, a cut connection (calls and streams),
   `Stop` and `GracefulStop` mid-call and mid-stream, `Close` (`ErrClientConnClosing`), interceptor
   order, `health` (unary and `Watch`), a manual resolver with the round-robin config, QuePaxa's
   generated service (`quepaxa/`, the kit quepaxa-net-2's use), 200 concurrent calls; and
   `TestAtMostOnce` (calls and streams through a proxy cutting every 15 ms: a handler runs at most
   once per call, a success ran it once and returns its reply, a stream's messages in order and
   complete), also run with the model's choices random (where, 2026-11-21, it found grpc-go's own
   spurious clean end of a server stream after a transparent retry, one run in ~50: kept by the model
   as grpc-go's behavior, allowed and counted by the test, `nonissues/grpc-transparent-retry-spurious-eof.md`,
   upstream grpc/grpc-go#9443). `-race` clean in both modes. etcd's
   examples serve and call over the model (`run.sh --etcd`; `examples/` builds against it):
   putget, watch, lease, auth, putget3, leasegrant, compactwatch, cache, leaseexpiry pass, timings
   as over grpc-go. *Known gaps in Go runs* (not in the claim): a model connection has no keepalive,
   so a silently dead peer (a partition without a reset) hangs a stream until its context ends
   where grpc-go fails it after its keepalive timeout (in the semantics a cut may come at any time,
   which covers it). This shows in `examples/etcd/partition` (passes over grpc-go in 165 s): over
   the model `TestMainRun`, `TestClientCuts` pass, `TestFailover` (killed after 374 s),
   `TestWriteOnce` ("no put failed: the cuts cut nothing": a model put waits for its connection's
   server preface instead of failing on an established connection) and `TestWatchFailover` (a watch
   on a blackholed member never ends: no keepalive close) fail: they assert grpc-go's keepalive
   closes and its reuse of established connections, timings the model's Go realization does not
   reproduce (the model's behaviors include grpc-go's: a cut may end a connection at any moment). A
   keepalive in the model's transport (pings while streams are active, a close after the timeout)
   would bring the Go runs closer; not done. The first runs also found two real faults of the model,
   fixed: a stream written before the server's preface (an under-approximation, above) and the
   address choice's Go body always the first address (now round-robin over the addresses not
   failing, `modelChooseAddr`). *For the Lean half*: specs for the model's transport and connection management
   (`newClientTransportStream`, `reader`, `operateHeaders`, `closeStream`, `Write`,
   `ReadMessageHeader`/`Read`, `getTransportConn`, `dialAddr`, the resolver wrapper,
   `exitIdleMode`/`enterIdleMode`, `serverTransport.HandleStreams`/`operateHeaders`, the server
   stream's methods, the wire's readers and writers) and for the kept code on the call paths
   (`invoke`, `newClientStream`, `withRetry`, `shouldRetry`, `SendMsg`/`RecvMsg`, `finish`,
   `Serve`, `handleRawConn`, `handleStream`, `processRPC`, `stop`, `parser.recvMsg`, `recv`,
   `encode`, `toRPCErr`); `modelChoose`/`modelChooseN` the trusted declarations; goose's needs to
   check first: `mem.BufferSlice` and its pools, `fmt`'s verbs in `status.Errorf`, generics
   (`GenericClientStream`), `sync.Cond`, `time.AfterFunc`, `url.Parse` (targets), the dns
   resolver's IP-literal path, map iteration in `createHeaderFields`.
5. dsverify's other library models (`log`, `log/slog`, `sync.Map`, `math/rand`, zerolog, go-redis,
   gogoproto, `cmap`, `gods`, `uuid`) stay lab-side, except where this repository already translates
   the package (then one copy, here).

### Phase 6: the statement and the kits

*(2026-11-21, etcd-grove#24: the shared harness pieces (driver, recorder, checker, porcupine) and dsverify's
`Remote` (clients on machines of their own) moved to kaashoek's `etcd-dist` claim: `examples/lib/remote` over
`lintest`/`kvcheck` and the verified porcupine, whose proof replaces the lab's porcupine axiom; the kits are
ported onto it.)*

- The statement: `DistDeploy plan hosts nodes g → Robust [] nodes g bound` (phase 4, above; the
  user's decision, 2026-11-19, in place of the lab's `SafeDist`), proved through `robust_of_distBoot`
  or `robust_of_distProto`; the lab's `driver_dist_safe`, goal template and checks follow (the lab's
  change).
- The kits' Go (the forks at their pins) and proofs, from the lab's `examples/<system>/` (above),
  copied into a part `Dsverify/` (modules `Dsverify.*`, nothing outside it imports it), with the lab's
  harness pieces they share (`clients`, `recorder`, `check`, `models`, `driver`, porcupine's axiom)
  merged into one copy, ported by editing (Q5), in order of transport: paxos (raw TCP), vr (JSON),
  rabia (bufio), epaxos and gryff (bufio, net/rpc master), craq (net/rpc over http), swiftpaxos
  (net/rpc, gob, sha256), quepaxa (gRPC); each `goal` restated as `DistDeploy … → Robust [] …`,
  `#print axioms` checked, a TCB collection per kit.
- The lab's rig traces of the kits checked with this repository's certified conformance checker
  (`examples/net/conform`).

**Phase 6's state (2026-11-22, branch `dsv-paxos`; `notes/dsv-paxos.md`):** paxos ported. The part
`Dsverify/` (lean_lib `Dsverify`, goose project `dsv-paxos`, Go in `examples/dsverify/paxos`), the
kit moved onto `examples/lib/remote` (ten machines: orchestrator, four client machines, five
servers; a write-once register with pending proposals as porcupine's model). The protocol's proof
(invariant, agents, transport over `Net/Spec/net` and `Proto.lean`, deployment) compiles; the
statement `paxos_remote_robust` (`DistDeploy … → Robust [] …`) is proved, `#print axioms` Lean's three
(no axiom, no `sorry`). Found: remote's
`ServeClient.spec` takes `newClient` as a persistent triple, so a client that needs exclusive
resources (paxos's one-shot proposer tokens) must be made before `ServeClient` (the kit does).

### Phase 7: etcd onto the same models (option B, its own stage)

The main tree's names-only `net` becomes the part's; the gRPC and net/http axioms (~130,
`Proof/google_golang_org/grpc/`, `Proof/net/http/Axioms.lean`) become theorems over the models;
rafthttp's dialer and etcd's `client/pkg/transport` wrappers run as translated code (option B §3);
the closed theorems become distributed (one node per member). Planned on its own from
`tcp-extension-design.md` §5-7 once phase 5 has streams, cmux and the HTTP client.
**Planned 2026-11-21: `notes/phase7-plan.md`** (claim #24; the inventory, the slices, the user's
decisions it needs).

## 4. Sizes and risks

- Phases 0, 1, 3: days. Phase 2: about a week with its review. Phase 4: 2-4k Lean lines. Phase 5 for
  the kits' subset (codecs, net/rpc, http server, unary gRPC): ~12k Lean lines of dsverify proofs to
  port, weeks; its etcd part (streams, the HTTP client, the rest of grpc) is option B's estimate
  (60-110k Lean lines in all, `option-a-cost.md`). Phase 6: per kit, from hours to days.
- A kit proof uses a fact of `NetConn` the net extension does not give: found in phase 4 by checking
  its statements against every kit's proof, before the models move.
- The kits' proofs may not be reachable from here (phase 0); then phase 6 waits for the user.
- Patches of real packages are harder to write than substitute packages; the patches' added files are
  dsverify's code and the kit-facing specs do not change.
- dsverify's runs keep landing on `NetConn` meanwhile: new kits switch to the export when the user
  decides; running runs finish on the old harness.
