# Porting dsverify-lab onto etcd-grove's network semantics (plan)

Plan, 2026-11-17, revised 2026-11-18 with the user's decisions (Section 2), and 2026-11-19 (phase 4: a
library of laws, not second specs); being implemented. The user's request: port dsverify-lab's network kits to
etcd-grove's network semantics (the net extension, v3.2; today `GooseLang/Ext/Tcp`, renamed in phase 1), copying what we need from dsverify-lab
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

**Q1. Models are patches of the real packages.** Option B (accepted 2026-11-12, U2) writes each model
as a patch of the real grpc-go / Go `net/http` source, keeping every type and option (etcd's
translated code and its dependencies, `otelgrpc`, grpc-gateway, the prometheus interceptors,
typecheck against the real API). dsverify-lab substitutes whole hand-written packages (a GOROOT
symlink farm, `go.mod` replaces) with only the API its kits reach, which cannot serve etcd. So:
`etc/model-patches/<project>/*.patch`, applied by `etc/goose.py` (an overlay for the standard
library), for grpc, net/http, net/rpc, encoding/json and gob; dsverify's model code becomes the
content of the patches' added files (framing, transport, dispatch), and its differential tests stay.

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
under crash *and restart*: `SafeDist` over the net extension with `goose_dist_adequacy`, as today;
a process's death without restart is already a cut for its peers (D10/D11). Crash-restart
statements (`goose_dist_crash_adequacy`, later `Robust`) only for kits with durable state.

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
  machine (`fk-lean1`/`fk-lean2` do not resolve; no ssh configuration). Phase 6 needs them copied here
  (the user's action).
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

**Phase 2's state (2026-11-19, branch `net-gaps`, v3.3, not landed: the trusted semantics waits for
the user's review; `notes/decisions.md`, "The net extension v3.3"):** done: 1 `"tcp4"` (D23),
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
| `addrUnset a`, `addrUnsetG` | `addrUnset a`, from the start: `addrs_start` (`SafeDist`'s bridge) |
| `addr_set_proto` (`==∗`), `addrs_set_proto` | `addr_set_proto`, `addrs_set_proto` (`={E}=∗`, with `regCtx`) |
| `sendTok`, `recvTok`, `connEnd` | the same; a `Read` gives `recvTokL` (`recvTokL_later`, or a credit) |
| `connFresh`, `connFresh_excl` | the same (timeless, `⊢ False`) |
| `sentLb`, `sendTok_sentLb` (no visible use) | `sentLb`, `sendTok_sentLb`, `recvTok_sentLb`, `sendTok_sentLb_prefix` |
| `recvTok_proto`, `protoPrefix`, `ProtoPrefixClosed`, `protoPrefix_closed`, `recvTok_proto_closed` | the same |
| `newConnResult` (`Dial`/`Accept`'s post) | `Dial.spec`/`Listener.Accept.spec`'s post (`isConn c cn s a ∗ Qok cn`) with `Qok` from `dial_au`/`accept_au`/`accept_shared_au` (`connEnd ∗ connFresh`) |
| `connErr`, `opErr`, `opResult` (codes) | the specs' `resErr`/`ReadErr` (kinds `closed`, `timeout`, `sys`; EOF a `ReadRes`) |
| `ownTCPConn c cid side` | `connAt t cn s a la ra`/`isConn c cn s a` (`Net/Proof/net/Base.lean`) with `connIs cn` |
| `ownListener l lid a`, `listening` | `isListener`/`lisAt` with `netLisAt`, and `netLis` (owned) or `lisInv` (shared) |
| `nodeIp ip` | the node's host in `NodeBootWpAt` (`Net/Statement/SafeDist.lean`) |
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
| `safeDist_of_wp`, `safeDist_of_bootAt`, `NodeBootWpAt`, `addrs_set_proto` (`SafeDist.lean`) | `Net/Statement/SafeDist.lean`: `safeDist_of_bootAt`, `safeDist_of_proto`, `NodeBootWpAt` |

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

**The statement** (`Net/Statement/SafeDist.lean`, module `Net.Statement.SafeDist`): `SafeDist nodes
pl hosts`, the lab's over `netExts`, `PlanWellFormed pl` in place of `NetConfig.WellFormed`, node
`i` on `hosts[i]`, over `goose_dist_adequacy` (Q4); bridges `safeDist_of_bootAt` (from every plan
address `addrUnset` and the ghost state's plan) and `safeDist_of_proto` (the library's names made
first). Not vacuous: `echo_safeDist`
(`Net/Proof/github_com/mit_pdos/etcd_grove/examples/net/echo/SafeDist.lean`) is the three-node echo
system as a `SafeDist` (plan `[(SrvAddr, "h")]`, every node on `"h"`), closed, `#print axioms`:
`propext`, `Classical.choice`, `Quot.sound`; its proof keeps echo's own protocol (`echoInvs`), so the
bridge serves a program that does not use the library too.

**Open, for phase 6:** a kit proof using the library end to end (dsverify's `netprobe` is the
first client, once its proof is copied here); the bufio laws above.

### Phase 5: one set of models, over the net extension (trusted Go code, proved specs)

Each model a patch (Q1), dsverify's tests kept as differential tests against the real library, a
"not modelled" panic outside its scope.
1. **Codecs, one generator for both projects.** dsverify's `pbgen.py` (per-type plain protobuf
   marshal code, byte-exact against protobuf-go v1.36.12, `PbCodec` proved per type) is the E2 (b)
   model etcd decided on: `etc/pbgen.py` for etcd's and raft's `.proto` files too (used by etcd in
   phase 7). The same for JSON (`jsongen.py`, `jsoncodec`, E3). gob: names-only plus the generated
   codec, net/rpc's only user.
2. **net/rpc** (kits only): dsverify's model as a patch of Go's `net/rpc` (overlay), its proofs
   (5.3k lines) ported over phase 4's specs; `rpcgen.py` with it.
3. **net/http**: from dsverify's server and `ReadResponse` (net/rpc's CONNECT, craq), then option B
   §4.4 (client `Transport.RoundTrip` with the program's dialer, resends, `ServeMux`, `Flusher`,
   `Shutdown`) for rafthttp and etcd's peer handlers; one per-address protocol vocabulary merging
   dsverify's `RpcWorld` and our `HttpNet`/`Proto` (`Proof/net/http/Boundary.lean`).
4. **gRPC**: option B §4.3 with Q2's wire. Unary first from dsverify's model and proofs
   (`ClientConn.Invoke.spec`, `handlerOk`, `GrpcWorld`, status codes, contexts over Perennial's
   `context`), checked against quepaxa-net's use; then what etcd needs: streams (`NewStream`, the
   generic stream wrappers, `InvGrpcStream.lean`'s two queues as a proved fact), interceptors,
   metadata, resolvers and idleness, `GracefulStop`/`Stop`, `WaitForReady`, transparent retry only
   when not dispatched.
5. dsverify's other library models (`log`, `log/slog`, `sync.Map`, `math/rand`, zerolog, go-redis,
   gogoproto, `cmap`, `gods`, `uuid`) stay lab-side, except where this repository already translates
   the package (then one copy, here).

### Phase 6: the statement and the kits

- `Net/Statement/SafeDist.lean`: dsverify's `SafeDist` over `netExts` with `PlanWellFormed` (Q4),
  written in phase 4 (above), and `driver_dist_safe`; the lab's goal template and checks follow (the
  lab's change).
- The kits' Go (the forks at their pins) and proofs copied into a part `Dsverify/` (modules
  `Dsverify.*`, nothing outside it imports it), ported by editing (Q5), in order of transport:
  paxos-net-3 (raw TCP), vsr-net-1 (JSON), rabia-net-1, epaxos-net-1/2, gryff-net-2 (bufio, net/rpc
  master), craq-net-2 (net/rpc over http), quepaxa-net-2 (gRPC); each `goal` restated over phase 6's
  `SafeDist`, `#print axioms` checked, a TCB collection per kit.
- The lab's rig traces of the kits checked with this repository's certified conformance checker
  (`examples/net/conform`).

### Phase 7: etcd onto the same models (option B, its own stage)

The main tree's names-only `net` becomes the part's; the gRPC and net/http axioms (~130,
`Proof/google_golang_org/grpc/`, `Proof/net/http/Axioms.lean`) become theorems over the models;
rafthttp's dialer and etcd's `client/pkg/transport` wrappers run as translated code (option B §3);
the closed theorems become distributed (one node per member). Planned on its own from
`tcp-extension-design.md` §5-7 once phase 5 has streams, cmux and the HTTP client.

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
