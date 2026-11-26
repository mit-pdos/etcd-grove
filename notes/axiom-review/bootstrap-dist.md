# Review: `bootstrap.wp_proof_dist` (statement `bootstrap.specDist`)

The `axiom` skill, run by a fresh agent given the axiom's text and the Go code (not the author's
reasoning), 2026-11-25. Branch `etcd-safe-bootax/2026-11-25`.

**Verdict: survives, with required changes to docstrings and Go evidence only (applied; re-review
below).** The Lean statement is unchanged. No Go execution the axiom covers panics or makes the post
`bootOk` false. The one assumption its truth rests on: a `GET /members` answered by something other than
etcd's peer handler with a list holding `null` panics `bootstrap` in Go; `bootRTOk` excludes both routes
to such an answer (the opaque `httpPeerSvc`, whose only writer at a peer address is `PeerServe_dist`, and
`noProxyEnv`). R1 and R2 below record this.

## Why an axiom, not a theorem

`bootstrap`'s Go is translated with its body, and #34 proves it over its callees' specs (`bootstrap.wp_proof`,
linked as `wp_bootstrap` with #34's open callee hypotheses), but at `bootstrap.spec`, which is false at this
shape (the #34 ledger, B4): `isMemberBootstrapped` sends `GET /members` to the other members through the round
tripper, a right `bootstrap.spec`'s precondition does not give, and its callee spec `isMemberBootstrapped.spec`
is over the single-process `http.HttpNet`, not the peer addresses across machines. A proof is missing two
things: #34's restated spec (`bootstrap.spec` with a round-tripper contract, of which `specDist` is the instance
at `etcd_safe`'s shape; `bootstrap.specDist_of_spec` already derives `specDist` from `bootstrap.spec`, so the
retirement is a swap), and `isMemberBootstrapped`'s GETs proved over S5's cross-machine net/http (the client
side of `httpAddrAt`'s peer protocols), which does not exist yet. A Go model or trusted code would not be
smaller: the code is translated and its first-start path proved over its callees' specs, so a model would
restate `bootstrap`'s whole first start (backend, WAL, cluster, raft's start) as new trusted code, where the
axiom is `bootstrap.spec`'s reviewed triple with four shape premises and one network right added.

## Axiom reviewed

- `bootstrap.wp_proof_dist [π : Net.NetProtoGS] : bootstrap.specDist`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/bootstrapDist.lean`); statement in
  `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrapDist.lean`; `etcd_dist.bootRTOk`, `httpAddrAt`,
  `httpPeerSvc`, `noProxyEnv` in `Proof/.../examples/etcd/dist/S5Interim.lean`.
- Revision: `76ff2828d8` plus the docstring edit and `TestBootPeerHangs` (committed as `902c4a3a14`).
- Go: etcd fork `e94f33b50` (server/v3, client/pkg/v3, pkg/v3), go1.27.3.

**The claim.** `bootstrap.spec` (#34's, reviewed) restricted to: every initial-cluster entry one URL; at most
64 entries; `U.peer = U.initURLs cfg.Name'`; one client URL; and the persistent `bootRTOk γ id dir` in the
precondition (every other peer `pid ∈ γ.vs` whose entry is `http://a` has `httpAddrAt γ pid a`; the four proxy
variables empty). Otherwise `bootstrap.spec`'s premises, precondition and post; a failure is a returned
`err ≠ nil`. What it adds over `bootstrap.spec` in Go is `isMemberBootstrapped`'s `GET <peer>/members`
(`cluster_util.go:41-55`, `:69-121`): where the attacks went.

## Attacks tried

- **A1. A `/members` answer `[null]` (panics in Go; blocked in Lean).** `getClusterFromRemotePeers` decodes into
  `[]*membership.Member` (`cluster_util.go:98`); `NewClusterFromMembers` (`:122`) does `c.members[m.ID] = m`
  (`membership/cluster.go:101`): a nil dereference inside `bootstrap` (`TestNullMemberAtPeer`). Blocked: each GET
  target `http://a` is in `dir pid`, so `bootRTOk` gives `httpAddrAt γ pid a`; `a`'s acceptor protocol is the
  opaque `httpPeerSvc γ pid .2`, per connection, so no proof writes on an accepted connection at `a`; the only
  writer is `PeerServe_dist` (its `httpAddrAt γ id pa`, `γn.N = srvNet γ`, `peerHandlerOf h s` of a started
  `srvNetMember γn s id`), so the answer is etcd's `peerMembersHandler` (`etcdhttp/peer.go:112-120`: the JSON of
  `cluster.Members()`, never `null`). Other routes to `a` are closed: `bridge.New` needs `netAddrLeft a`
  (exclusive with the address invariant `addr_set_proto` made); grpc's serve path needs `grpcAddrAt a` (an
  address's protocol is set once); the single-process HTTP registry needs `httpAddrNet` (closed 2026-11-24); a
  wildcard listener's `lisUnset` is disjoint from `addrUnset a` (`addrs_lis_start`). Load-bearing: R1.
- **A2. An HTTP proxy (panics in Go; blocked by `noProxyEnv`).** The transport's `Proxy` is
  `http.ProxyFromEnvironment` (`client/pkg/v3/transport/transport.go:42`); with `HTTP_PROXY` at a stand-in
  answering `[null]` and a non-loopback peer URL, Go panics the same way (`TestProxyNull`). `noProxyEnv` has the
  four variables `""`, which Go's `getEnvAny` treats as unset; `NO_PROXY` and `REQUEST_METHOD` only turn a proxy
  off. Go reads the proxy environment once per process (`sync.Once`); `osEnvIs`'s whole-run reading covers it.
- **A3. A dial to another address than `httpAddrAt`'s (blocked).** Go dials `canonicalAddr(URL)`; `httpAddrAt`
  contains `addrTok a`, hence `addrOk a` (`GooseLang/Ext/Net/Impl.lean`: canonical `d.d.d.d:p`, a valid
  non-ephemeral port), for which the dial address is `a`. `bootURLsPlain` gives scheme `http` and no path,
  query, user or fragment, so the GET's base URL is `"http://" ++ Host`.
- **A4. GETs to uncovered peers or to this member (blocked).** `getRemotePeerURLs` (`cluster_util.go:131-141`)
  skips this member by name and takes the others' URLs from the cluster built from `bootCfgRO`'s map: exactly
  `dir pid` for `pid ∈ γ.vs = bootGo.ps`, `pid ≠ bootGo.id` (ids distinct, `initMapOk`). Duplicate URLs are
  refused by `CheckDuplicateURL` (`config.go:214`) with an error.
- **A5. Non-answers (Go answers `false` or returns an error).** Refused, hanging or closed connections
  (`TestBootThreeMembers`' first member, `TestBootPeerHangs`; the client timeout is the bootstrap timeout, a
  zero one may hang: non-termination, no counterexample); a redirect is not followed (`CheckRedirect` returns
  `ErrUseLastResponse`, `:76`; the body does not decode); a truncated body (`continue`); an empty list (an
  error, then `false`, `:121-124`); this member listed with client URLs: the error `member %s has already been
  bootstrapped` (`bootstrap.go:434-435`, `TestBootErrors`), which the post allows. A real answer is compared by
  id only (`:46-47`) and writes nothing to the local cluster.
- **A6. The in-place sort of B4 (blocked by the shape).** `advertiseMatchesCluster` (`config.go:249-256`) sorts
  the map's own slice: one element, `sort.Sort` writes nothing, `bootCfgRO`'s `↦*□` holds; `urlsEqual`
  (`netutil.go:147`) sorts its own copies; equal URLs give equal strings, so no DNS. A name missing from the map
  is an error from `hasLocalMember` (`config.go:241-246`) first.
- **A7. Peer TLS and the transport (blocked).** `bootCfgOk`'s `tlsEmpty`; an unresolvable `LocalAddr` is
  `NewTransport`'s error, returned (`bootstrap.go:72-75`); `RegisterProtocol("unix")` does not panic
  (`transport-emptycn.md`).
- **A8. The Lean statement (nothing found).** `bootRTOk` is persistent and the post is `bootstrap.spec`'s, so
  `specDist` is weaker than `spec`; `specDist_of_spec` and `BootDist.lean`'s derivations strengthen nothing. No
  entailment from persistent points-to facts to a pure conclusion (the cross-world check does not apply).
  `httpAddrAt` is indexed by `γ` and `pid`, an address set once: the GETs reach only members of `γ`.

## Go tests (at the pin, `TMPDIR` on disk)

`examples/axiomcx/bootstrapdist` (after R1):
```
--- PASS: TestBootThreeMembers   a booted, peers unreachable; b, c booted after 1 GET /members served by a
--- PASS: TestBootErrors         cannot access data directory: ... not a directory;
                                 member 71c9e24b01d4ac59 has already been bootstrapped
--- PASS: TestBootPeerHangs      a booted after 2.27s with b hanging
--- PASS: TestNullMemberAtPeer   a stand-in answering [null] at a peer address: bootstrap panics:
                                 runtime error: invalid memory address or nil pointer dereference
--- PASS: TestProxyNull          a proxy answering [null] for a peer URL: bootstrap panics: (the same)
```
In the last two the stand-ins sit where Lean admits no writer: they show what `bootRTOk` carries; they do not
refute the axiom. The reviewer's own copy also ran a redirect case (`err=nil`, no panic).

## Required changes, and what was done

- **R1** (the axiom's docstring and the evidence package): say that a non-etcd `/members` answer panics
  `bootstrap` and that the axiom relies on `bootRTOk` for both routes; add the two tests (the proxy case in a
  child process). Done: the docstring's "What the round-tripper contract carries" paragraph;
  `TestNullMemberAtPeer`, `TestProxyNull`; `nonissues/etcd-bootstrap-members-null-panic.md` (input only a
  non-member peer sends).
- **R2** (`httpPeerSvc`'s docstring, `S5Interim.lean`): its intended reading lists the rafthttp/leasehttp
  requests; the dialer's requests now include `bootstrap`'s read-only `GET /members`. Done. `PeerServe_dist`'s
  next review should cover serving it (etcd's `peerMembersHandler`, read-only).
- Optional, not done: the 64-entry and one-client-URL premises are not needed by `bootstrap`'s Go; they are
  `etcd_safe`'s shape, harmless restrictions.

## Not tried

No Lean counterexample (none needed). Goroutines `net/http` leaves after the GET (idle connections,
`MaxIdleConnsPerHost = 1024`) are not counted against `ThreadBoundLe`: not a panic, and the same holds for
every opaque library that spawns goroutines. `bootstrap.spec` itself, `PeerServe_dist` and `NewServer_dist`
belong to their own reviews. Address aliasing in the net extension (covered by `addrOk`). The restart and crash
side is out of scope (`etcd_safe`'s crash side uses `bootstrapCrashContract`, untouched here).

## Re-review (2026-11-25, a second fresh agent): survives

R1 and R2 applied correctly; the Lean statement unchanged (`git diff 902c4a3a14 -- Spec/` empty; only
docstrings changed in the axiom file and in `S5Interim.lean`); the cited Go matches the pin
(`cluster_util.go:98`, `:122`; `membership/cluster.go:101`; `etcdhttp/peer.go:112-120`; `transport.go:42`);
`addrOk` is inside `httpAddrAt` (`addrProto` holds `addrTok a`). The evidence test passes (5/5). New attacks,
none through: a nil local member (`hasLocalMember` runs first, `config.go:208`); a started peer of `γ` with a
different cluster view (clones of non-nil entries, compared by id: `false` or the "already bootstrapped"
error); malformed headers or bodies (`continue`), `//members` (excluded by `bootURLsPlain`), HTTP/2 (no TLS);
CGI mode and lowercase-only proxy variables (with all four `""`, no proxy); connection reuse (a pooled
connection goes back only to the same address and protocol). No further required change.
