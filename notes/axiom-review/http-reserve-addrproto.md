# Review: `http.reserve` and an address's net protocols (2026-11-24)

**Target.** `axiom http.reserve` (`Proof/net/http/Axioms.lean`, D39a), as on branch `http-register-addrleft/2026-11-24`
(`31edea7d90`, `register` already consuming `netAddrLeft a`): it took `httpProtoFree a` alone and gave
`httpProtoAt a P ∗ httpProtoOwn a P`. With `RoundTrip`'s spec through `transport.NewTimeoutTransport`'s
`roundTripperOk H` (its post `□ ∃ w, (H.proto R.host).resp R γk st w`, `Boundary.lean`) and the net laws.

**Finding (refuted).** Found by a sweep of the trusted HTTP boundary. `RoundTrip` promises a client of `a` the reserved
protocol's `resp` from the reservation on, whoever answers at `a`; nothing tied `a`'s net protocols to HTTP. A program
reserves `a` for a protocol `P` whose `resp` excludes status `200` (`P.srvOk` holds: only the server's own statuses and
`204`), never registers `a`, listens at `a` (`net.Listen.spec`, `netListenerAt l a ∗ netAddrLeft a`), sets `a`'s net
protocols to trivial ones (`addr_set_proto_tok`, or keeps `netPend a ∅` so that `Accept`'s `Qok` is vacuous), accepts
the client's connection and writes `HTTP/1.1 200 OK`. `RoundTrip` returns `200`; its post says `st ≠ 200`.

- **Go:** `examples/axiomcx/httpreserve/` (`TestMainPanics`; go1.27.3; 5/5 on the sweep, 1/1 here).
- **Lean (sketch, not built):** `reserve` (from `startRights`' `httpProtoFree a`), `net.Listen.spec` (`netAddrFree a`,
  `netAddrFrees_start`), `netProto_alloc`, `addr_set_proto_tok`, `Listener.Accept.spec_addrOk` with `accept_au`,
  `writeP` of the raw answer; `NewTimeoutTransport` (`roundTripperOk`), `NewRequest_ok`, `WithContext_ok`, the
  `RoundTrip` post at `R.host = a`. No etcd axiom. `register`'s fix (`http-register-addrleft.md`) does not apply: the
  program never registers `a`.

**Fix** (`notes/decisions.md`, "`http.reserve` fixes the address's net protocols"): `reserve` also takes `httpAddrNet a`
(`Proof/net/http/AddrNet.lean`, persistent): `a`'s net protocols are the opaque `httpNetCliP`/`httpNetSrvP`, set once by
the theorem `httpAddrFree_set` from `netAddrFree a` (consumed; `addrClaim a` kept, as `httpAddrFree a`). After it:

- no `netAddrFree a` (its `addrUnset a` is spent), so no `net.Listen.spec` at `a` and no `netAddrLeft a`: the program
  cannot give `a` protocols of its own;
- a raw program may still listen at `a` (`listen_au` from the persistent `addrProto`), accept and read, but its
  connections meet `a`'s opaque protocols: a raw acceptor can write nothing a client reads (an empty write, then a
  close: an error `RoundTrip`'s spec allows), a raw dialer to `a` nothing either (`httpNetCliP`), which also keeps
  `register`'s hole closed without `netAddrLeft a` in `register`'s premise (now `netListenerAt l a ∗ httpProtoOwn a P`
  again);
- the member's peer listener comes from `httpAddrFree a` (`net.Listen.specHttp`, a theorem from Net's `Listen` spec).

Its callers: the clusters' reservations (`netHttp_reserve3`, `netHttp_reserveL`: each address's `netAddrFree` with its
`httpProtoFree`, through `http.reserveAddr`), the five registering members (`etcdstart.NewMember`, `StartMemberAuth`,
`auth3.startMember`, `restart`/`restartN`'s `newMember`: `net.Listen.specHttp`, no `netAddrLeft`). Trust-shrinking for
`reserve`; `register`'s premise loses `netAddrLeft a`, which the reservation's net fact subsumes. Two new opaque
definitions (trusted text, no law, as grpc's). The drafts of `Proof/net/http/ListenerClose.lean` follow (the close gives
back `httpAddrFree a`, never a fresh `netAddrFree a`; `registerClosable_spec` as `register`).

## The listener's tie (a second finding, the same day)

**Finding (refuted, pre-existing on `lean`).** An independent `axiom`-skill review of the fix above (`de16250167`) found
`register` open to a third route: `netListenerOpen l a` (`Proof/net/InvNet.lean`) was `∃ t lv, ⌜l = *TCPListener t⌝ ∗
netLis lv a true ∗ netLisAt lv a`, nothing tying the Go pointer `t` to the extension's listener `lv` (Net's `isListener`
holds it, `lisAt t lv x`: `t ↦□ TCPListener{lid: lv, ...}`; `net.Listen`'s proofs dropped it). So the listener facts
of the reserved `a` repack around the Go value of a raw listener at an unreserved `b`; `register lb a P` and `Serve_ok`
promise `b`'s handler `P.req` of a raw `POST` the program writes to `b`. Variant: swap two reserved addresses'
listeners, and a `RoundTrip` client of `a` reads `b`'s `200`. The same reaches `grpc.start` and `bridge.New`, the other
axioms over `netListenerAt`.

- **Go:** `examples/axiomcx/httpregfwd/` (`TestMainPanics`, the handler's goroutine panics; 5/5 on the review, 1/1
  here).

**Fix.** `netListenerOpen` (and so `netListenerAt`) keeps the tie, `lisAt t lv x`; `net.Listen`'s two proofs
(`Proof/net/Listen.lean`, `Proof/net/ListenHttp.lean`) keep it from Net's `isListener`. Nothing else builds the
predicate (its consumers are axioms), so no consumer changes. Trust-shrinking: a stronger definition under the
premises of `register`, `grpc.start`, `bridge.New`.

**Re-review (the same day, at `77d29e37ea`).** An independent re-review found the tie, `reserve`/`reserveAddr`/
`register`/`Serve_ok`/`net.Listen.specHttp`/`AddrNet`, `grpc.start`/`start'`/`grpcServeTok`/`Serve` and `bridge.New`
all survive (listener swaps, close and reuse, copies, wrappers, the other net APIs, re-listening, grpc and the bridge
at reserved addresses). Caveat: `grpcAddrIs_agree` is sound only because the listener `grpc.start` consumes stays open
for the rest of the run in the model; a future `Server.Stop`/`GracefulStop` spec that gives back the listener or the
address must revisit it (as `ListenerClose.lean`'s drafts must for HTTP). Docstrings corrected: an address may be
listened on again after a `Close` (`listen_au`); what is once per run is the claim `addrClaim a` and the registration.
