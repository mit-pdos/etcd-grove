# Review: `http.register`'s precondition and an address's net protocols (2026-11-24)

**Target.** `axiom http.register` (`Proof/net/http/Axioms.lean`, D38c/D39a), as on `lean` at `91ca351121`: it took
`netListenerAt l a ∗ httpProtoOwn a P`. With `http.reserve` and `http.Serve_ok` (`Serve_spec`, `handlerOk`,
`Boundary.lean`).

**Finding (refuted).** Found by review 5 of etcd-dist's interim axioms (`notes/putget-dist-plan.md` §12 on branch
`dist-putget-interim/2026-11-24`), the `axiom` skill. The http boundary's closed-world argument ("every request a
server of the program receives comes from a client of the program that went through `RoundTrip`", `Boundary.lean`'s
header) stopped holding at phase 7 S2's interface: `net.Listen` also returns `netAddrLeft a`, from which the program
sets `a`'s net protocols (`addr_set_proto_tok`) to trivial ones, dials `a` (`dial_au`) and writes any bytes
(`writeP`). `Serve_ok` then promises the handler `□ (H.proto a).req R` of a request the protocol excludes.

- **Go:** `examples/axiomcx/httpaddrleft/` (`TestMainPanics`: the protocol says every request is a `POST`, the program
  writes a raw `GET`, the handler's goroutine panics; go1.27.3; 5/5 on the review, 1/1 here).
- **Lean:** `http-register-addrleft/SKETCH.lean.txt` (not built): `net.Listen`, `netProto_alloc`, `addr_set_proto_tok`,
  `http.reserve`, `http.register`, `Serve_ok`, `net.Dial`, `Write`; no etcd axiom.
- A variant at an etcd-dist address (route B: `etcdAddr_set`, then `listen_au`): grpc-go's preface `PRI * HTTP/2.0`
  reaches the handler (Go's server runs it with method `PRI`: `http-register-addrleft/httph2c_main.go.txt`).

**Fix** (`notes/decisions.md`, "`http.register` consumes what sets the address's net protocols"): `register` also
consumes `netAddrLeft a`, as `bridge.New` since its fix. The program that registers `a` has spent what sets `a`'s net
protocols; route B leaves `netPend a` inside `addrProto`'s invariant, so it cannot form `netAddrLeft a` either. Its
five callers (`etcdstart.NewMember`, `StartMemberAuth`, `auth3.startMember`, `restart`/`restartN`'s `newMember`)
pass `net.Listen`'s `netAddrLeft`, their specs unchanged.
