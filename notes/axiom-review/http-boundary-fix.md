# The http-boundary fix's texts (self-review, 2026-11-14)

Branch `http-boundary-fix` (worktree `/shared/etcd-grove-auth3`), the fix of two findings of the
network fault review (etcd-grove-81's `/shared/tmp/coord-81/netfault/verify-rafthttp/`). Reviewed by
the fix's author with the `axiom` skill's attack list; an independent review is the coordinator's.

## Texts reviewed

- `http.handlerOk`, `http.handlerFor` (`Proof/net/http/Boundary.lean`; through them `Serve_ok`,
  `mux_handlerOk_ok`, `probing.NewHandler`'s axiom): a handler run receives `reqTicketOnce R γk :=
  ⌜onceOnly R⌝ -∗ reqTicket γk` in place of `reqTicket γk`.
- `http.onceOnly`, `http.noIdemKey` (definitions the statement above is written in).
- `http.srvStatuses`, `http.Proto.srvOk`, and `http.reserve` (`Proof/net/http/Axioms.lean`) taking
  `P.srvOk`; `roundTripperOk`'s text unchanged (its docstring and the round trippers' updated).

## Verdict

**Survives** every attack tried. One gap of the surrounding boundary found, not of the new texts:
the environment's HTTP proxy (below, "Found on the way"), fixed by a loopback-only `netAddrLit`.

## Attacks tried

1. **Two handler runs with the ticket** (the refuted case). A run gets the ticket only when
   `onceOnly R`: a method other than `""`/`GET`/`HEAD`/`OPTIONS`/`TRACE`, no `Idempotency-Key` nor
   `X-Idempotency-Key` present. Such a request is not `isReplayable` (go1.27.3
   `net/http/request.go:1561`, whatever its body), so `persistConn.shouldRetryRequest`
   (`transport.go:844`) retries it only after `nothingWrittenError` (no byte written: no server read
   it) or `http2isNoCachedConnError` (no connection used). HTTP/2's own retry
   (`internal/http2/transport.go:506`) is only after `errClientConnUnusable` (not sent), a `GOAWAY`
   past the stream (unprocessed by the protocol) or `REFUSED_STREAM` (Go's server refuses before
   running a handler). Go's server runs one handler per request read. `examples/premisefix/httpreplay`:
   a `GET` runs twice, a `POST` with a key (empty or not, any case) runs twice, a `POST` as rafthttp
   sends it runs once.
2. **A key the model does not see.** `noIdemKey` is over `R.hdr`'s canonical keys; the only writes
   of a request's headers are `Header.Set` (`HeaderSet_spec`/`HeaderSetPtr_spec`, canonicalizing as
   Go's `Set` does) and `setPeerURLsHeader`/`createPostRequest` (proved); `hdrOwn` is opaque, so no
   direct map write (`req.Header["Idempotency-Key"] = nil`, a presence Go counts) has a spec.
   `WithContext` shares the header map, as Go's shallow copy.
3. **Lower-case or empty method.** Go compares `valueOrDefault(r.Method, "GET")` case-sensitively;
   `onceOnly` excludes `""` and the four upper-case names, so a lower-case `"get"` is non-replayable
   in both (and `NewRequest_spec` admits only `GET`/`POST`).
4. **Body without `GetBody`.** Go then never replays (whatever the method); `onceOnly` ignores the
   body, so it calls more requests replayable than Go: only fewer tickets.
5. **A status no handler set** (the refuted case 2). Go's server answers itself with `400`, `417`,
   `431`, `501`, `505` (`conn.serve`, `readRequest`, `sendExpectationFailed`; HTTP/2's
   `serve400Handler` and `handleHeaderListTooLong`); no `408` in go1.27.3. The mux's own `404`/`307`
   are `mux_handlerOk_spec`'s premise; its `400` for `RequestURI == "*"` and `405` for method
   patterns are unreachable (paths start with `/`, `NewRequest_spec`; `litPathPat` patterns have no
   method). A handler returning without writing is excluded by `handlerDone`; a panicking one gets no
   response. Informational statuses are not returned by `RoundTrip` (`101` only if a handler sends
   it). `examples/premisefix/httpsrvstatus`: `431`/`417` through rafthttp's round tripper and the
   five over a raw connection, no handler run.
6. **Their headers and bodies.** `srvOk` asks `resp` at any bytes `w` (the reader's prefixes) and
   `rhdr R []`; the server's answers set only `srvKeys` keys (`Content-Type`, `Connection`,
   `Content-Length`, `Date`, `X-Content-Type-Options`), checked by the test, so `srvView [] hc`.
7. **Vacuity.** `raftProto_srvOk` proves the raft protocol meets `srvOk` (none of the five is `200`,
   `403`, `410`), so `reserve` stays usable; `srvOk` is a premise on the caller, which only weakens
   the axiom.
8. **A protocol registered without `srvOk`.** `httpProtoAt` is made only by `reserve` (opaque raw
   fact), and `roundTripperOk` asks `httpProtoAt R.host (H.proto R.host)`.

## Found on the way (fixed 2026-11-14, etcd-grove-81's decision: `netAddrLit` loopback only)

**The environment's proxy.** rafthttp's round trippers are `*http.Transport`s with `Proxy:
http.ProxyFromEnvironment` (`client/pkg/transport/transport.go:42,63` at the pin). With
`HTTP_PROXY`/`HTTPS_PROXY` set, a request to a non-loopback address goes to the proxy, which may
answer itself (`502`, `407`, ...) with a status neither a handler nor Go's server made, so
`roundTripperOk`'s `resp` promise is false of it. Loopback hosts are never proxied
(`httpproxy/proxy.go:178-185`), and the closed theorems' programs use `127.0.0.1` literals, but
`netAddrLit` admitted any IPv4 literal. Candidate fixes were a new world assumption (no proxy
configured for the program's addresses) or a loopback-only `netAddrLit`. **Fixed** by the latter
(etcd-grove-81, no new world assumption): `netAddrLit` asks the first octet `127`
(`Proof/net/InvNet.lean`), so every address of `As` is in `127.0.0.0/8`, which `useProxy` never
proxies; every closed theorem discharges `hAsLit` by `decide` over `127.0.0.1` literals, unchanged.
`examples/premisefix/httpproxy`: with `HTTP_PROXY` set, a request to `127.0.0.2` reaches the member,
one to `10.255.255.1` gets the proxy's `502`.

## Not tried

A Lean counterexample (none was needed: no attack got through); TLS (`HTTPS`) and HTTP/2 were read,
not run (rafthttp's closed paths are plaintext HTTP/1.1).

## The independent review (etcd-grove-81's, 2026-11-14) and its fixes

Three findings, each confirmed with a Go test, all fixed on this branch.

1. **BLOCKER, the closed-world wording.** "No code of `e` this repository does not verify connects
   to an address of `As`" is false of every multi-member program: etcd's names-only code sends the
   prober's `GET /raft/probing`, the version monitor's `GET /version` and bootstrap's `GET /members`
   to the peer ports, and the dials are `http.Transport`'s and grpc's (axiomatized, not verified).
   **Fix:** `addrsUnclaimed` (and `addrUnclaimed`, `netAddrFree`/`netListenerAt`, `net.Listen`)
   now say (a) the world assumption, unchanged: no other process connects; (b) what the program
   does: its connections carry requests of its verified or trust-boundary clients, or those three
   names-only requests, which reach no handler whose protocol needs knowledge. Checked: the
   `RaftHandler` mux routes only `/raft`, `/raft/stream/`, `/raft/snapshot`, `/raft/probing`
   (rafthttp `transport.go:163-166`), so `/version` and `/members` get its `404`. To make "needs
   no knowledge" true, `raftProto.req`'s stream branch is narrowed from "a `GET` of any path but the
   prober's" to "a `GET` under `/raft/stream/`" (`streamPfx`): before, `handlerOk` delivered
   `□ streamReq` of a `GET /version` that no client established (unused: the mux's `404` premise
   drops it, `TransportHandler.lean`, but a false fact in a trusted statement). Being `GET`s, these
   requests' runs get no ticket (`reqTicketOnce`), which also closes a hole the old `handlerOk`
   had: a names-only request's run received an exclusive ticket of an arbitrary name.
   `examples/premisefix/peerreqs` (three members, 8 s: `GET /raft/probing` 200 x20, `GET /version`
   404 x4, `GET /members` 404 x3).
2. **MAJOR 1, transparent gunzip and the transport's request headers.** A handler that sets
   `Content-Encoding: gzip` makes rafthttp's client read decompressed bytes, not a prefix of what
   the handler wrote (`examples/premisefix/httpgzip`). **Fix:** `hdrsReady` asks `respHdrsOk` of the
   committed headers: no `Content-Encoding` (nor `Trailer`, `Keep-Alive`, `Proxy-Connection`,
   `Upgrade`: `respNoKeys`). Request side, confirmed: the handler sees `Accept-Encoding`,
   `User-Agent`, `Content-Length` the client never set, so `reqAt`'s `hdrAt hm R.hdr` let a proof
   conclude `r.Header.Get("Accept-Encoding") = ""` (`examples/premisefix/httpreqhdr`). **Fix:**
   `reqAt` gives `hdrAt hm hs` with `reqHdrView R.hdr hs`: the client's value, trimmed, at every key
   but `reqTpKeys`.
3. **MAJOR 2, rewritten header values.** Go's server turns CR/LF into spaces, the client trims
   surrounding spaces and tabs, and a non-token key is not sent (`examples/premisefix/httphdr`).
   **Fix:** `respHdrsOk` also asks token keys and `hdrValOk` values (printable ASCII, no surrounding
   space). Request side: a non-token key or a CR/LF value makes `RoundTrip` fail; trimming is in
   `reqHdrView`.

Found while fixing them: **`Flush` before the commit.** Go's `Flush` on an uncommitted writer
commits `200` and the headers, after which `WriteHeader(500)` is ignored, but `Flush_spec` kept the
writer at `none` (`examples/premisefix/httphdr`, `TestFlushCommits`). **Fix:** `Flush_spec` asks a
committed writer (`st.isSome`); every caller flushes after `WriteHeader`.

The proofs: the three raft handlers prove `respHdrsOk` of what they set (`X-Etcd-Cluster-ID` an id's
hexadecimal string, `idStr_hdrValOk`; `X-Server-Version` and `Allow` constants); the handlers and
`addRemoteFromRequest` read the server's headers `hs` and carry the protocol's facts over with
`fromOkAt_view`/`peerURLsHdrOk_view` (`Pipe.lean`: an id string and a list of plain peer URLs are
unchanged by trimming).

**Attacks on the new texts** (self-review): HTTP/2's connection-specific headers, dropped on both
sides, are in `reqTpKeys`/`respNoKeys`; obs-text request values pass unchanged (only trimmed) and
are excluded from response values (`hdrValByte` is printable ASCII only), which only restricts
handlers; `canonKey` is idempotent on canonical keys, so the server's re-canonicalization is the
identity on `R.hdr`'s keys; `Host` never reaches `r.Header`; a key the client set among
`reqTpKeys` gets no promise.

## The second review (etcd-grove-81's, 2026-11-14)

1. **MAJOR, `Pragma`.** Go adds `Cache-Control: no-cache` to a header map it reads with `Pragma:
   no-cache` (`fixPragmaCacheControl`, go1.27.3 `response.go:218`, from `readRequest`,
   `request.go:1177`, and `ReadResponse`, `response.go:201`), on the server and on the client.
   **Fix** (key exclusions): `Pragma` in `respNoKeys`, `Cache-Control` in `reqTpKeys`;
   `examples/premisefix/httppragma`. The other headers Go touches on read, checked at go1.27.3:
   `Host` (moved to `r.Host`, `server.go:1087`, `request.go:1074`), `Transfer-Encoding`
   (`transfer.go:644`), `Content-Length` (`transfer.go:687,727,736`), `Connection`
   (`transfer.go:768`), `Trailer` (`transfer.go:790`): all in `reqTpKeys`, and on responses in
   `srvKeys` or `respNoKeys`; the server's write side drops only keys of `srvKeys`
   (`server.go:1231-1340`, `respExcludeHeader`).
2. **MINOR, leasehttp's forwarded `POST`s.** A follower's `RenewHTTP`/`TimeToLiveHTTP` send `POST
   /leases` and `/leases/internal` to the leader's peer port (`v3_server.go:553,682`): part (b) of
   `addrsUnclaimed` now names them. **Unminted tickets:** as `onceOnly` `POST`s, their handler runs
   receive `reqTicketOnce`, a ticket no `RoundTrip` minted (leasehttp's client is names-only).
   Harmless today: `raftProto.req` puts no premise on them, the mux answers `404` and takes no
   ticket, and no closed program forwards a lease request. **The coming auth-on-leases work (three
   members) reaches this path**: a verified handler of `/leases` must not rely on a ticket of such a
   request (or the boundary must stop handing one to requests no verified client sends).
3. **MINOR, the restart boundary.** After a served listener is closed and `http.Serve` returns, its
   keep-alive connections keep starting new runs of the OLD handler, even after the address is
   listened on again with another handler (`examples/premisefix/httpkeepalive`).
   `ListenerClose.lean`'s header now says so. No closed theorem uses `ListenerClose` and restart1
   has no listener; **restart3's review must account for those runs** (old-generation handler runs
   of a re-served address).
