# rafthttp stage 2: the HTTP boundary (design; reviewed by the user 2026-10-22)

D38 (A), `notes/rafthttp-plan.md` stage 2. Drafted and reviewed 2026-10-22 (decisions at the end);
the Lean statements follow it.

## What the translated code calls

From the stage-1 translation (`Code/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp.lean`):

- **Client side** (stream readers dialing, pipeline posting): `http.NewRequest(method, url,
  body)`, `Request.WithContext`, `Header.Set` on the request's headers, `RoundTripper.RoundTrip`
  (the round trippers come from the names-only `NewRoundTripper`/`newStreamRoundTripper`), the
  response's `StatusCode`, `Header` (`Get`) and `Body` (`io.ReadCloser`: `Read`, `Close`;
  `io.ReadAll`, `io.ReadFull`), `httputil.GracefulClose`, `(*http.Transport).CloseIdleConnections`.
- **Server side** (the pipeline and stream handlers, run by `http.Serve` through the transport's
  `ServeMux`): `http.NewServeMux`, `ServeMux.Handle`, the request's `Method`, `URL.Path`, `Header`
  (`Get`), `Body` and `RemoteAddr`, `ResponseWriter.Header().Set`, `WriteHeader`, `Write`,
  `w.(http.Flusher).Flush`, `http.Error`.
- **Pure helpers**: `path.Join`, `path.Dir`, `path.Base`; `url.URL`'s fields and `String`.

`http.Request` and `http.Response` are axiomatized types here (Goose does not translate their
structs), so the specs speak of their fields' addresses (`structFieldRef`), as the gRPC boundary
does for its messages.

## The model

**Bytes cross the network; ghost state does not.** The boundary says what a server receives and
what a client reads back, as bytes, plus one closed-world fact that lets the receiver use what the
sender proved about those bytes.

1. **Servers and their protocols.** A program's peer address `a` (the program's own: `netAddrFree`,
   then `netListenerAt` from `net.Listen`) is served by at most one `http.Serve(l, h)`. Before the
   servers start, the cluster fixes for each address its **request protocol** `Req_a` (a persistent
   predicate on a request: method, path, headers, body bytes) and **response protocol** `Resp_a`
   (a persistent predicate on a request and the response stream's bytes). These are ghost facts
   (a persistent `httpProto γh a Req Resp`), allocated with the network's names, alongside today's
   `γn.dir`.
2. **A request is delivered as sent, or not at all.** `RoundTrip(req)` to `http://a/...` either
   returns an error, or the request was handed, as a fresh `*Request` with the same method, path,
   headers and a body reader, to a handler goroutine of the server at `a`. The client must prove
   `□ Req_a(req)` of what it sends (method, path, headers, the body's bytes). The handler gets
   `□ Req_a(req)`. **This is the closed-world trust statement**: every request a server of the
   program receives comes from a client of the program that went through `RoundTrip`, with the
   bytes that client sent. A persistent property the client proved of those bytes therefore holds
   of the received ones.
3. **Body streams are prefixes.** The handler's body reader yields successive pieces whose
   concatenation `r` is always a prefix of the client's body `b`. It returns `EOF` only once
   `r = b`; it may return an error at any point, and then nothing more. So `io.ReadAll` gives
   either the whole body or an error, never a truncated body with `EOF`. The pipeline handler
   relies on this before unmarshalling.
4. **Response streams are prefixes.** The handler's `ResponseWriter` is an exclusive token
   holding the status it set and the bytes `w` written so far. `Write(b)` needs
   `□ Resp_a(req, w ++ b)` and may be called from any goroutine the token is passed to; this is the
   stream writer's use. The client's response, if `RoundTrip` returned one, has **the status the
   handler set** (`WriteHeader`, or `http.Error`'s; `200` if it wrote without setting one) and
   unconstrained headers (the code reads them only in version checks, which at worst reject). Its
   body reader yields pieces whose concatenation `r` is always a prefix of some `w` with
   `□ Resp_a(req, w)`. It ends with `EOF` or an error at any time.
   (Revised 2026-10-22: the first draft let the status be arbitrary, but a `403`/`410` is
   reported as `errMemberRemoved` on `Transport.ErrorC`, which stops the member, and today's
   contract promises nothing on `ErrorC`. The handlers answer `403`/`410` only when `IsIDRemoved`
   holds of the sender, never in the static clusters proved:
   `issues/etcd-rafthttp-misaddressed-403-member-removed.md`.)
5. **Failures.** Any `RoundTrip`, body read or `Write` may fail at any time; a cancelled request
   context makes them fail. `Flush` returns; it does not matter for safety. A handler's panic is
   recovered by `Serve` (the pipeline handler panics on a `Process` error that is not a
   `writerToResponse`, which the server's `Process` never returns).
6. **Routing.** `NewServeMux`/`Handle` build a mux whose `ServeHTTP` dispatches a request to the
   handler of the longest registered pattern that prefixes its path (`ServeMux`'s documented rule,
   a pure function of the patterns), or answers `404`. `Serve(l, h)` runs `h.ServeHTTP` for each
   request, so the handler's precondition is what 2-4 provide.

**What rafthttp's proof puts in the protocols** (not part of the boundary; the boundary is generic
in them):

- `Req_a` for `POST /raft` (the pipeline): the body is `proto.Marshal(m)` of a message deposited in
  the **mailbox** for `a`'s member.
- `Req_a` for `GET /raft/stream/{t}/<id>`: the requester is member `<id>` (identity only, no body).
- `Resp_a(req, w)` for that stream: `w` is the concatenation of the encodings (with the codec's
  states, for msgappv2) of messages deposited, sent by `a`'s member to `<id>`.
- **The mailbox**: an invariant holding, per destination, the multiset of messages sent (keyed by
  wire content, `wireEq`) with their bundles. `Send` deposits (and records a persistent "sent"
  fact, which is what the protocols mention). The receiver withdraws the bundle of a message it
  decoded: the persistent part `P` copied, the one-shot part `O` taken, or obtained by `dup` for
  a message not `once` (a second delivery of the same bytes). This works because `NetPayload`
  already has that shape.

Today's network contract (`Net.lean`: `netBundle`, `netRecv`, `netRaftOk`) stays the interface of
the server and example proofs. It becomes rafthttp's proved spec, its delivery derived from the
mailbox and the protocols.

## Why this boundary, and its trust content

- It is about bytes and routing, true of `net/http` over TCP (HTTP/1.1 framing makes a truncated
  body an error, not an `EOF`), plus the closed world the current specs already assume: a
  program's peer addresses are its own (`netAddrFree`) and only its own clients talk to them.
- The protocols move only **persistent** knowledge across the wire: what a sender proved of bytes
  it sent, which stays true. Nothing exclusive crosses: the mailbox moves exclusive resources, in
  the program's own ghost state. That is D38's (A), as approved. (B) would let a request carry
  exclusive resources, which is not something Go's HTTP does.
- Compared with today: the five `Transport` axioms, `RaftHandler`'s and `Serve`'s current spec
  (which names the raft network and states delivery to `Process`) are replaced by statements about
  HTTP alone. What stays assumed is in `notes/rafthttp-plan.md` ("Stays assumed").

## The package variables (the other stage-2 item)

The rafthttp variables the proofs read (`RaftPrefix`, `RaftStreamPrefix`, `supportedStream`,
`linkHeartbeatMessage`, `ConnReadTimeout`, the error values) get their values by **translating
their initializers** (`gen-init.py` steps over `errors.New`, `fmt.Errorf` and `proto.Size`'s
existing specs). `path.Join` in `RaftStreamPrefix`'s initializer, and `Dir`/`Base` in the stream
handler, need either `path` translated with bodies (it is plain Go over strings) or a trusted
pure model. The proposal is to translate it; the fallback is a trusted model. Once these are
translated, the two `opaqueInitsOk` accepted at stage 1 (`path`, `pkg/v3/ioutil`) can go too.

## Decisions (the user, 2026-10-22)

1. The closed-world statement of model point 2 (received requests are sent requests, so
   persistent facts about the bytes carry over): **accepted**.
2. The client sees the status the handler set (model point 4, revised); headers unconstrained:
   **agreed**.
3. `path`: **translated with bodies** (not a trusted model).
4. **Dynamic clusters** (the user: "we will have a dynamic cluster, so `errMemberRemoved` will be
   important"): the boundary stays as revised (the status the handler set, faithfully). What
   changes is rafthttp's spec: today's "nothing on `Transport.ErrorC`" (true of a static cluster
   only) becomes "`errMemberRemoved` for member `X` only with a witness that `X` was removed".
   The response protocol's status clause: a `403`/`410` only after the answering member's
   `Raft.IsIDRemoved(from)` returned true. **The removal is a parameter** of rafthttp's spec, a
   persistent predicate `removed X` supplied by the membership model (whoever builds the dynamic
   cluster's), and `IsIDRemoved`'s contract promises `true` only of removed ids. So rafthttp's
   proof does not depend on how removal is modelled. The server's handling of `ErrorC` (`run`
   stops the member on `errMemberRemoved`) then needs a spec that stopping a removed member is
   correct; today's `NewServer` assumes nothing arrives.

