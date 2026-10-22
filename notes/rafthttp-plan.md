# Plan: rafthttp verified, the trust boundary pushed down to HTTP

Stage 0 (scoping) of 2026-10-22, at `lean` `a00708b853`; D33 (`notes/decisions.md`; (A) approved
by the user, 2026-10-22). Nothing proved yet. The inventory below is of the etcd pin
(`upamanyus/etcd` `188113160d`; `server/etcdserver/api/rafthttp`, test files excluded; the fork has
no commits in the package: `CutPeer`/`MendPeer` are upstream's test hooks).

## Goal

Today rafthttp is names-only and its behaviour is assumed (D21b (A)): five axioms
(`Transport.Start`, `AddPeer`, `AddRemote`, `CutPeer`, `MendPeer`), `EtcdServer.RaftHandler`'s
(`raftHandlerOf`) and `net/http.Serve`'s, over the network contract of
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Net.lean`: a message given to `Send`
with its bundle (`netBundle`: persistent `P`, one-shot `O`) reaches the `Process` of the member
holding the slot of its `To` as a fresh copy (`netRecv`, `wireEq`), possibly lost; the snapshot
stream saves the database before `Process` (`netSnapBundle`, `snapDirInv`). Every multi-member
result (`linkv3_safe`, `linkv3p_safe`, `linkv3p_watch_safe`, reconfiguration) rests on it.

The goal: translate rafthttp's message path and prove that contract from trust-boundary specs of
`net/http` (and the few other packages it calls), so that the five transport axioms and
`RaftHandler`'s become theorems and what remains assumed is a generic statement about HTTP. **The
server's and the examples' proofs keep `Net.lean`'s contract as their interface** (it becomes the
transport's proved spec), so none of them changes.

## What rafthttp does (the inventory)

About 2,600 lines without metrics (`stream.go` 607, `http.go` 417, `transport.go` 332, `peer.go`
246, `msgappv2_codec.go` 189, `snapshot_sender.go` 146, `util.go` 142, `pipeline.go` 131, `remote.go`
72, `probing_status.go` 68, `peer_status.go` 63, `msg_codec.go` 44, `urlpick.go` 34; `metrics.go` 159).

- **Send.** `Transport.Send` looks the destination up (`peers`/`remotes` under `t.mu`) and calls
  `peer.send`, which drops the message if the peer is paused (`CutPeer`) and otherwise picks a
  channel without blocking (full: dropped, `ReportUnreachable`): a stream writer's `msgc` (4096)
  if its stream is working (MsgApp to the `msgappv2` stream, others to the `message` stream), else
  the pipeline's `msgc` (64). MsgSnap goes by `SendSnapshot`, never `Send` (D22 S-i).
- **Streams are pulled.** The *receiver* B dials the sender A: `streamReader.dial` sends
  `GET /raft/stream/{msgapp|message}/<B>` (headers: from, to, versions, cluster id, peer URLs) by
  `RoundTrip`; A's `streamHandler` checks it, writes `200`, flushes, hands the `ResponseWriter` to
  A's `streamWriter` goroutine (`attachOutgoingConn`) and blocks until the writer closes it.
  The writer encodes each message into the response and flushes (batches of up to 2048). B's
  `decodeLoop` reads `resp.Body`, decodes, and puts each message on `recvc`/`propc` (4096, non-
  blocking: full, dropped); two goroutines per peer call `Raft.Process`. A broken stream drops the
  writer's queued messages (`closeUnlocked` replaces `msgc`) and the reader redials (rate-limited).
- **Pipeline.** Four goroutines per peer POST one marshalled message each to `/raft`
  (`createPostRequest`), read the response, map the status (`204` ok, `403` removed, `412`
  incompatible); no retry. The receiver's `pipelineHandler` reads the body (`io.ReadAll`),
  unmarshals and calls `Process` synchronously in net/http's handler goroutine.
- **Codecs.** `messageEncoder`: an 8-byte big-endian length and `proto.Marshal`. `msgappv2`: a
  one-byte tag (heartbeat, "AppEntries", full message) and **a stateful delta encoding**: an
  AppEntries frame carries only the entries and the commit index, and the decoder rebuilds From,
  To, Term, LogTerm and Index from its own state (`msgappv2_codec.go:192-199`), in lockstep with the
  encoder's (a fresh pair per connection).
- **Delivery is at most once and unordered across paths** (four pipeline workers, stream and
  pipeline interleaved, `recvc`/`propc` drained separately): what the contract says (possibly
  lost, no order), so nothing is lost by not proving FIFO.
- **`CutPeer`/`MendPeer`** pause/resume the peer (drop outgoing, drop stream-inbound after
  decoding; pipeline and snapshot inbound still processed) or stop/start a remote's pipeline
  (`issues/etcd-rafthttp-cutpeer-twice-remote-panic.md`, with the race noted 2026-10-22).

External calls: `net/http` (`RoundTripper.RoundTrip`, `NewRequest`, `Request.WithContext`, headers,
`Response.StatusCode`/`Body`, `ResponseWriter.Header/WriteHeader/Write`, `http.Flusher`,
`http.Error`, `ServeMux`, `Transport.CloseIdleConnections`); `io`, `bytes`, `encoding/binary`
(`Read`/`Write` through reflection), `context`, `time` (ticker, `AfterFunc`), `sync`, `errors`,
`fmt`, `strings`, `path`, `net/url`; zap; `xiang90/probing`; `x/time/rate`; semver; prometheus;
`client/pkg/v3/{transport,types}`; `pkg/v3/{pbutil,ioutil,httputil}`; raftpb and `proto`;
`snap`; `v2stats`.

## The proposed boundary (D33)

**HTTP at the level of bytes**, true of `net/http` over TCP, with the closed-world facts the
current specs already make (`netAddrFree`, `netListenerAt`: the program's peer addresses are its
own):

1. **Routing.** `http.Serve(l, mux)` on the listener bound at `a` runs, for each request sent to
   `http://a/...`, the handler the mux registered for its path, on its own goroutine, with the
   request's method, path, headers and a body reader; it recovers a handler's panic (the
   connection dropped). A request reaches only the server listening at its URL's address.
2. **A request's body.** The handler's body reader yields, in order, a prefix of the bytes the
   client's request body produced, then EOF only if they were all sent; or an error.
3. **A response stream.** `RoundTrip` returns an error or a response whose status and headers are
   those the handler set before its first write or flush, and whose body reader yields, in order,
   a prefix of the bytes the handler wrote **and flushed** (from any goroutine, before it closed
   the connection), then EOF or an error. A connection may fail at any time (both sides then see
   errors). This is the per-connection byte-stream fact the streams rely on; it names the
   connection (a ghost name shared by the handler's `ResponseWriter` and the client's body).
4. **Cancellation.** A request's context cancelled makes `RoundTrip` or a body read return an
   error.

**Ghost state does not cross the wire.** Bytes carry no Iris resources, so the bundles move through
an invariant, the **mailbox**: `Send` deposits each message's bundle keyed by its wire content
(the `MsgSt` up to `wireEq`; a multiset: the same content may be sent twice); the receiver, having
decoded bytes into a message, proves it equal on the wire to a deposited one and withdraws that
bundle (the persistent part copied, the one-shot part taken; a second delivery of the same bytes
uses the payload's `dup` for a message not `once`, which is what `NetPayload` provides). Per
connection, a stream's invariant relates the bytes written so far to the encodings of the messages
deposited for it (with the encoder's states), so a decoded prefix names deposited messages.
Proposed alternative (B): a resource-passing HTTP boundary (a request or a flushed write carries a
resource to the handler or the reader). Simpler proofs, but a stronger and less standard trust
statement (Go's HTTP carries no resources); recommendation (A), the bytes-level one with the
mailbox.

**Stays assumed** (beside HTTP): the concurrency bound `netProcSlots` (2^29 concurrent `Process`
calls: handler goroutines are unbounded, as today, a physical fact); `time`, `rate.Limiter.Wait`
(returns or the context's error), zap, prometheus and the probes as no-op specs; the semver
checks with arbitrary results (they can only cause a rejection, a loss); `proto`'s marshal and
unmarshal over raftpb (existing specs); `encoding/binary`'s `Read`/`Write` of `uint64`/`uint8`.
**The snapshot stream** (`snapshot_sender.go`, `snapshotHandler`, `SaveDBFrom`) stays an axiom in
this track (D22's owner's area): `SendSnapshot` keeps today's `netSnapBundle` contract as its own
trust-boundary spec.

## Stages

0. **(this) Scoping**: the inventory, the boundary, D33 drafted. Stop for approval.
1. **Translation.** rafthttp's message path with bodies (`transport.go`, `peer.go`, `stream.go`,
   `pipeline.go`, `remote.go`, `http.go`'s pipeline and stream handlers, `msg_codec.go`,
   `msgappv2_codec.go`, `urlpick.go`, `peer_status.go`, `util.go`'s request helpers); metrics,
   probing and the snapshot sender names-only. Goose gaps found here (the inventory's list:
   interface embedding in `outgoingConn`, a function-local type in the snapshot sender, Go 1.26's
   `new(expr)` in the codec, `binary.Read` through reflection, an unchecked `w.(http.Flusher)`)
   are worked around (trusted models, `Code/**.toml`) or recorded in
   `notes/perennial-changes.md`.
   **Done 2026-10-22** (branch `rafthttp-plan`; the two `opaqueInitsOk` accepted by the user):
   Goose translates the whole message path (90
   functions, both codecs included, no unsupported feature). Names only, besides the above: the
   package variables' initializers (`errMemberRemoved`, `supportedStream`, `ConnReadTimeout`, the
   URL prefixes, ...: they call `errors.New`, `fmt.Errorf`, `path.Join` and `proto.Size`, which
   `gen-init.py` would need custom steps for), run by `Init.lean`'s `opaqueInitsOk`; and
   `waitSchedule` (`runtime.Gosched`: Perennial has no `runtime` initializer proof). New
   names-only packages: the standard library's `path`, etcd's `pkg/v3/ioutil` and
   `pkg/v3/httputil`. **Trust base +2** (537 -> 539, accepted by the user): the
   `opaqueInitsOk` of `path` (`ErrBadPattern`) and of `ioutil` (`ErrShortRead`, `ErrExpectEOF`,
   `defaultBufferBytes`), the usual "an untranslated variable initializer runs" axioms; they can
   go once those initializers are translated (with stage 2's variable facts). No statement changed.
2. **The HTTP boundary.** The specs of 1-4 above (`Spec/net/http/`), replacing `net.http.Serve`'s
   current spec (which mentions the raft network) by the generic one, and the mailbox and stream
   invariants (`Proof/.../rafthttp/`). Reviewed with the user before proofs rely on them. Also
   the package variables' values (translated initializers, or facts), which stages 4-6 read.
   **Design drafted 2026-10-22 for review: `notes/rafthttp-http-boundary.md`** (bytes and routing,
   per-address request/response protocols carrying persistent facts, the mailbox), **reviewed by the
   user 2026-10-22** (decisions at its end: the closed world accepted, the status faithful, `path`
   translated, the removal a parameter of rafthttp's spec for dynamic clusters). Since then:
   `path` translated with bodies (`Clean`, `Join`, `Split`, `Base`, `Dir`, with `internal/bytealg`'s
   `LastIndexByteString`; **trust base +1**, accepted by the user: `bytealg`'s `init()`, which detects CPU
   features and cannot be translated, assumed to run, `initFuncsOk`); **the boundary drafted in Lean**, `Proof/net/http/Boundary.lean`
   (definitions and spec statements, not axioms; nothing uses them yet): `HReq`, `Proto`, `HttpNet`,
   the client's `reqOwn`/`respAt`/`respReader`/`roundTripperOk`, the server's `reqAt`/`bodyReader`/
   `respWriter`/`handlerOk`, and the statements of `Serve`, `NewRequest`, the bodies' `Read`,
   `Write`/`WriteHeader`/`Flush`, `io.ReadAll`/`io.ReadFull`; then (2026-10-22, the rest) the
   headers (`canonKey`, `hdrSet`/`hdrGet`, `hdrOwn`/`hdrAt`, `Header.Set`/`Get`, `w.Header()`;
   `reqOwn`/`reqAt` now name the `Header` map and the `URL`'s `Path`), `http.Error`, routing
   (`patMatches`, `route`, `muxOwn`, `NewServeMux`/`Handle`, `handlerFor`, the mux's
   `handlerOk` from its registrations, with the protocol allowing the mux's own `404`/`301`
   for unrouted requests), `url.URL.String` (`urlOf` of host and path), and `encoding/binary`'s
   `Write` of a `uint64` and of a `uint8`-kind value and `Read` into a `*uint64`, stated over
   the writer's `Write` and the reader's `ReadFull` (Go's fast path; `uint64OfBE` opaque).
   The whole boundary is drafted; still statements only, for the user's review. (Stage 3 moved
   the `encoding/binary` statements to `Spec/encoding/binary/`, corrected: D33a.)
3. **Codecs.** `messageEncoder`/`Decoder` and the msgappv2 pair: decoding the bytes of an
   encoding gives a message equal on the wire (`wireEq`). **Risk**: the msgappv2 decoder rebuilds
   only From, To, Term, LogTerm, Index, Entries and Commit of an AppEntries frame; `wireEq`
   compares the whole message, so the encoder's tag choice must imply the other fields are the
   decoder's defaults. Either raft's MsgApps satisfy that (a fact from raft's side, of the kind
   `SentMsgOk` states), or `wireEq` is weakened to the fields `Process` reads (a change to
   `Net.lean`'s interface, then checked against the server's proof), or it is a finding.
   **The risk resolved, 2026-10-22, (a) chosen by the user** (D33a): raft's one `MsgApp`
   constructor sets only the fields the short frame carries (plus `From` = itself), so the shape
   goes into the sender's promise (`SentMsgOk`, `netBundle`); `wireEq` stays.
   **Done 2026-10-22, the simple codec** (`msg_codec.go`): `messageEncoder.encode` and
   `messageDecoder.decodeLimit` proved, over the generic protobuf specs (D33a: `PbType`,
   `proto.{Size,Marshal,Unmarshal}Pb`, the instance `pbMessage`), `pbutil.MustMarshalMessage`
   (translated with its body, proved), `encoding/binary`'s `Write`/`Read` of an integer
   (`Spec/encoding/binary/`), and contracts of the writer and the reader (`rafthttp/Codec.lean`:
   `writerAt` with a permission on what may be written, `readFullAt` with what is known of what
   was read). The encoder writes the frame (`msgFrame`: eight big-endian length bytes, then the
   encoding) of an encoding of the message, or fails; the decoder reads such a frame and returns
   the decoded message, owned. **Seven new axioms**, accepted by the user: the three generic
   `proto` axioms and the three `encoding/binary` ones, which no linked result reaches yet (no
   `Link.lean` for rafthttp until stage 6), and rafthttp's `errorsNewVarsInit`
   (`ErrExceedSizeLimit = errors.New(...)`), which every result reaching rafthttp's package
   initializer does: the baseline 540 -> 541 (the eight example collections +1). `decode` (the limit `readBytesLimit`, an untranslated variable)
   waits for the package variables' values.
   **Done 2026-10-22, the `MsgApp` shape in `SentMsgOk`** (D33a): `AppShape`, a premise of
   `raft.send` (`maybeSendAppend` proves it), carried to `netBundle` by the server's payload; no
   closed statement changed, trust base unchanged.
   **Done 2026-10-22, the msgappv2 pair** (`msgappv2_codec.go`, D33a): `msgAppV2Encoder.encode`
   and `msgAppV2Decoder.decode` proved over a pure model of the stream's frames
   (`rafthttp/MsgAppV2.lean`: `V2St`, the codec state; `V2Frame frm to cs w bs cs'`, the
   heartbeat, AppEntries and App frames; frames self-delimiting, `V2Frame.unique`). The encoder
   writes a frame of its message's wire content (given an `MsgApp` of raft's shape from `frm` to
   `to`, or the link heartbeat: `V2EncOk`); the decoder, knowing only that what it reads is
   compatible with a frame (`V2Compat`), reads one and returns a message of its content, owned,
   and the next state. Also proved: `isLinkHeartbeatMessage`, `pbutil.MustUnmarshalMessage`
   generically (`MustUnmarshalMessagePb`). `proto.MarshalOptions` translated (a struct of options;
   protobuf now imports `internal/pragma`, and raft's `Init.lean` runs its initializer). A finding:
   `issues/etcd-rafthttp-msgappv2-unbounded-lengths.md` (the decoder allocates whatever lengths
   the stream says). **New axioms, accepted by the user**: `proto.ClonePb` and
   `proto.MarshalAppendPb` (generic, `InvProto.lean`'s vocabulary), `pbEnc_ok` (what `pbEnc` is: a
   frozen message's encoding is an encoding of it, below `2^63` bytes), `v2stats.FollowerStats.Succ`
   (a no-op, as the metrics), and rafthttp's `linkHeartbeatMessage_init` (the heartbeat
   variable's untranslated initializer, `gen-init.py`'s custom kind); only the last is reached by
   a linked result yet (the baseline 541 -> 542).
   **Next**: `From` = the sender's id and `MsgMarshals` (no responses, known enums, including the
   entries') for the messages handed to `Send`; then stage 4 (the pipeline).
4. **Pipeline**, end to end: `pipeline.handle`/`post`, `pipelineHandler`, the mailbox withdrawal,
   `Process`. The simplest complete delivery path; first proof that the mailbox design works.
5. **Streams**: `streamWriter.run` (its five-way select, the queue replaced on close),
   `streamReader.run`/`decodeLoop`/`dial`, `streamHandler`, `attachOutgoingConn`; reconnection.
   The hardest stage.
6. **`Transport`**: `Start`, `AddPeer`, `AddRemote`, `Send`, `Handler` (and `RaftHandler` over
   it), `CutPeer`/`MendPeer` (peers only, `id ∉ rs` as today), proving today's axioms' statements;
   then the trust base drops by those axioms and `RaftHandler`'s, gains the HTTP specs.

## Costs and risks

- Several weeks, comparable to the watch client. Stage 5 carries most of the risk (a goroutine
  handing a `ResponseWriter` to another, a select with nil-able cases, a queue replaced on close).
- The mailbox keyed by wire content needs `MsgSt` content equality to be decidable enough to
  count deposits (a multiset of contents; GMap over an encodable key). Two equal messages sent
  concurrently are interchangeable, which is what makes the multiset sound.
- `wireEq` and the msgappv2 delta encoding (stage 3's risk above).
- Coordination: the snapshot stream and `SaveDBFrom` are the D22 owner's; this track keeps
  `SendSnapshot`'s contract unchanged, so the two can proceed independently. `Net.lean`'s
  interface is shared: changes to it (stage 3's weakening, if needed) go through both.

## Open

- Whether `remote`s (members not yet in the peer map) are in scope: today's specs allow
  `AddRemote`, so yes, with their pipeline only.
