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
   **Done 2026-10-22, what the encoders need of a sent message** (D33a, "The sent messages'
   facts"): no responses, for every message raft queues in every mode (`XfOk`, `isRaftMsg`; a
   forwarded request's from `raft.Step`, `NetMsgOk`, `fwdP`), and a `MsgApp` from its sender
   (`AppFrom id`, with the node's id in `XfOk`, `isRaftMsg` and `NodeNames`). `MsgMarshals` is now
   only "no responses": protobuf-go keeps an enum value outside the declared ones (**Open enums**
   below), so the enum bounds the wire model had are dropped and no entry-type invariant is needed.
   `Send` takes messages with no responses and `Process` gets copies with none (`netBundle`,
   `netSnapBundle`, `netRecv`; accepted by the user, 2026-10-23). No axiom added, baseline 542. The server's bundle keeps the sender
   existential: tying it to the transport's id is stage 6's (`srvEr` indexed by the member id).
   **Next**: stage 4 (the pipeline).

   **Open enums** (checked 2026-10-22). `raft.proto` is proto2, whose enums are closed: the spec
   says a decoder puts an undeclared value in the unknown fields. protobuf-go does not: it treats
   every enum as open (the protobuf "Enum behavior" page lists Go as non-conformant). The wire model
   (`PbMessage.lean`) relies on the Go behavior, checked by this test against the pinned raft
   (`raft37-goose-lean-a1`, `c8217eb`; run as `enumtest/enum_test.go` in a checkout of it, `go
   test ./enumtest/`; it passes, the unknown fields empty):

   ```go
   package enumtest

   import (
       "testing"

       "google.golang.org/protobuf/proto"
       pb "go.etcd.io/raft/v3/raftpb"
   )

   func TestOpenEnums(t *testing.T) {
       m := &pb.Message{Type: pb.MessageType(99).Enum(), To: proto.Uint64(2), From: proto.Uint64(1),
           Entries: []*pb.Entry{{Type: pb.EntryType(5).Enum(), Index: proto.Uint64(7), Data: []byte("x")},
               {Type: pb.EntryType(-3).Enum(), Index: proto.Uint64(8)}}}
       bs, err := proto.Marshal(m)
       if err != nil {
           t.Fatal(err)
       }
       m2 := &pb.Message{}
       if err := proto.Unmarshal(bs, m2); err != nil {
           t.Fatal(err)
       }
       if !proto.Equal(m, m2) || m2.GetType() != 99 || m2.Entries[0].GetType() != 5 ||
           m2.Entries[1].GetType() != -3 || len(m2.ProtoReflect().GetUnknown()) != 0 {
           t.Fatalf("not round-tripped: %v", m2)
       }
   }
   ```
4. **Pipeline**, end to end: `pipeline.handle`/`post`, `pipelineHandler`, the mailbox withdrawal,
   `Process`. The simplest complete delivery path; first proof that the mailbox design works.
   **Started 2026-10-23.** A gap found first: the pipeline carries one-shot messages (a
   `MsgReadIndex`'s read credit, a forwarded `MsgProp`'s tickets), and with only persistent facts
   crossing the wire a receiver cannot show no other delivery withdrew the same message's one-shot
   part. Go delivers a POST at most once (the client never replays one: `Request.isReplayable` is
   false for a `POST` without an `Idempotency-Key`; the server runs one handler per request read),
   so the boundary says so: **a request ticket** (the user's choice, 2026-10-23; D33b). The steps:
   - 4a. The boundary revised: `RoundTrip` takes a fresh exclusive ghost ticket (`reqTicket γk`)
     and the handler receives it; the protocols are indexed by the ticket's name; the handler's
     contract is a WP whose postcondition also covers a panic (`Serve` recovers one) and lends each
     invocation one of `netProcSlots` receiver resources; `io.ReadAll` over any reader keeping the
     prefix contract.
   - 4b. The pipeline's protocol and mailbox: a `POST /raft` request's body encodes a message `st`
     for the address's member, with `□ P st`, and a deposit per request, `inv (O st ∨ reqTicket
     γk)`, which the ticket's holder withdraws once. `pbMessage`'s `eqv`: a decoded (or cloned)
     copy of a message with no responses has none.
   - 4c. The receiver: `pkg/v3/ioutil`'s `limitedBufferReader` translated (a per-read cap), and
     `pipelineHandler.ServeHTTP` proved (the version checks with arbitrary results;
     `addRemoteFromRequest` a premise until stage 6; `Process` by `netRaftOk`).
   - 4d. The sender: `pipeline.post` (`createPostRequest`, `RoundTrip`, the response read and
     checked, the picker), `pipeline.handle`, `start`/`stop`.
   - 4e. The boundary specs the proofs use become axioms (for the user's acceptance).
   **Done 2026-10-23: 4a, 4b, 4c.** The boundary revised (tickets; a handler's writer non-`nil` and an
   `http.Flusher`; a received request's `RemoteAddr` ASCII and `Body` non-`nil`; `prefixReaderOk`);
   `ioutil.NewLimitedBufferReader` translated and proved; `Pipe.lean` (the protocol, the deposit,
   `pipe_withdraw`); `pbMessage`'s `eqv` keeps "no responses"; net/http's method and status
   constants and rafthttp's `RaftPrefix` initializer translated. **`pipelineHandler.ServeHTTP`
   proved** (`rafthttp/pipelineHandler__ServeHTTP.lean`) over its callees' specs as hypotheses: it
   calls `Process` with the decoded copy and its bundle (the persistent part from the protocol, the
   one-shot part withdrawn with the ticket), answers `204`, or `405`/`412`/`400` on a refused request,
   or `500` and panics on `Process`'s `ErrStopped` (`Serve` recovers). On the way, with the user's
   agreement (2026-10-23): `netRaftOk`'s `Process` returns raft's `nodeErr` (the server's `Process`
   spec says so); `errors.AsLeaf` (`Spec/errors/AsLeaf.lean`, a new trust-boundary axiom: `As` of an
   `errors.New` error outside the target's type set is `false`; Perennial's `As` axiom allows any
   result), with the method-set premise `ErrorStringNotWriter` and `errors.AsTarget writerToResponse`
   (a premise, as the examples' `AsTarget` of `EtcdError`); `addRemoteFromRequest` a premise of the
   handler (`pipeHandlerOk`) until stage 6. rafthttp's package fact gains `errIncompatibleVersion`,
   `ErrClusterIDMismatch`, `errStopped` (`errorsNewVarsInit`'s list: three more entries) and the four
   metric vectors (`receivedBytes`, `recvFailures`, `sentBytes`, `sentFailures`: **four new
   `<X>_init` axioms**, of `gen-init.py`'s `promvec` kind, reached by every result through rafthttp's
   initializer: baseline 542 -> 546, accepted by the user 2026-10-23). `prometheus.counterSpec` gains
   `Add` (the `WithLabelValues` axiom promises more). Still a spec only:
   `checkClusterCompatibilityFromHeader` (the version check: `semver`, `version`'s values).
   **Done 2026-10-23: 4d** (over its callees' specs as hypotheses; not linked until stage 6).
   `urlPicker.pick`/`unreachable` proved (`Picker.lean`, `pickerOk`). **`pipeline.post`** proved
   (`Sender.lean`: `pipeSenderOk`, `peerURL`, `postErr`): the request gets a fresh ticket and the
   message's deposit, the response is read and checked, and the error returned has an `Error()`
   (`http.errStrOk`, a boundary fact of net/http's errors). **`pipeline.handle`** proved
   (`Handle.lean`: `pipeMsg`, what a message on `msgc` carries, a bag; `pipeHandleOk`): each
   message is marshalled and posted; on failure the peer is deactivated, `ReportUnreachable`, the
   failure counted; on success activated, the bytes counted; on `stopc` it returns, handing its
   `Raft` resource to `wg.Done()`. **`pipeline.start`/`stop`** proved (`pipeFixed`,
   `pipeStarted`): `start` makes the channels, `Add(4)`, forks four `handle`s, each with one of
   four `R`s; `stop` closes `stopc` and `Wait` gives them back. Also proved: `peerStatus.activate`/
   `deactivate` (`PeerStatus.lean`), `isMsgApp`, `isMsgSnap`, and a local join `Add(4)`
   (`WaitGroupAdd.lean`: Perennial's covers `Add(1)` only, `notes/perennial-changes.md`). New
   trust items, for 4e: `fmt.SprintfID` (an axiom: `Sprintf` of a `types.ID`, whose `String` Go
   calls), `v2stats.FollowerStats.Fail` (an axiom, as `Succ`), two more metric-vector inits
   (`activePeers`, `disconnectedPeers`, `gen-init.py`'s `promvec` kind), and the net/http
   boundary fact `errStrOk`. Still specs only: `createPostRequest`, `checkPostResponse`,
   `checkClusterCompatibilityFromHeader` (their proofs need `http.StatusText`, untranslated,
   `version.MinClusterVersion`'s initializer, `strings.TrimSuffix`, and the `fmt.Errorf` errors'
   distinctness from `errMemberRemoved`).
   **Done 2026-10-23: 4e** (D33c, for the user's review). An address's protocol is registered
   once, from its listener (`http.register`: `httpListenerAt`, which `Serve` takes, and
   `httpProtoAt`, which `RoundTrip` asks of a request's host), so the specs stated for any `HttpNet`
   are sound; the sender gets its peer's hosts' registration (`pipeReg`, for stage 6 to establish).
   The eleven boundary specs the proofs use are axioms (`Proof/net/http/Axioms.lean`); reviewing
   them found three over-claims, fixed: `NewRequest` fails for a host `url.Parse` rejects
   (`urlHostOk`, in `urlPlain`), and `WriteHeader`/`http.Error` panic outside `100`-`999` and do not
   set a `1xx` status (both now ask `200 ≤ st ≤ 999`). None is reached by a linked result yet (stage
   6 links the pipeline), so the baseline is unchanged. **Accepted by the user (2026-10-23)**, all of
   stage 4's trust items: `http.register` and the eleven boundary axioms; `errors.AsLeaf`; the premises
   `ErrorStringNotWriter`, `ErrorStringLeaf` and `errors.AsTarget writerToResponse`;
   `context.WithCancelBackground`; `rafthttp.waitSchedule`; `fmt.SprintfID`;
   `v2stats.FollowerStats.Fail`; `errMemberRemoved` among `errorsNewVarsInit`'s errors (accepted
   with the inits: the six metric-vector inits, 542 -> 548).
   **Next**: the three callee proofs, each needing trust items for the user's review first:
   `createPostRequest` a fact of `version.MinClusterVersion` (its initializer untranslated: an
   init axiom, reached through the server); `checkPostResponse` `http.StatusText`, a request's
   `URL.String()` and `Header.Get` while built, and a fresh-pointer `fmt.Errorf` (a Perennial gap,
   `notes/perennial-changes.md`); `checkClusterCompatibilityFromHeader` semver's parsing and the
   version package. Then stage 5 (streams). Deferred by the user's choice (2026-10-23, "start stage
   5"): stage 5 first.
5. **Streams**: `streamWriter.run` (its five-way select, the queue replaced on close),
   `streamReader.run`/`decodeLoop`/`dial`, `streamHandler`, `attachOutgoingConn`; reconnection.
   The hardest stage.
   **Scoped 2026-10-23** (the user: "start stage 5"). Everything is translated with its body
   (`stream.go`, `streamHandler`, `closeNotifier`, `peer.attachOutgoingConn`, `util.go`'s helpers).
   The design (D33d, drafted for review):
   - **One-shot parts over a stream.** A stream carries many messages per request, so the pipeline's
     deposit per ticket does not do: the reader B withdraws the `i`-th frame's deposit with a token
     of its own, `i ↪[γw] ()` of a ghost map `γw` it owns the authority of (B reads frames in order,
     so it inserts `i` once). The writer A must deposit for B's `γw`, and B must know A's deposits
     are for its `γw`: the request's ticket names it, in a **registry** (`Rh`'s ghost map from
     ticket names to `γw`, its authority in an invariant), which B fills when it allocates the
     ticket, fresh for the registry (`dghostVar_alloc_strong` over the map's finite domain). No
     trust: the registry and the tokens are this repository's ghost state.
   - **The stream's response protocol.** For a stream `GET` to A of type `t` by B (the path's id),
     a `200` response's bytes are a prefix of a chain of frames (`t`'s codec: msgappv2's
     `V2Frame A B` from the initial state, or the message codec's `msgFrame`) of messages each a
     link heartbeat or a message to B with `□ P` and its deposit `inv (O st ∨ i ↪[γw] ())`; other
     statuses carry nothing (the reader treats them as failures; a `410` is reported on `ErrorC`,
     which stops the server: a loss). Frames are self-delimiting (`V2Frame.unique`, the message
     frame's length), so a decoded frame is the chain's `i`-th: what the decoders' premises
     (`V2Compat`, `readFullAt`'s knowledge) and B's withdrawal need.
   - **The writer** holds the `respWriter` (handed over by `attachOutgoingConn` through `connc`)
     with the chain written so far; each message it encodes is deposited first. (`run`'s five-way
     select, `msgc` replaced on close: a queued message's bundle is dropped, a loss.)
   - **Boundary items** (statements, for review at the end, as 4e): (1) **a fix to the draft
     `handlerOk`** (a statement only: `Serve` is not an axiom yet): a handler's WP must give back
     its `respWriter` (Go: "A ResponseWriter may not be used after the Handler.ServeHTTP method
     has returned"; the draft lets a handler leak it to a goroutine that writes after the return,
     which in Go writes to a released buffer); the stream handler gets it back from the writer
     when the writer closes the connection (`closeNotifier`). (2) A response body's `Close` from
     another goroutine while one reads (`streamReader.stop`/`close`; Go's body supports it): a
     persistent closer fact. (3) `semver.MustParse` may panic (on a peer's malformed
     `X-Server-Version`: the client side of the boundary does not constrain response headers);
     the comparisons arbitrary. (4) `rate.Limiter.Wait`, `transport.IsClosedConnError`,
     `httputil.GracefulClose`, `errors.Is` with arbitrary results where only a log or a status
     depends on them.
   - **`path`.** B's path is `path.Join(endpoint t, B's id)`, and A recovers `t` and the id by
     `path.Dir` and `path.Base` (and `types.IDFromString`). Specs of `path`'s `Clean`, `Join`,
     `Dir`, `Base` against pure models (translated with bodies since stage 2), and the lemmas
     for a clean prefix and one segment.
   The steps: **5a** the stream protocol (`Stream.lean`: the registry, chains, deposits,
   withdrawal; `raftProto`'s stream part); **5b** the writer (`streamWriter`: `run`, `close`,
   `closeUnlocked`, `writec`, `attach`, `stop`, `startStreamWriter`); **5c** the reader
   (`decodeLoop`, then `dial`, `run`, `start`, `stop`, `close`, `pause`, `resume`); **5d** `path`
   and the ids; **5e** `streamHandler.ServeHTTP`, `closeNotifier`, `peer.attachOutgoingConn`;
   **5f** the boundary items as axioms, for the user's acceptance.
   (The user asked whether a protocol state machine, as raft's, would help: no, the property is
   per connection, with one writer and one reader and no order claimed; the pure framing model,
   `Chain`, is the separation, and the risk is in the code's goroutine handoffs. A model of
   connection epochs would earn its keep only for FIFO or liveness.)
   **Done 2026-10-23: 5a** (`rafthttp/Stream.lean`; no axiom, baseline 548). Pure: `StreamCodec`
   (state, frames, self-delimiting, non-empty) with `msgCodec` (`MsgFrameOf`) and `v2Codec`;
   `Chain`, `chainBytes`, `Chain.agree` (two chains whose bytes extend one another are prefixes of
   one another), `Chain.compat` and `Chain.frame` (the reader's next bytes, its decoded frame).
   Ghost: the registry (`RaftHttp.γreg`, `streamRegInv`, `streamReg`; `stream_ticket_alloc`
   allocates a ticket fresh for the registry, `streamReg_agree`), the reader's tokens (`streamRd`,
   `stream_withdraw`, `streamRd_skip`), the deposits (`streamDeposit`, `stream_deposit`); the
   protocol (`frameDep`, `streamSent`, `streamReq`, `streamResp`) with the writer's and the
   reader's lemmas (`streamSent_extend`, `streamSent_chain`, `streamSent_compat`,
   `streamSent_v2Compat`, `streamSent_frame`). `raftProto` moved to `Stream.lean`: a `GET` is a
   stream request, a `200` a stream's response (the pipeline proofs unchanged in substance, through
   `raftProto_resp_of`, `raftProto_req_of_pipe`, `raftProto_req_pipe`). `messageEncoder.encode`'s
   spec gains the encoding's bound (`< 2^63`, from `Size`), which the message codec's frames need.
   Still opaque: `idStr` (`ID.String`'s result) and so `streamPath` (5d ties them to `path.Join`).
   For 5c: the decoders' specs must say a decoded copy has no responses (`netRecv`).
   **Done 2026-10-23: 5b, the stream writer** (over its callees' specs as hypotheses; not linked
   until stage 6). `rafthttp/Writer.lean`: what `msgc` carries (`swMsg`), an attached connection
   (`outConnOk`: the handler's response writer after a `200`, the connection's registration, and
   `closeRight`, the right to close it once, which gives the response writer back), the goroutine's
   live connection (`swLive`: encoder, writer at the chain written so far, its frames' facts), the
   fields `mu` guards split in halves between `run` and the lock (`swLockInv`, `swRunOwn`), the
   writer's fixed fields (`swFixed`) and the stop/done rights. Proved: `streamWriter.run` (its
   four-way select, two cases on nil channels while not working; the message's one-shot part
   deposited as its frame's before it is encoded; a heartbeat's frame without one; the old
   connection closed and `msgc` replaced on a failure or a new connection), `close`,
   `closeUnlocked`, `writec`, `attach`, `stop`, `startStreamWriter`, `newMsgAppV2Encoder`,
   `streamType.String` (and its pointer form); `WriterRun.lean`'s `wp_stream_encode` (`enc.encode`
   for either stream type), `stream_perm` (what the encoder may write is in the response's
   protocol), `respWriter_writerAt`. On the way: `ConnReadTimeout`'s initializer translated (five
   seconds: `NewTicker` needs a positive period); the writer contract (`writerAt`) and both
   encoders' specs say an error's `Error()` returns (`http.errStrOk`: the writer logs it).
   **For the user's review (5f)**:
   - `linkHeartbeatSize_init` (**a new init axiom**, `gen-init.py`'s custom kind, reached by every
     result through rafthttp's initializer; **accepted by the user 2026-10-23, baseline 548 -> 549**): the heartbeat's size
     variable holds an `int` from `0` to below `2^50` (its untranslated initializer is
     `proto.Size(&linkHeartbeatMessage)`, two bytes); the writer adds it to a counter.
   - **An open premise, `swMsgBound`**: a message queued to a stream writer encodes below `2^50`
     bytes. The writer sums up to 2049 messages' sizes into an `int` it adds to a prometheus counter,
     whose `Add` panics on a negative value (the counter spec asks `0 ≤ n`); only an overflow past
     `2^63` bytes between two flushes would make it negative. Stage 6 must discharge it, by a physical
     bound (a trust item: no message is a petabyte; but stated on `pbEnc` it would contradict a logical
     heap holding a larger slice) or by letting `Add` of a negative value panic (Go's behavior, a
     change to the counter spec), which the writer's goroutine may (its spec's fork accepts a panic).
   - The draft `respWrite_spec` (not an axiom yet) corrected: `Write` writes the first `n` bytes, all
     of them unless it fails (`io.Writer`'s contract), with an error whose `Error()` returns.
   **5c, the stream reader, done but `dial`'s proof (2026-10-23).** Proved over their callees'
   specs (not linked until stage 6): `streamReader.decodeLoop` (the heart of the reader: each
   frame decoded is the writer's frame of that index; a message's one-shot part withdrawn with
   the reader's token for that index and the message handed to `recvc` or `propc` with its bundle,
   `netRecv`; heartbeats and messages while paused or with a full channel dropped; a failed
   decode closes the body; the stopped check returns `io.EOF` or the close's error; the error
   never `nil`, its `Error()` returns), `run` (dial, decode, the peer status, the rate limiter,
   the context's `Err`, `close(done)`), `start` (the `done` channel, `errorc`, a cancellable
   context, the goroutine), `stop` (cancel, close under `mu`, wait for `done`), `close`, `pause`,
   `resume`, `peerStatus.isActive`, `messageDecoder.decode`, `newMsgAppV2Decoder`.
   `rafthttp/Reader.lean` (`decOwn`, `srLockInv`, `srFixed`, `stream_known`,
   `respReader_readFullAt`, `wp_stream_decode`, `bag_nonblocking_send_au`: a Perennial gap) and
   `rafthttp/ReaderRun.lean` (`srCfg`: what `dial` and `run` read; `srDial`; `srFixed0`, the fields
   before `start` sets the context; `srStopRight`, `srDoneRight`; `wp_Is_errStrOk`: `errors.Is`
   of an `http.errStrOk` error; `wp_ctx_Err`: `ctx.Err()` from `isContext` alone). On the way:
   `readBytesLimit`'s initializer translated (512 MiB); the reader contract (`readFullAt`) and
   both decoders say an error's `Error()` returns, and the msgappv2 decoder that a decoded copy
   has no responses; `decodeLimit` takes the premise that a frame it may read is of an encoding,
   so `proto.Unmarshal` does not fail by its own spec (no trust change).
   **`dial`: spec only.** Its spec (`streamReader__dial.lean`, a hypothesis of `run`'s proof)
   says it does not panic: `semver.MustParse` of the peer's `X-Server-Version`
   (`issues/etcd-rafthttp-stream-dial-bad-server-version-panic.md`) parses, since the peer is a
   member of the program, whose handlers set it to `version.Version`. A goroutine may not panic
   (`wp_fork`), so `run` needs this. Its proof (with 5d's path and id lemmas) needs **the
   response's headers in the HTTP boundary's protocol**, which today has only status and bytes
   (`respAt`'s header is some map): a design question for 5e, where the handler that sets the
   header is proved. The rest of `dial`: the picker, `NewRequest`, the headers,
   `WithContext`, the ticket (`stream_ticket_alloc`), `RoundTrip`, `checkStreamSupport` (reads
   the untranslated `supportedStream`), the status switch, `GracefulClose`, `ReadAll`, the
   precondition-failed body against `errIncompatibleVersion`/`ErrClusterIDMismatch`,
   `reportCriticalError` on `errorc` (`srDial`'s `errorc` and `ErrorC` carry no channel fact yet:
   to add with the proof).
   **Accepted by the user (2026-10-23)**, the 5c trust items:
   * `http.errStrOk` now also says the error is of a well-formed error tree (`http.errTreeOk`:
     for a pointer target, Perennial's `errors.errorIsTree` and `TreeTyped`), what `errors.Is`
     needs (`run` asks `errors.Is(err, errUnsupportedStreamType)` of `dial`'s error and
     `errors.Is(err, io.EOF)` of `decodeLoop`'s). The accepted boundary specs that give
     `errStrOk` (`RoundTrip`, `respWrite_spec`, ...) so now also assume net/http's errors are
     such trees (true of Go's: their `Is`/`Unwrap` methods return); `errors.New`'s are proved to
     be (`errorString_errStrOk`, under the method-set premise `ErrorStringLeaf`).
   * `transport.IsClosedConnError` (a names-only package; its body is
     `err != nil && strings.Contains(err.Error(), "closed")`: translatable once `strings.Contains`
     has a spec) and `(*rate.Limiter).Wait` (`golang.org/x/time/rate`, names-only; any error,
     with the opaque persistent `rate.limiterOk`, which `rate.NewLimiter` will give in stage 6):
     two trust-boundary specs, axioms, not reached yet.
   * rafthttp's `errorsNewVarsInit` gains `errUnsupportedStreamType` (`fmt.Errorf` without verbs,
     an `errors.New` error; it leaves `opaqueInitsOk`), so the package fact says it.
   * Earlier: `zap.Bool` and `raftpb.MessageType.String` (as `zap.String`'s and
     `ConfChangeType.String`'s); `ReadFull_resp_spec` states its bound and error, `respCloser` and
     `RespCloseAny_spec` (a response body closed from another goroutine, as `stop` does while
     `decodeLoop` reads; Go supports it).
   **Done 2026-10-23: 5d, `path` and the ids** (not linked until stage 6; no axiom added, one
   trust-boundary statement strengthened). Go's `path`, translated with bodies since stage 2, is
   proved against pure models that follow its code (`Proof/path/Model.lean`: `cleanModel` with
   the lazy buffer's output, `joinModel`, `splitModel`, `baseModel`, `dirModel`,
   `lastIndexByte`): `Clean` (its lazy buffer `lbOwn`, `Proof/path/Defs.lean`, and the methods
   `index`, `append`, `string`; the main loop, the backtracking of `..` and the copy of an element
   as nested loops), `Join`, `Split`, `Base`, `Dir`, and `internal/bytealg.LastIndexByteString`.
   `Proof/path/Segs.lean`: on a rooted path of plain segments (non-empty, no `/` or `.`), `Clean`
   is the identity, `Join(segsPath segs, s)` appends `s`, `Base` gives the last segment and `Dir`
   the rest. `types.idStr` (`Proof/go_etcd_io/etcd/client/pkg/v3/types/IDStr.lean`):
   `strconv.FormatUint(id, 16)`, lowercase hex, a plain segment, ASCII. `Stream.lean`:
   `streamPath t rid` is `Join(t.endpoint(), rid.String())` (`streamPath_join`), and the stream
   handler's `Base` and `Dir` of it give back `idStr rid` and the endpoint (`streamPath_base`,
   `streamPath_dir`). `streamType.endpoint` proved (`Join(RaftStreamPrefix, ...)`), given
   `RaftStreamPrefix`'s value as a premise: its initializer (`path.Join(RaftPrefix, "stream")`) is
   untranslated, and gen-init cannot run a callee's spec in a package initializer; stage 6
   provides it (an init axiom, or translating it once gen-init can).
   **Accepted by the user (2026-10-23)**: `types.ID.String`'s spec (and `String_ptr`'s) now says which
   string it returns, `types.idStr id` (was: some ASCII string); a trust-boundary statement used
   across the server, the axiom's name unchanged (the users now derive ASCII, `idStr_ascii`).
   **Open for `dial` (needs the user's decision):** its no-panic spec rests on the peer's
   `X-Server-Version` header, which the HTTP boundary does not model (a response's header map is
   some map). A design: the protocol (`Proto`) gains a pure predicate on a response's headers
   (`rhdr`), which `RoundTrip`'s response gives (`respAt`'s headers satisfy it) and which the
   handler must establish before the first `Write`/`WriteHeader` commits the headers (a
   `respWriter` tracking its header map, `w.Header().Set` updating it). raftProto's would be
   "`X-Server-Version` parses as a semver" (rafthttp's handlers set `version.Version`). The
   alternative, a premise of `dial`'s spec (that the peer's version header parses), leaves the
   panic in the trust base as an assumption about peers.
   **5e scoped (2026-10-23; the user chose the header model, `rhdr`).** Three steps:
   **5e-1, the boundary's response headers** (accepted by the user, 2026-10-23):
   * `canonKey` becomes a definition, Go's `textproto.CanonicalMIMEHeaderKey` (a key of token
     bytes gets its first letter and each letter after `-` upper case, the rest lower case; any
     other key is left as it is), so that distinct keys are known distinct (`X-Server-Version`
     is not `Content-Type`).
   * The protocol (`Proto`) gains `rhdr R hs`, a pure predicate on the headers a handler commits.
     A fresh response writer comes with its header map, empty (`respHdrs wr []`, exclusive);
     `w.Header()` before the commit lends it (`hdrOwn`, given back after a `Set`); the commit
     (`WriteHeader`, the first `Write`, `http.Error`) needs `rhdr R hs` of the headers set.
   * The client sees the committed headers but for the keys Go's server sets itself
     (`srvKeys`: `Date`, `Content-Type`, `Content-Length`, `Transfer-Encoding`, `Connection`,
     `X-Content-Type-Options`, which `http.Error` sets): `RoundTrip`'s response's header map
     `hc` has some `hs` with `rhdr R hs` and `hdrGet hc k = hdrGet hs k` off `srvKeys`.
   * A handler returns its response writer, committed (the D33 review's open item: Go's "A
     ResponseWriter may not be used after the Handler.ServeHTTP method has returned"); the
     stream handler gets it back from the writer when the connection closes (`closeNotifier`).
   * raftProto's `rhdr`: `X-Server-Version` is unset or parses (`semver`); rafthttp's handlers
     set it to `version.Version` or not at all. It needs `version.Version`'s value
     (`"3.8.0-alpha.0"`: the version package's init fact, today some string) and that it parses,
     and that `"2.0.0"` does (`serverVersion`'s default): a sufficient, decidable form of
     Masterminds' grammar with a boundary fact that it parses.
   Then the pipeline's proofs are revisited (its handler sets `Allow` and `X-Etcd-Cluster-ID`).
   **5e-2**: `streamHandler.ServeHTTP`, `closeNotifier`, `peer.attachOutgoingConn`.
   Its boundary items, accepted by the user (2026-10-23): `types.IDFromString`'s spec (of a
   member id's string, `idStr x`, it returns `x` and no error: `strconv.ParseUint(s, 16, 64)`
   inverts `FormatUint`); the version facts (`version.Version` holds `"3.8.0-alpha.0"`, its
   initializer's value; `semver` parses a version of the simple form `MAJOR.MINOR.PATCH` with an
   optional `-` prerelease of alphanumerics and dots, which `"3.8.0-alpha.0"` and `"2.0.0"` are).
   The handler's transport facts (`peerGetter.Get` gives the peer's stream writers; `AddRemote`
   returns) are premises, which stage 6 proves of `Transport`.
   **5e-2 done (2026-10-23)**: `streamHandler.ServeHTTP` proved (`405` off `GET`; the headers set,
   `verHdrOk` of them; the check's `412`s; the stream type from the path's `Dir` and the reader's
   id from its `Base`; `410` for a removed member; for an unknown one, `AddRemote` with its
   `X-PeerURLs` and `404`; `412` on an `X-Raft-To` mismatch; else `200`, flushed, the connection
   attached to the peer, and the wait on its close notifier, which gives the writer back),
   `newCloseNotifier`, `closeNotifier.Close`/`closeNotify` (`rafthttp/CloseNotifier.lean`: the
   writer handed back through a broadcast channel whose invariant holds it or the handler's
   ticket), `peer.attachOutgoingConn` (`rafthttp/Peer.lean`, `peerStreams`). `connBack` is now a
   committed writer. One more boundary item, for review in 5f: `Header.Get` through a pointer to
   the map (`r.Header.Get`, `HeaderGetPtr_ok`; `Get` of the map was already one). Not linked
   until stage 6.
   **5e-3**: `streamReader.dial`'s proof (5c's), over the response's `X-Server-Version`.
   **5e-3 done (2026-10-23)**: `streamReader.dial` proved over its callees' specs: the URL (the
   picker's, its path `Join(endpoint, idStr lid)`, `streamPath`), the request (`NewRequest` of a
   `GET` with a `nil` body, its five headers set through `Header`'s pointer wrapper, the peer URLs,
   `WithContext`), the stopped check under `mu` (`ctx.Done()`, an `fmt.Errorf` error), the
   `RoundTrip` with a fresh stream ticket (`stream_ticket_alloc`), the peer's version (no panic:
   `serverVersion` of a member's headers, `verHdrOk` through `srvView`) and ours (`"3.8.0-alpha.0"`
   parses), the stream-type check, and the status switch (`410`: `errMemberRemoved` reported on
   `errorc`; `200`: the stream; `404`, `412` (its body against the two package errors), others:
   errors). Proved with it: `serverVersion`, `compareMajorMinorVersion`, `reportCriticalError`;
   spec only: `checkStreamSupport` (reads the untranslated `supportedStream`), `setPeerURLsHeader`
   (`URL.String` of any URL), to prove with `createPostRequest` before stage 6. The reader's
   configuration (`srCfg`) gains `errcOk` of `ErrorC` (a bag of errors whose `Error()` returns) and
   `RaftStreamPrefix`'s value, premises stage 6 provides.
   Boundary items, accepted by the user (2026-10-23): `semver.New`, `Version.Major`/`Minor`,
   `httputil.GracefulClose`, `strings.TrimSuffix` (a Perennial gap), `fmt.ErrorfPlain` (no `%w`: an
   `errors.New` error), `RoundTrip`'s `respCloser`, `version.MinClusterVersion`'s value. Found on the
   way, also accepted by the user: `http.NewRequest_ok` and `URLString_ok` (statements since stage 2, now
   used; `URLString_spec` restated on the pointer, `String`'s receiver), `readerHas_nil` (a `nil`
   body), `HeaderSetPtr_ok` (`Set` through the pointer, as `HeaderGetPtr_ok`); `reqRest` restated
   over the request's fields but its headers (its docstring's meaning; setting a header keeps it).
   For stage 6: a `410` sends `errMemberRemoved` on `ErrorC`, which `Transport.Start`'s axiom says
   never happens (no member is removed: `IsIDRemoved` is false of every member).
   **5f (2026-10-23): stage 5's trust items, together.** Every boundary spec a stage-5 proof takes is
   now an axiom; this stage adds the last three the reader and writer use, `http.respWrite_ok`
   (`Write` writes a prefix of its bytes, all unless it fails), `ReadFull_resp_ok` (a prefix of
   some response of the protocol) and `RespCloseAny_ok` (a body closed from any goroutine). The
   whole list, each accepted by the user at its step: (5b) `linkHeartbeatSize_init`; (5c)
   `http.errStrOk`'s error tree, `transport.IsClosedConnError`, `rate.Limiter.Wait`,
   `errUnsupportedStreamType` in rafthttp's `errorsNewVarsInit`, `zap.Bool`,
   `raftpb.MessageType.String`, `respCloser`; (5d) `types.ID.String` names `idStr`; (5e-1) the
   response headers (`canonKey` defined, `rhdr`, `respHdrs`, `srvView`, `handlerDone`,
   `RespHeader_ok`); (5e-2) `types.IDFromString`, `version.Version`'s value, `semverValid_simple`,
   `HeaderGetPtr_ok`; (5e-3) `semver.New`/`Major`/`Minor`, `httputil.GracefulClose`,
   `strings.TrimSuffix`, `fmt.ErrorfPlain`, `RoundTrip`'s `respCloser`, `MinClusterVersion_init`,
   `NewRequest_ok`, `URLString_ok`, `readerHas_nil`, `HeaderSetPtr_ok`, `reqRest`'s fields. Of
   these only the init facts are reached by a linked result today (the rest wait for stage 6).
   **Accepted by the user (2026-10-23)**, with the trust check: the one new axiom a linked result
   reaches is `MinClusterVersion_init` (baseline 549 -> 550).
   **Left for stage 6** (premises of the stage-5 specs, and Go code to prove): `swMsgBound` (a
   queued message encodes below `2^50` bytes); `RaftStreamPrefix`'s value (`srCfg`,
   `streamHandlerOk`); `errcOk` of `ErrorC`, and a `410`'s `errMemberRemoved` there against
   `Transport.Start`'s axiom; the stream handler's transport facts (`peerGetter.Get`, `AddRemote`);
   the spec-only helpers `createPostRequest`, `checkPostResponse`,
   `checkClusterCompatibilityFromHeader`, `checkStreamSupport` (`supportedStream`'s value),
   `setPeerURLsHeader` (`URL.String` of any URL).
6. **`Transport`**: `Start`, `AddPeer`, `AddRemote`, `Send`, `Handler` (and `RaftHandler` over
   it), `CutPeer`/`MendPeer` (peers only, `id ∉ rs` as today), proving today's axioms' statements;
   then the trust base drops by those axioms and `RaftHandler`'s, gains the HTTP specs.
   **Scoped 2026-10-23.** What is axiomatized today and what replaces it:
   * Axioms to prove: `Transport.Start` (with what its statement promises of every goroutine and
     handler: `netTransport`'s `Send`/`Stop`/`SendSnapshot`, `Process` only with messages sent to
     the member, nothing on `ErrorC`), `AddPeer`, `AddRemote`, `CutPeer`, `MendPeer`,
     `EtcdServer.RaftHandler` (`Handler()`'s mux), and D21 M5's `net/http.Serve` of a raft handler
     (`Spec/net/http/Serve.lean`), replaced by the HTTP boundary's `Serve_spec` (D33) and
     `register`. The opaque `transportLive`, `transportRemotes` and `raftHandlerOf` become
     definitions over the transport's fields (`t.mu` guarding `peers`/`remotes`, the stats, the
     round trippers, the network's `RaftHttp`).
   * The network's two layers joined: `RaftHttp` (owner of a host, the stream registry) from
     `NetNames` (`dir`), allocated with it (`netNames_alloc`), and each member's peer listener
     registered with `raftProto` (`http.register`), its address a URL of `dir id`.
   Steps: **6a** the transport's state (the predicates as definitions, `RaftHttp` from `NetNames`,
   the listener's registration; what the stage-5 specs left as premises: `RaftStreamPrefix`'s value,
   `errcOk` of `ErrorC`, the stream handler's `peerGetter`/`AddRemote` facts); **6b** the peer and
   the remote (`startPeer`, `peer.send`/`pick`/`Pause`/`Resume`/`stop`, `startRemote`,
   `remote.send`, the URL picker's construction) and `Transport.Send` (routing by `To`);
   **6c** `Handler()` (a mux of the pipeline, stream and snapshot handlers and the prober's),
   `RaftHandler`, `Serve`; **6d** `Start`, `AddPeer`, `AddRemote`, `CutPeer`, `MendPeer`, `Stop`;
   **6e** the spec-only helpers (`createPostRequest`, `checkPostResponse`,
   `checkClusterCompatibilityFromHeader`, `checkStreamSupport`, `setPeerURLsHeader`) and
   `swMsgBound`; **6f** linking (`etc/gen-link.py --server`), the trust base's delta.
   Decisions, **the user chose the recommendation in each (2026-10-23)**:
   (1) **the snapshot stream** (`SendSnapshot`, the snapshot sender and handler: untranslated,
   D22's contract): keep it as a trust-boundary axiom, cut out of `Start`'s at the snapshot
   sender's and handler's own functions; (2) **`ErrorC`**: `netRaftOk`'s `IsIDRemoved` returns
   `false` (the server's spec already says so: static membership), so the stream handler never
   answers `410` and the protocol says it (`raftProto`'s stream responses are not `410`), keeping
   `Start`'s "nothing on `ErrorC`"; (3) **`swMsgBound`**: let `Counter.Add` of a negative value panic
   in its spec (Go's behavior), which the writer's goroutine may, instead of a physical bound on a
   message's size; (4) **the prober** (`addPeerToProber`, `probing`, untranslated): a
   trust-boundary axiom (it only measures round trips and logs).

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
