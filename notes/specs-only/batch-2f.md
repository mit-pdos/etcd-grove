# Batch 2f: rafthttp, etcd's raft transport

Author's report (2026-11-09). Build: `etc/specs-build.sh --dir Spec/net/http
Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp`: OK (117 modules). Snippets: `cd examples &&
go vet ./specreq/rafthttp/` and `gofmt -l`: clean.

## Files

- `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Api.lean` (namespace `Rafthttp`): the
  vocabulary, its header (the shape, the at-most-once argument, the intended realization), laws.
- 103 spec files beside it, one per function: the client-facing `Transport` methods (`Start`,
  `Handler`, `Send`, `SendSnapshot`, `AddPeer`, `AddRemote`, `UpdatePeer`, `RemovePeer`,
  `RemoveAllPeers`, `ActiveSince`, `ActivePeers`, `Stop`, `CutPeer`, `MendPeer`, `Pause`, `Resume`)
  with Users / Proof sketch / Changes / Margin, and the internal ones (`Get`, `removePeer`, `peer`,
  `pipeline`, `remote`, `peerStatus`, `urlPicker`, both codecs, the three handlers and their
  constructors, `closeNotifier`, `util.go`'s helpers, the snapshot sender, the stream writer and
  reader) mirroring the code with a short comment. The untranslated `NewListener`,
  `NewRoundTripper`, `newStreamRoundTripper`, `waitSchedule`, `addPeerToProber` are trust-boundary
  specs (said so in each).
- `Spec/net/http/Api.lean` (namespace `Http`): **the HTTP boundary**, assumed: its model (header),
  vocabulary, the bundles `roundTripperOk`, `handlerOk` (with `servePre`/`serveDone`), and the
  assumed laws (`reserve`, `protoAt_agree`, tickets, a body's `Read`/`Close`, a response writer's
  `Header`/`WriteHeader`/`Write`/`Flush`, the field laws of requests and responses, the mux).
  Beside it, one file per function: `Serve`, `NewServeMux`, `ServeMux__Handle`, `NewRequest`,
  `Request__WithContext`, `Header__Set`, `Header__Get`, `Header__Get_owned`, `Error`, `StatusText`,
  `Transport__CloseIdleConnections`, `URL__String` (net/url's, as this boundary uses it).
- Snippets `examples/specreq/rafthttp/`: `transport.go` (`ReqStartTransport`, `ReqSendReady`,
  `ReqMembership`, `ReqConnected`, `ReqStop`), `snapshot.go` (`ReqSendMergedSnapshot`), `receive.go`
  (`Receiver`, a `Raft` as etcd's: refuses another member's message, panics on a proposal delivered
  twice; `ReqServePeer`).

## Exported vocabulary (client-facing)

- `Net` (`γ : Raft.Cluster`, opaque `names`): the transport layer of one raft cluster.
- `snapImg ν i bs` (persistent): `bs` is a database image certified for a snapshot of index `i`;
  its meaning is the client's, fixed by `net_alloc.spec`.
- `raftProto ν : Http.Proto` (opaque): rafthttp's HTTP protocol under `/raft`.
- `peerAddr ν a` (def, persistent): `a` is reserved for a protocol agreeing with `raftProto ν` under
  `/raft`; `peerAddr_reserve.spec`.
- `sendable lid m` (pure): not a `MsgSnap`; a `MsgApp` of raft's shape from `lid`.
- `outMsg ν lid ml m` (def): `Send`'s per-message premise (a share of the message, `msgSent`,
  `msgCredit`, `sendable`); `outSnap ν mp` (def): `SendSnapshot`'s (snap's message, a `MsgSnap`
  with raft's facts, the reader with `snapImg`).
- `recvd ν ss m` (def): what a delivery carries: `msgSent`, `msgCredit`, and for a `MsgSnap` its
  database saved (`dbSaved ss i bs ∗ snapImg ν i bs`).
- `raftOk ν id ss r` (def, persistent bundle): the receiver's `Raft` contract (`Process` with
  `recvd` and a thread token, returning `procErr`; `IsIDRemoved`; the two reports).
- `procErr err` (opaque, persistent): `procErr_nil.spec`, `procErr_nodeErr.spec`.
- `isTransport t ν id` (persistent), `trRunning t q` (fractional: `AddPeer` a share, `Stop` the
  whole); `trCfg tv ν` (def): the literal's fields `Start` needs.
- `raftProto_muxAnswers.spec`: the handler's mux may answer `404`/`301` off its patterns.
- Provisional stand-ins for other batches (`req/` sections below): `snapshotterOk`, `dbSaved`,
  `snapMsgOwn` (snap), `serverStatsOk`, `leaderStatsOwn`, `followerStatsOk` (v2stats), `urlsHosts`,
  `urlsAt` (types), `errChanOk` (the server's `errorc`).
- Internal (opaque, "(internal)"): `peerAt`, `peerStopRight`, `peerIface`, `remoteAt`,
  `remoteStopRight`, `pipeFresh`, `pipeAt`, `pipeStopRight`, `pipeWorker`, `msgChanAt`,
  `recvChanAt`, `swAt`, `swStopRight`, `swRun`, `swLocked`, `outConn`, `srFresh`, `srAt`,
  `srStopRight`, `srRun`, `srLocked`, `streamBody`, `ssAt`, `ssStopRight`, `snapReq`, `snapBodyAt`,
  `pickerAt`, `statusAt`, `cnAt`, `cnCloseRight`, `writerAt` (+ `writerAt_write.spec`),
  `msgEncAt`, `msgDecAt`, `v2EncAt`, `v2DecAt`, `v2Frame`, `v2Compat`, `msgFrame`, `pbEncodes`
  (raftpb's, provisional), `trMaps`, `phAt`, `shAt`, `sthAt`, `proberAt`, `semverAt`,
  `semverParses`, `verHdrOk`, `postHdrs`, `peerURLsSet`.

`Http` (assumed): `HReq`, `Proto` (`hreq`, `body`, `resp`), `canonKey`/`hdrSet`/`hdrGet`/`srvKeys`/
`hdrView`, `onceOnly`, `pathUnder`, `Proto.agreeUnder`; `addrFree`, `protoAt`, `protoOwn`,
`listenerAt`, `reqTicket`, `reqOwn`, `reqRO`, `hdrMap`, `hdrRO`, `readerAt`, `readerCloser`,
`respAt`, `srvReq`, `respW`, `muxOwn`, `muxAt`, `errOk`, `urlOk`, `urlStr`; `roundTripperOk`,
`servePre`, `serveDone`, `handlerOk`.

## What the API guarantees (the users' needs)

- **Delivery**: a message is delivered at most once, as a `Process` call with a fresh copy and its
  `recvd` (the sender's `msgSent` and `msgCredit`), at the member serving the URL of its `To`; lost
  and reordered messages allowed. A `MsgSnap` goes only by `SendSnapshot`, and is delivered after
  its database is saved. The receiver checks `To` (etcd's `Process` does, answering `403`).
- **At most once, R1's S8**: yes, from the code (the header of `Api.lean`, and
  `req/go_etcd_io_raft_v3.md` "from 2f" item 1): etcd's `γ.dup = false` is sound.
- **Reports** (`ReportUnreachable`, `ReportSnapshot`): calls of the receiver's contract, no promise
  (liveness).
- **Lifecycle**: `Start` errors or starts; every method is concurrent-safe; `AddPeer` needs the
  transport not stopped; `Stop` joins the writers, readers and pipelines (not the `Process` loops or
  the handlers: the margin says so).

## Main changes from the old specs (`specs-ref`)

- The old statements were over the network contract `NetNames`/`NetPayload` (`P`, `O`, `once`,
  `dup`, `img`), `netSlot`, `netBundle`, `netRecv`, `netRaftOk`, `TransportState`'s records and the
  snapshot directory invariant `snapDirInv`. Restated over raft's own vocabulary: the bundle is R1's
  `msgSent`/`msgCredit`; the payload's `dup`/`once` are R1's `γ.dup`; the snapshot directory is
  snap's (`dbSaved`); the image certificate is `snapImg`.
- **Relaxed**: no member slot (`netSlot`): delivery to any member is harmless, `Process` checks
  `To`; no URL directory tying a URL to its member (`γn.dir`, `trURLsOk`): only that every URL is a
  peer address of the network; no remote-id list `L`; no `raftPool`/`R`s/`netProcSlots`: each
  goroutine (rafthttp's forks, `Serve`'s handler runs) holds its own thread token, and the read-lock
  paths take the caller's `threadTok`; `IsIDRemoved` any boolean (was `false`: static clusters).
- **`Stop`, `UpdatePeer`, `ActivePeers`, `Pause`, `Resume`, `removePeer`, `peer.update`,
  `peer.activeSince`, `peerStatus.activeSince`, `urlPicker.update`, `NewListener`,
  `NewRoundTripper`, `newStreamRoundTripper`** specified (no old spec; users call them).
- **The HTTP boundary, one correction** (for the user): the old boundary (D38b) gave every handler
  run the request's ticket. Go's client replays a replayable request (`GET`, no idempotency key) on
  a reused connection whose response read fails (`persistConn.shouldRetryRequest`), so a `GET`'s
  handler may run twice: the old statement was false for the stream dials. Now only a `onceOnly`
  request (a `POST`) carries a ticket; the streams' one-shot credits ride on the reader's per-frame
  tokens (named by the request, not owned by the handler), which a replay cannot duplicate (its
  bytes go to a response no client reads).
- **Handler goroutines** hold their thread token from `Serve`'s trusted model's forks (was: a pool
  of `httpProcSlots` resources given to `Serve`).

## Functions left out

- `(*streamType).String` (Go's pointer wrapper; no caller), `monitorProbingStatus` (untranslated;
  run by `addPeerToProber`'s trusted goroutine), `metrics.go`'s `init` (the metric vectors'
  initializers, a package-init fact).

## Requirement hand-offs written (`notes/specs-only/req/`, "from 2f")

- `go_etcd_io_raft_v3.md`: the answer to S8 (at most once), the `MsgApp` shape law and `m.src = id`
  of a `Ready`'s messages.
- `go_etcd_io_raft_v3_raftpb.md`: `Marshal`/`MustMarshalMessage` give an encoding (`pbEncodes`),
  `Unmarshal` its inverse (functional), `Clone` of the link heartbeat, getters, a `MsgSnap`'s
  non-nil snapshot and metadata.
- `go_etcd_io_etcd_server_v3_etcdserver.md`: the network's allocation and image meaning, the closed
  world of peer addresses, the server as `raftOk` (with `procErr` of its `HTTPError`s), `Send`'s
  premise, `trCfg`, `trRunning`'s discipline, the merged snapshot.
- `go_etcd_io_etcd_server_v3_etcdserver_api_snap.md` (new): `snapshotterOk`, `SaveDBFrom` with
  `dbSaved`, `snap.Message` (`snapMsgOwn`, the close once, `ExactReadCloser`).
- `go_etcd_io_etcd_server_v3_etcdserver_api_v2stats.md` (new): the stats' three predicates.
- `go_etcd_io_etcd_client_pkg_v3_types.md` (new): `NewURLs` (`urlsHosts`, `urlsAt`), `ID.String`,
  `IDFromString`.

`req/go_etcd_io_etcd_server_v3_etcdserver_api_rafthttp.md` (2d's needs of this batch) did not exist
when this report was written; the server's uses were read from its code (`server.go`, `raft.go`,
`util.go`) instead.

## Open questions for the user

1. **The database image's meaning is a predicate fixed at the network's allocation** (`net_alloc`,
   `snapImg ν i bs ∗-∗ Img i bs`): a departure from TaDa of the approved kind (a persistent
   predicate fixed at creation that the writer proves and the reader only reads,
   `examples/c3-store-law.md`). The TaDa alternative, a client-owned set of images made, would make
   every server thread it through `SendSnapshot` for no client that reads it differently.
2. **The closed world of peer URLs**: every URL the transport is given is reserved for the
   network's protocol (`peerAddr`). A member added with a URL served by something outside the
   program (or by another cluster) is outside the model: a deployment premise, as before (the old
   `netAddrFree`), now stated per URL at `AddPeer`/`AddRemote`/`UpdatePeer` and the literal's `URLs`.
3. **The HTTP boundary's ticket correction** (above): a trust statement narrowed (only `onceOnly`
   requests carry a ticket); the old one was false for a replayed `GET`.
4. **`Serve`'s handler goroutines' thread tokens** come from a trusted model whose per-connection
   goroutines are forks (as Go's `srv.Serve` is), not from nothing; the alternative is a client-
   supplied pool (the old `httpProcSlots`), which costs every server a bound no Go program has.
5. **Helpers no batch owns**, specified here only by their use in the proof sketches (trusted or
   translated): `pkg/v3/ioutil` (`NewLimitedBufferReader`, `ReaderAndCloser`, `ExactReadCloser`),
   `pkg/v3/httputil` (`GracefulClose`), `pkg/v3/pbutil` (folded into the raftpb request),
   `client/pkg/v3/transport` (`NewTimeoutTransport`, `NewListenerWithOpts`, `IsClosedConnError`),
   `xiang90/probing`, `x/time/rate` (`NewLimiter`, `Wait`), `Masterminds/semver` (`MustParse`,
   `New`, `LessThan`: `semverAt`, `semverParses` provisional here). Who owns them?

## Known issues the specs record

- `issues/etcd-rafthttp-stream-dial-bad-server-version-panic.md`: `serverVersion`'s and
  `checkClusterCompatibilityFromHeader`'s premise `verHdrOk`; `raftProto`'s response headers carry a
  parsable `X-Server-Version` (members only).
- `nonissues/etcd-rafthttp-msgappv2-unbounded-lengths.md`: `msgAppV2Decoder.decode`'s `v2Compat`.
- `nonissues/etcd-rafthttp-addremote-bad-peerurls-panic.md`: a non-member's header is outside the
  closed world (`addRemoteFromRequest`).
- `nonissues/etcd-rafthttp-misaddressed-403-member-removed.md`: harmless for safety here (the
  server stops on `errorc`, always safe; `reportCriticalError` promises nothing more).
- `nonissues/etcd-rafthttp-cutpeer-twice-remote-panic.md`: gone with the fork's remote flag; no
  premise.

## Round 1 repairs (2026-11-09)

Reviews: `reviews/2f-provability-1.md`, `reviews/2f-completeness-1.md`, with the coordinator's
decisions. Rebuilt: `etc/specs-build.sh --dir Spec/net/http
Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp` OK (119 modules). `go vet` and `gofmt` are
clean on the snippets. `etc/issues-status.py --check` is clean (index regenerated).

Some statements earlier in this report are superseded by this section: `snapImg` is now the
network's field `ν.img` over 2e's `BeImage`; `dbSaved`, `snapshotterOk` and `protoOwn` are gone;
`recvd`/`raftOk` take no snapshotter.

### First tier, provability

- **F1, handler thread tokens.** `Http.Serve.spec` takes `handlerPool p n`, a pool of `n` of the
  caller's thread tokens (`Http.handlerPool_alloc.spec` from `threadToks n`). Each handler run
  draws one and returns it. The assumed physical fact (at most `n` concurrent handlers, the bound
  adequacy fixes) is in the header. The "trusted model's forks" claim is gone. The same requirement
  is written for 2a in `req/google_golang_org_grpc.md`, "from 2f".
- **F2, `onceOnly`.** Now: a non-empty method, not `GET`/`HEAD`/`OPTIONS`/`TRACE`, and neither
  idempotency key **present** (any value), as `isReplayable` tests (`Header.has`). For such a
  method without a key, Go never replays the request, whether or not its body is rewindable. New
  law `postHdrs_onceOnly.spec`.
- **F3, the closed world tied to the bound socket.** `net.Listen` (`Spec/net/http/Listen.lean`) and
  `NewListener` give a fresh `listenerAt l a` for the string the socket is actually bound at (port
  `0`: the actual one, `portZero`), plus `listenerCloser`. `Serve` takes the listener and the
  persistent `protoAt a P`. Only reserved strings can be dialed.
  - The residual environment premise, stated in the header: `addrFree` is issued for at most one
    string per socket, never for port 0, and no proxy relays peer traffic. Aliases are the one case
    the bind cannot settle. A per-socket key alone would be unsound for a rebind after a close (old
    dial facts reach the new socket), and senders must address peers before those peers listen. So
    the protocol stays per string, set once and persistent.
- **F4, `Img` a field.** `Net GF` has the fields `img : w64 → BeImage → IProp` and
  `dbIn : w64 → IProp`, fixed at `net_alloc` (the post equates them literally). `snapImg ν i img`
  is `□ ν.img i img`.
- **F5 + completeness F3, the snapshot database.**
  - `trCfg` takes `Snap.isSnapshotter ss sd ∗ saveOk ν sd`: the client's persistent update over 2e's
    `snapDbs`, at 2e's `saveAt` (an existing file kept), committing `ν.dbIn i`.
  - The handler hands that update to 2e's `SaveDBFrom.spec`, with `readerAt_dbReader.spec`, and
    `Process` gets `ν.dbIn i` (`recvd`). The client's invariant says what the kept file holds.
  - `outSnap` now uses 2e's `isMessage`/`msgClose`/`dbReader`.
  - New snippet `ReqInstallReceived` (`DBFilePath` of the processed index).
- **F6.** The duplicate-proposal panic in `Receiver.Process` is dropped. The comment says what is
  true: each message is delivered at most once, but a proposal can reach a member twice as two
  messages when raft re-forwards it.
- **F7 + completeness F1.**
  - New laws: `Http.respW_agree`, `Http.handlerOk_agree` (protocols agreeing under a pattern) and
    `Http.handlerOk_narrow`.
  - `Transport.Handler.spec`'s post is now `□ ∀ P, ⌜raftCompat ν P⌝ → handlerOk h P "/"`.
    `raftCompat` means: agreeing with `raftProto` on `/raft` and `/raft/`, and allowing the mux's
    `404`/`301` elsewhere. `raftCompat_self.spec` covers the root-serving examples.
  - `peerAddr` is restated with `raftCompat`.
  - New snippets: `ReqServeRoot`, and `ReqServePeer` beside another handler.

### First tier, completeness

- **F2, serving an address again.** `protoOwn` is gone and `Serve` takes the persistent `protoAt`.
  New specs `Listen` (`net.Listen`) and `Listener.Close`. Snippet `ReqRestartServe` serves, closes,
  listens again and serves a second transport.
- **F3.** See F5 above.
- **F4 (mostly 2d's).** Written in `req/go_etcd_io_etcd_server_v3_etcdserver.md`, "from 2f, round
  1":
  - `raftOk` is needed from `tr.Start()`, before `s.start()`;
  - `procErr` must be in `Process`'s post, with a law for `HTTPError`;
  - `IsIDRemoved` needs a spec, with a thread token;
  - the `dbIn`/`img` meaning, the `Transporter` callers' thread tokens, peer addresses for
    `MemberAdd`/`MemberUpdate`, and the package variables.

### Second tier done

- The raft request is restricted to `MsgApp` (item 3 withdrawn).
- `msgChanAt ch ν lid pid K`: `To = pid`, and a message predicate `K` fixed per stream writer
  (`swAt … K`).
  - `peer.send` and `remote.send` take `m.to = pid`.
  - `pick` gives `K m`.
  - `streamWriter.attach` of a msgappv2 connection needs `K ⊆ MsgApp`.
- Body readers that are not HTTP: `Http.NewBuffer_reader.spec` and `Http.MultiReader_reader.spec`
  (which covers `ReaderAndCloser`); `dbReader_readerAt.spec` for the merged snapshot's pipe.
- A body's prefix knowledge: `Proto.bodyPre`. `RoundTrip` asks the client's reader prefixes for
  it, and the handler's reader carries it. This fixes the snapshot handler's order: its metadata is
  dereferenced before `EOF`.
- `raftProto` excludes `MsgSnap` on `POST /raft` (header); `protoAt_agree` dropped.
- `transporterOk tp ν id`, the interface value; `ReqConnected` now goes through `Transporter`.
- `vars_init.spec`: `ConnReadTimeout`/`ConnWriteTimeout` read-only and at least 5s (a scope
  restriction), and `ErrClusterIDMismatch`'s error.
- `urlsNoComma` in `trCfg` (requested of types).
- `ReqErrorC` snippet.
- Nonissues filed:
  - `nonissues/etcd-rafthttp-peerurl-comma-split.md`;
  - `nonissues/etcd-embed-raft-read-timeout-ticker-panic.md`.

### Not done (second tier)

- Completeness item 4: the `rafthttpBootCfg` slot as a `Rafthttp.bootCfg` IProp with elimination
  laws. 2e's hub would take `trCfg` directly for now. This goes to the integration pass.
- Completeness item 8: specs of `http.Client.Do` over `roundTripperOk` for `peerRt`'s monitors
  (low priority, as the reviewer says).
- Completeness item 9: a two-goroutine `trRunning` snippet. 2d carries the share to `onStop`.

### Open questions added

6. **The alias premise** (F3): the environment issues `addrFree` for at most one string per socket.
   Is this residual deployment premise acceptable, or should the boundary model address
   resolution?
7. **The handler pool's `n`** (F1): the server picks `n` when it lends `Serve` its thread tokens.
   The physical premise (at most `n` concurrent handlers) is the assumed part.
