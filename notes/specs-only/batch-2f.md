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
