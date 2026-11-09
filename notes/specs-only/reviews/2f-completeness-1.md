# Batch 2f (rafthttp, net/http): completeness review, round 1

Reviewer: completeness. Read: `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/` (the
client-facing `Transport` specs in full, the internals by their headers), `Spec/net/http/`,
`examples/specreq/rafthttp/`, the users in `.lake/src/server/` (`etcdserver/{server,raft,util,
bootstrap,corrupt}.go`, `etcdserver/api/etcdhttp/peer.go`, `embed/{etcd,config}.go`,
`etcdmain/config.go`), the examples (`examples/lib/{etcdstart,cluster3}`,
`examples/etcd/{restart,partition,lease,leasegrant}`), etcd's integration framework
(`tests/v3@…673da07c8fab/framework/integration/cluster.go`), and the consumers' current specs in
2d/2e (`EtcdServer__{Process,ReportSnapshot,ReportUnreachable,RaftHandler,CutPeer,adjustTicks,
sendMergedSnap,applySnapshot,applyConfChange}.lean`, `isConnectedSince.lean`, `ApiBoot.lean`,
`ApiApply.lean`, `api/snap/Api.lean`). `batch-2f.md` was read only after the findings were formed.

`req/go_etcd_io_etcd_server_v3_etcdserver_api_rafthttp.md` does not exist. 2d and 2e did not write
a hand-off. They wrote provisional stand-ins in their own files instead (`ApiBoot.lean`:
`raftHandler`, `transporterOk`, `rafthttpBootCfg`; `ApiApply.lean`: `mergedSnap`, `dbReader`;
`api/snap/Api.lean`: `dbReader`). I checked those against 2f below (section "2d's and 2e's needs").

## The users, by pattern

| # | pattern | call sites | what it relies on | snippet |
|---|---|---|---|---|
| P1 | construct, `Start`, add remotes and peers | `server.go:412-438` | `Start` errs or starts; `AddRemote`/`AddPeer` do not panic | `ReqStartTransport` |
| P2 | `Send` a `Ready`'s messages (raft loop) | `raft.go:250` (leader, before the write), `raft.go:329` (follower) | returns; at-most-once delivery as `Process` with raft's facts; losses allowed | `ReqSendReady`, `ReqReceiver` |
| P3 | merged snapshot: `SendSnapshot`, then wait on `CloseNotify` | `server.go:1874-1905` | message closed once; reader closed (releases the backend snapshot) | `ReqSendMergedSnapshot` |
| P4 | receive a snapshot, install it | rafthttp `http.go:275` `SaveDBFrom`, then `Process`; `server.go:1068-1071` `OpenSnapshotBackend`, which panics if `<index>.snap.db` is missing | **the db file of the snapshot's index is in the snapshot dir, with an image, when the apply thread installs it** | none |
| P5 | membership while running | `server.go:2075/2085/2101` (conf change), `1157-1166` (snapshot) | no panic (`AddPeer` before `Stop`; URLs parse) | `ReqMembership` |
| P6 | health heuristics through the `Transporter` interface | `util.go:28-100`, `server.go:504` (`adjustTicks`), `server.go:1655` | returns some time / count | `ReqConnected` (on `*Transport`, not the interface) |
| P7 | the handler on the peer listener | `etcdhttp/peer.go:62-79` (mux at `/raft`, `/raft/` beside 8 other patterns, P ≠ raftProto), `examples/lib/etcdstart/common.go:172` and `examples/etcd/restart/restart3.go:79` (**`http.Serve(l, s.RaftHandler())` at the root**), `examples/etcd/lease/leasekv_cluster_test.go:35-39`, `examples/etcd/leasegrant/leasegrant_cluster_test.go:74` (**mounted at `/`** beside lease handlers) | the handler serves the listener's protocol | `ReqServePeer` (its own mux, `/raft` and `/raft/` only) |
| P8 | restart a member on the same peer address | `examples/etcd/restart/restart3.go:76-79,102-104` (listener closed, `net.Listen` and `http.Serve` again); `framework/integration/cluster.go:1265-1269` | the address can be served again by the new transport's handler | none |
| P9 | the server as `rafthttp.Raft` | `server.go:412` (`Raft: srv`), `server.go:700-730` | rafthttp calls `Process`, `IsIDRemoved`, the reports, **from `tr.Start`/`AddPeer` on, before `s.start()`** | `ReqReceiver` |
| P10 | fatal errors on `ErrorC` | rafthttp `pipeline.go:170`, `snapshot_sender.go:113`, `stream.go:624`; `server.go:845-848` receives, logs, stops | sends never block; the receiver may log it | none |
| P11 | stop and test hooks | `raft.go:440` (`onStop`), `raft.go:449-456` (`Pausable` assertion), `server.go:2197-2210`; `cluster3.go:147-151`; `framework/integration/cluster.go:1166-1172,1358-1368` | no panic | `ReqStop` |
| P12 | exported package variables | `server.go:495` (`adjustTicks` reads `ConnReadTimeout`), `server.go:119` (etcdserver's package init reads `ConnWriteTimeout`), `corrupt.go:533,613` (`ErrClusterIDMismatch.Error()`), `framework/integration/cluster.go:367` | the value can be read; an error whose `Error()` returns | none |
| P13 | `NewRoundTripper` outside the transport | `bootstrap.go:72` → `peerRt` (`server.go:326,1506`, version monitor, hash-KV checker) | a round tripper for the peers' *other* endpoints | none (bootstrap is a trusted triple) |

## What is good

- Every exported method the server calls has a spec, plus the test hooks. The internals are complete
  enough that the proof sketches can be followed down to the codecs.
- `AddPeer`/`AddRemote`/`UpdatePeer` take the URL slice as `DFrac.discard`. This looks strong but
  is needed: `addPeerToProber` hands `us` to the prober, which keeps it (`transport.go:314-315`).
  Every real caller passes a fresh slice it can give up (`Members()` returns clones, and the
  conf-change context is freshly decoded).
- `trRunning` stands for the one real panic (`AddPeer` after `Stop`, "transport stopped"). It is a
  fraction, so `NewServer` and the apply thread can share it, and `Stop` takes it whole. etcd's
  order (`run`'s defer stops `sched` before `r.stop()`, `server.go` `run`) lets 2d carry it.
- The at-most-once argument, which is R1's S8 (`Api.lean` header), and the narrowed HTTP ticket
  (`onceOnly`) are what `ReqReceiver`'s duplicate-proposal panic relies on. `outMsg`'s
  `∃ dq` share fits R1's `readyDq`.
- `ReqServePeer`, as written, can be proved: `peerAddr_reserve` gives `protoOwn a (raftProto ν)`,
  `mux_handlerOk` at `/` needs the two `/raft` handlers and the mux's 404/301, and
  `raftProto_muxAnswers` gives those for every request.

## First tier

### F1. `Transport.Handler.spec`'s post does not serve the handler's real call sites (P7)

`Transport__Handler.lean` gives `Http.handlerOk h (raftProto ν) "/raft" ∗ Http.handlerOk h
(raftProto ν) "/raft/"`. The real call sites need more:

- `examples/lib/etcdstart/common.go:172` and `examples/etcd/restart/restart3.go:79` call
  `http.Serve(l, s.RaftHandler())`. `Serve.spec` takes `handlerOk h P "/"`, and no law turns
  `/raft` into `/`.
- `leasekv_cluster_test.go:36` and `leasegrant_cluster_test.go:74` mount the handler at `"/"` in a
  mux beside lease handlers. That mux's protocol `P` agrees with `raftProto ν` only under `/raft`.
  `mux_handlerOk` needs every handler at the same `P`, and there is no law to restate `handlerOk`
  at an agreeing protocol: `respW … P` is opaque, so `handlerOk` cannot be transferred by
  unfolding.
- etcd's `NewPeerHandler` (`etcdhttp/peer.go:62-79`) mounts it at `/raft` and `/raft/` with eight
  other patterns, which is the same transfer problem.
- 2e's stand-in `raftHandler h γ id` ("which `http.Serve` may serve on the member's peer listener",
  `ApiBoot.lean:239-241`, the post of `EtcdServer.RaftHandler.spec`) cannot be realized from 2f's
  post.

`handlerOk h (raftProto ν) "/"` is true. Rafthttp's own mux answers 404/301 off its patterns, and
`raftProto_muxAnswers` allows that for every request, so 2f's proof can give it.

**Fix.** State the post for every compatible protocol, for example
`□ ∀ P, ⌜raftCompat ν P⌝ → Http.handlerOk h P "/"`, where `raftCompat ν P` is
`agreeUnder "/raft" P (raftProto ν) ∧ agreeUnder "/raft/" P (raftProto ν)` plus "`P` allows
404/301 at the paths outside `/raft`". Add an `Http` law that narrows the prefix
(`pathUnder pfx' ⊆ pathUnder pfx → handlerOk h P pfx ⊢ handlerOk h P pfx'`). Clients must not
unfold `servePre`. Add a snippet that serves `tr.Handler()` at the root, and one that mounts it at
`/` beside another handler.

### F2. A member cannot serve its peer address again after a restart (P8)

`Serve.spec` consumes `protoOwn a P` and never returns it. `protoOwn` is exclusive and is minted
once per address and run (`reserve` from `addrFree`). `examples/etcd/restart/restart3.go` closes
the stopped member's listener (`stop`, l.102-104) and then runs `net.Listen` and `http.Serve` again
on the same `peerAddr` with the restarted server's handler (`startMember`, l.76-79). etcd's
`Member.Restart` (`framework/integration/cluster.go:1265-1269`) does the same. The second `Serve`
cannot be proved.

The closed world does not need the serving right to be exclusive. "Every request at `a` is
handled at protocol `P`" needs only `protoAt a P`, which is persistent and agreed by
`protoAt_agree`, and two servers on one address with the same `P` break nothing. The restarted
transport has the same `ν`, so the old connections' handlers (the stopped server's) and the new one
serve the same protocol.

Related: nothing gives `Http.listenerAt`. There is no `net.Listen` spec (the examples call
`net.Listen` directly, `etcdstart/common.go:168`, `restart3.go:74`), and no `Listener.Close`
spec. `rafthttp.NewListener.spec` has no user. gRPC has its own `Grpc.listenerAt`, so a `net.Listen`
spec must say which one it gives.

**Fix.** `Serve.spec` takes `protoAt a P`, or `protoOwn` becomes persistent. Add `net.Listen`
(giving `Http.listenerAt`, or one listener predicate shared with 2a) and `Close`. Add a snippet
that serves, closes the listener, then listens and serves again on the same address with a second
transport of the same member id.

### F3. A received snapshot's database cannot be traced to the apply thread's install (P4)

The server relies on the following for no-panic. Rafthttp's snapshot handler saves the stream
(`http.go:275`, `SaveDBFrom`) before `Process`. Later, `applySnapshot` calls `OpenSnapshotBackend`
and panics if `<index>.snap.db` is missing (`server.go:1068-1071`, `storage/backend.go:63-67`).
2f's chain cannot deliver this:

- `recvd` gives a persistent `dbSaved ss i bs`, made by the provisional `snapshotterOk ss`. 2e's
  snap vocabulary is now different. `Snap.snapDbs sd F` is exclusive and timeless, held by the
  server's invariant: "the receiving transport adds, the apply thread installs and releases"
  (`api/snap/Api.lean:19-23`).
  - `trCfg` gives the transport no access to that invariant: `snapshotterOk` carries nothing the
    server could build it from.
  - A persistent "the file was saved" cannot be eliminated against `snapDbs`, because the apply
    thread renames the file away (`OpenSnapshotBackend`) and `ReleaseSnapDBs` deletes files.
- `dbSaved ss i bs` with `bs` the received stream is false when the file already existed.
  `SaveDBFrom` keeps the existing file and returns success (`snap/db.go:56-63`). The file then
  holds an earlier stream's bytes, not `bs`. 2f's own req says "(or keeps an existing one)" and
  still gives `dbSaved … bs`.
- 2d's `EtcdServer.Process.spec` takes only `msgSent`/`msgCredit`, so `dbSaved` is dropped at the
  receiver. 2d's `applySnapshot` sketch takes the image "from 2f delivering the db to the
  snapshotter (`req/` 2e/2f)", which does not exist yet.
- No snippet covers this pattern. `ReqReceiver` only steps the message.

**Fix (to settle with 2e).** The client owns the snapshot directory, so state the receive side
over a client-chosen contract, as `raftOk` is. One option: `trCfg` takes a persistent
`saveOk ν ss` bundle. `SaveDBFrom(r, i)`, given a reader whose complete streams are
`snapImg ν i` images, returns an error or a client token `dbIn ss i`. The server realizes it with
its invariant over `snapDbs`: `F i = some img → Img i img` for an image of whatever stream was kept
first. `recvd` then carries `dbIn ss i` in place of `dbSaved ss i bs`, and its meaning (for etcd:
"the file is there until the apply thread installs index ≥ i") is the server's. The other option:
give `SaveDBFrom` a logically atomic spec over `snapDbs` (2e) and have `trCfg` take the client's
update. In either case, write the snippet: a `Receiver` whose `Process` of a `MsgSnap` records the
index, and an installer that opens `DBFilePath(index)` and panics on an error.

### F4. The server cannot establish `raftOk` where it starts the transport (P9; mostly 2d's to fix)

`Transport.Start.spec` takes `raftOk ν id ss srv` at `server.go:412-426`. From then on, peers'
`Process` loops and stream readers run: `AddPeer` at `server.go:436` starts them, all before
`s.Start()`. What 2d offers instead:

- `EtcdServer.Process.spec` is stated over `srvNode s γ id`, which `ApiApply.lean:188` defines as
  "after `start`". That cannot be the source at `NewServer` time. In the Go code everything
  `Process` reads (`lgMu`/`lg`, `cluster`, `stats`, `memberID`, `r`'s node) is set before
  `tr.Start()`.
- Its post is `True`. `raftOk` needs `procErr err`, because the pipeline and snapshot handlers do
  `errors.As(err, &writerToResponse)` and `WriteTo`. No `procErr` law exists for
  `httptypes.HTTPError`, which 2f requested in `req/…etcdserver.md`, "from 2f", item 3.
- `EtcdServer.IsIDRemoved` (`server.go:725`) has no spec.

`EtcdServer.ReportSnapshot.spec` and `EtcdServer.ReportUnreachable.spec` exist but are also over
`srvNode`, with the same timing problem.

**Fix.** In 2f's req (item 3), add the timing: `raftOk` is needed from `tr.Start()`, before the
server starts. 2d then states `Process`/`IsIDRemoved`/the reports over a predicate `NewServer`
holds at that point, with `procErr` in `Process`'s post, and states the `HTTPError` law.

## Second tier

1. **The `Transporter` interface and the thread token.** The heuristics (`util.go:28-100`) take a
   `rafthttp.Transporter` interface value. 2e's stand-in `transporterOk tp` ("`ActiveSince` may be
   called from any goroutine", `ApiBoot.lean:243-245`) has no 2f counterpart. By the "an interface
   value gets a bundle" preference, 2f should export it: `transporterOk tp ν id` with
   `isTransport t ν id ⊢ transporterOk (iface t) ν id`, its `ActiveSince`/`ActivePeers` taking
   `threadTok`.
   - 2d/2e's callers take no `threadTok` and must add it: `isConnectedSince.lean` and the other
     users of `transporterOk`; `EtcdServer.adjustTicks.spec` (calls `ActivePeers`);
     `EtcdServer.CutPeer.spec` and `EtcdServer.MendPeer.spec` (call `Transport.CutPeer`/`MendPeer`,
     which take `threadTok`). Their real callers all run on goroutines that hold one.
   - `ReqConnected` calls through `*Transport` and should go through the interface, as
     `util.go` does.
2. **No law for the exported variables (P12).** Without one, these cannot be specified:
   - `adjustTicks` (`server.go:495`) reads `ConnReadTimeout`;
   - etcdserver's package init (`server.go:119`) reads `ConnWriteTimeout`;
   - `corrupt.go:533,613` call `ErrClusterIDMismatch.Error()`.

   `streamWriter.run`'s sketch also uses "`ConnReadTimeout / 3` positive" (`stream.go:169`,
   `time.NewTicker` panics at ≤ 0), with no stated source. The variables are writable:
   embed's `--raft-read-timeout` flag writes the global (`embed/config.go:631`), etcdmain clamps it
   to ≥ 5s (`etcdmain/config.go:180-187`), and embed does not. With a value below 3ns, a stream
   writer panics.

   Suggest a law of rafthttp's `isPkgInit` giving read-only points-to's, with the scope restriction
   "no one writes them after init" stated, and a `nonissues/` entry for the embed flag (a
   precondition etcdmain meets; not filed by me, read-only review).
3. **`ErrorC` (P10) has no snippet, and `errChanOk` has no owner yet.** The server's side is only
   "receive, log with `zap.Error`, stop" (`server.go:845-848`), so "any error" is enough. Add a
   two-line snippet, and have 2d define `errChanOk` for `srv.errorc` (capacity 1, `server.go:318`).
4. **`rafthttpBootCfg` (`ApiBoot.lean:288-290`) is a `Prop` slot.** 2f's boot needs are resources:
   `peerAddr ν a` for `cfg.PeerURLs`, `urlsAt`. Its description ("the cluster's directory within the
   transport's bounds") is the old `γn.dir` vocabulary. Under the slot convention 2f should export
   the slot, `Rafthttp.bootCfg ν cfg : IProp`, with elimination laws to `trCfg`'s URL conjunct.
5. **The `peerAddr` premise is not carried to its source for runtime membership changes (P5).**
   `applyConfChange`'s sketch calls `AddPeer`/`UpdatePeer` (2f), whose URLs must be `peerAddr`s.
   Neither the server's sketch nor `ClusterServer.MemberAdd`/`clientv3` `MemberAdd` carries that
   fact for URLs a client supplies. The author's open question 2 names the premise; nobody threads
   it. `ReqMembership`'s "Assumes: the URLs as in ReqStartTransport" hides it. Say where it enters:
   for example, a `peerAddr` premise on the client's `MemberAdd`/`MemberUpdate` URLs, kept by the
   membership invariant.
6. **Three predicates for the merged snapshot's reader.** 2f's `outSnap` wants
   `Http.readerAt rc _ (snapImg ν i)`. 2d's `mergedSnap` has `dbReader rc γ k`, and 2e's snap has
   `Snap.dbReader r img`, marked "provisional, 2f's". `rc` is an `io.Pipe` reader
   (`newSnapshotReaderCloser`), not an HTTP body, and nobody gives `Http.readerAt` of it.
   `snapMsgOwn` likewise faces 2e's `isMessage`/`msgClose`. Export the reader predicate 2e expects,
   or a law from it, and reconcile `snapMsgOwn`.
7. **`Send`'s `sendable` cannot be established today.** It needs R1's `MsgApp`-shape law and
   "`Ready` messages have `src = id`", which 2f requested (`req/go_etcd_io_raft_v3.md`, "from 2f",
   item 2). `Spec/go_etcd_io/raft/v3/Api.lean` has no such law yet (only `msgSent_type`,
   `msgSent_snap`). This is pending on R1, not a 2f defect.
8. **P13.** Outside the trusted `bootstrap`, `peerRt` is used for GETs and POSTs to the peers' other
   endpoints (`promoteMemberHTTP`, `server.go:1506`; the version monitor; `corrupt.go`'s hash-KV
   client). The `http` directory has no `Client.Do`/`Get` over `roundTripperOk`. In the examples
   those requests hit a raft-only handler and get the mux's 404, which `raftProto_muxAnswers`
   allows. Low priority: the consumers' sketches treat those monitors as model-neutral.
9. **`trRunning` across threads (P5/P11).** The snippets are sequential. etcd's discipline is that
   the apply thread's share must reach the raft loop's `onStop`: `sched.Stop()` comes before
   `s.r.stop()`. 2d can carry this (for example in `r.stopped`'s payload). A snippet with
   `AddPeer` on one goroutine and `Stop` on another, after a join, would pin the requirement.

## 2d's and 2e's needs of 2f

- `raftHandler` (2e): not met (F1).
- `transporterOk` (2e): not exported, and the thread token is missing on the caller side
  (second tier 1).
- `rafthttpBootCfg` (2e): wrong kind (second tier 4).
- `mergedSnap`/`dbReader` (2d) and `Snap.dbReader` (2e): no 2f counterpart (second tier 6).
- The snapshot-install chain (2d's `applySnapshot`, 2e's `snapDbs`): F3.
- In the other direction, 2f's needs of 2d (`raftOk`, `procErr`, `IsIDRemoved`) are not met: F4.

## Ranking (need of revision)

1. `Transport.Handler.spec`, with `Http` (`Serve.spec`, `protoOwn`, the missing narrowing,
   agreement and listener laws): F1, F2.
2. `recvd`/`dbSaved`/`snapshotterOk` (`Api.lean`), with 2e's snap: F3.
3. `trCfg`/`raftOk` at `Transport.Start.spec` (2d's side mostly): F4; second tier 4.
4. `ActiveSince`/`ActivePeers` (the interface bundle), the package-variable laws: second tier 1, 2.
5. `SendSnapshot`/`outSnap` (reader-predicate reconciliation), `AddPeer`/`UpdatePeer` (where
   `peerAddr` comes from): second tier 5, 6.
6. `Send`, `Stop`, `RemovePeer`, `RemoveAllPeers`, `Pause`/`Resume`/`CutPeer`/`MendPeer`: fine
   (pending R1's law for `Send`).

## Verdict

Not done. Every method has a spec and the internals are thorough, but four first-tier problems
remain:

- The handler cannot be served the way the examples and etcd serve it: at the root, or beside
  other handlers (F1).
- A member cannot serve its peer address again after a restart (F2).
- The receive-to-install chain for snapshot databases does not connect to the server's
  snapshot-directory model, and `dbSaved` is false when `SaveDBFrom` keeps an existing file (F3).
- The server cannot supply `raftOk` at `tr.Start()` with 2d's current `Process` spec (F4, mostly
  2d's).

A second round is warranted after the repairs.
