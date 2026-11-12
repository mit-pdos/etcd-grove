# Batch 2f (rafthttp and the net/http boundary): provability review, round 1

Reviewer: provability (independent of the author). Read: `README.md`, `review-brief.md`,
`PRINCIPLES.md` (the hard rules, "A trusted statement never gives out a counted resource it did not
take"), `SpecPlan/Spec/net/http/*`, `SpecPlan/Spec/.../rafthttp/*` (Api.lean and the specs on the paths below), the
three snippets, the `## from 2f` requests, R1's `SpecPlan/Spec/go_etcd_io/raft/v3/{Api,ApiCore,Model,node__Step}.lean`.
Go: `.lake/src/server/etcdserver/api/rafthttp/` (pinned fork), raft `.lake/src/raft/`, the pinned
`snap/db.go` and `client/pkg/v3/{types,transport}`, Go go1.27.3's `net/http`
(`/usr/local/go/src/net/http`). I read `batch-2f.md` only after writing the findings below.

## Summary

The at-most-once argument holds up against the code: I found no path that delivers a message twice
(details in "What is good"). The msgappv2 shape law is true of raft for `MsgApp`. What fails is
mostly in the trust boundary and in a few laws and requests that nothing can realize or that are
false of the code. Seven findings are first tier.

## First tier

### F1. `Serve` hands each handler run a thread token it never took (hard rule; `SpecPlan/Spec/net/http/Serve.lean`, `Api.lean` `servePre`/`serveDone`)

`Serve.spec`'s precondition holds no `threadTok`, but each `handlerOk` run gets one in `servePre`.
Its justification is "the trusted model's forks: their thread tokens come from the thread fuel".
No such model exists. `Code/net/http.toml` translates names only (`translate = ["!*", "Method*",
"Status*", "!StatusText"]`), and `TrustedCode/` has nothing for `net/http`. So `Serve` is an assumed
statement outside the semantics, which is exactly PRINCIPLES' lease-ex D1 case: "Analogy with a
modelled operation ... is no argument when the thing is outside the semantics".

Here is how it goes wrong. `RoundTrip` takes no token either, so a program can open `threadBound`
concurrent stream `GET`s. Each one makes a handler run that holds a token while it blocks
(`<-c.closeNotify()`). Any `handlerOk` proof may stash its token in an invariant, and
`threadToks T ⊢ False` then gives program-level `False`. The grpc batch makes the same claim
(`SpecPlan/Spec/google_golang_org/grpc/Api.lean:14-19`), so both must be fixed together.

**Fix:** make the realization real.
- Add a `TrustedCode/net/http` model of `Serve`: an accept loop that `Fork`s one goroutine per
  connection (`wp_fork_tok`), and per request an external "read a request" step carrying the
  closed-world knowledge.
- List `Serve` as `trusted` in `Code/net/http.toml`, and record the plan in the header instead of
  "assumed".
- Until that model exists, `Serve.spec` breaks the hard rule. The alternative is a thread-pool
  handle that the owner of `Serve` passes in (the bounded-pool fix chosen for grpc, STATUS
  "Soundness bugs: the handler pool").

### F2. `onceOnly` disagrees with Go's `isReplayable` (unsound trust statement; `SpecPlan/Spec/net/http/Api.lean` `onceOnly`)

`Request.isReplayable` (`request.go:1561-1575`) tests `r.Header.has("Idempotency-Key")`, which is
presence (`header.go:72-75`: `_, ok := h[key]`), not a non-empty value. `onceOnly` tests
`hdrGet R.hdr "Idempotency-Key" = []`, which is true for a header set to `""`.

So a `POST` built with `NewRequest`, then `Header.Set("Idempotency-Key", "")` (the boundary's own
`Header.Set` spec allows it), is `onceOnly` by the spec. Go replays it on a reused connection
(`shouldRetryRequest`, `transport.go:873-881`). Both handler runs then "receive" the exclusive
`reqTicket τ` (`servePre`), and `reqTicket_excl` gives `False`. rafthttp never sets the key, but the
axiom is general.

A smaller gap of the same kind: `valueOrDefault(r.Method, "GET")` treats `""` as `GET`, while
`onceOnly` treats it as once-only. This is unreachable today, because `reqOwn` comes only from
`NewRequest`, whose spec allows only `GET`/`POST`.

**Fix:**
- State key absence: `∀ p ∈ R.hdr, p.1 ≠ canonKey "Idempotency-Key" ∧ p.1 ≠ canonKey "X-Idempotency-Key"`.
- Add `R.meth ≠ ""`.

Checked and sound as stated:
- `nothingWrittenError` retries only when no byte reached the connection (`transport.go:868-872`,
  and `pc.nwrite`), so no handler ran.
- rafthttp's transports never use HTTP/2. `client/pkg/v3/transport/transport.go:41,62` set
  `DialContext` and `TLSClientConfig` without `ForceAttemptHTTP2`.
- HTTP/2's own retries replay only streams the server refused or never processed.

### F3. The closed world is per string, but listeners and aliases are per socket (unsound boundary; `NewListener.lean`, `Serve.lean`, `Api.lean` `addrFree`/`reserve`)

`NewListener.spec` gives `listenerAt l u.Host'` from `True`, for any URL. `Serve` then believes that
"every request read at `a` was sent ... through `RoundTrip` to `a`". Two cases break that:
- **Port 0.** `"http://localhost:0"` passes `types.NewURLs`; I checked `url.Parse` and
  `SplitHostPort` with go1.27.3. Requests reach the real port, under a different string.
- **Host aliases.** `localhost:p`, `127.0.0.1:p` and `[::1]:p` can name one socket. This is the
  repository's own finding `axiom/netaddralias` in `specs-ref/notes/STATUS.md`, "Axiom sweep
  batch 3".

Either way, a client that holds `protoAt s1 P1` with a trivial `P1` reaches a handler served at
`s2` under `protoOwn s2 (raftProto ν)`. That handler gets `msgSent`/`msgCredit` facts nobody proved:
a delivered message that was never sent. Nothing in the batch says where `addrFree` comes from, or
that strings are canonical.

**Fix:** state the physical fact as the environment's premise in the header:
- `addrFree a` is issued once per socket, `a` canonical, and never with port 0;
- `NewListener.spec` requires such an `a`, or consumes a token tied to `addrFree`;
- (deployment) no HTTP proxy relays peer traffic: `NewTransport` uses `Proxy: http.ProxyFromEnvironment`.

### F4. `net_alloc.spec` cannot be realized (`rafthttp/Api.lean:466-469`)

The law asks for `□ ∀ i bs, snapImg ν i bs ∗-∗ Img i bs` with no modality, for any persistent
`Img : w64 → List w8 → IProp GF` chosen at runtime. The header realizes `snapImg` as "a saved
predicate fixed at `net_alloc`". Saved-predicate agreement holds only under `▷` (IProp is not
discrete). Nor can `Net` carry `Img` itself: `NetNames : Type` is declared without `GF` and cannot
hold an `IProp GF`. So the direction `snapImg ⊢ Img` cannot be realized as stated.

**Fix**, either:
- make the image predicate a transparent field of `Net` (as the old `NetPayload.img`,
  `specs-ref/.../rafthttp/Net.lean:77`), with `snapImg ν i bs := ν.img i bs`; or
- weaken the law to `snapImg ν i bs ⊢ ▷ Img i bs`. The consumer, the server's apply path, is in a
  WP and can strip the later.

**Uncertain:** whether Perennial's Lean Iris has a later-free saved predicate. I believe not.

### F5. `SaveDBFrom` keeps an existing file, so `dbSaved ss i bs` of the bytes read is false (`req/..._snap.md` item 2; the sketch of `snapshotHandler.ServeHTTP`)

`snap/db.go:57-65`: if `<index>.snap.db` already exists, the temp file is removed and the existing
file is kept (D22 finding 7, `specs-ref/notes/rafthttp-plan.md:892-898`). The request asks snap to
return `dbSaved ss id bs` for the stream just read, and the handler's sketch relies on that. snap
cannot prove it when another sender's image, or one from an earlier run, is already there.

`recvd` itself is fine: it is `∃ bs`.

**Fix:** restate the request.
- The snapshotter carries a directory invariant `I` (for etcd, `snapImg ν`), fixed when it is
  created and durable across restarts: the files on disk outlive the run.
- `SaveDBFrom` takes `□ ∀ B, Φ (r ++ B) -∗ I id B` and returns `∃ bs', dbSaved ss id bs' ∗ □ I id bs'`.
- Fix the sketch to match.

### F6. `ReqReceiver`'s "a proposal delivered twice" panic cannot be proved, and is false of raft (`examples/specreq/rafthttp/receive.go:39-51`)

The guard panics if two `MsgProp`s with the same entry data reach one member's `Process`. Nothing in
the specs gives that:
- `msgCredit` is opaque, with no elimination or exclusivity law (R1 `Api.lean:739-744`), so
  `Process` cannot tie a credit to entry data.
- The `Assumes:` line ("raft forwards a proposal at most once") is not a spec fact, and it is false.
  A follower re-forwards a proposal it received (`raft.go:1743-1744`; through `node`, re-stamped
  `From = r.id`, `node.go:386-388`). Each hop consumes one credit and hands out the next. With
  leader churn (C→A, A follower→B, B follower→A) the same proposal reaches A's `Process` twice,
  with one-shot credits and an at-most-once transport.

At-most-once per message is already what the triples encode: `Send` takes the credit, and `Process`
(`raftOk`) gets it with `recvd` for `node.Step`.

**Fix:** drop the data-duplicate guard and keep "the message is stepped with `node.Step`'s
precondition (`msgSent`, `msgCredit`, `To = id`); a non-node error panics". Or ask R1 for a
per-proposal token law, if a caller really needs per-proposal exclusivity.

### F7. `ReqServePeer` cannot be proved under its own assumption: no law moves `handlerOk` between agreeing protocols (`receive.go:70-83`; `Http/Api.lean`; `Transport.Handler.spec`)

The snippet, `peerAddr`'s docstring and the server's peer mux (`etcdhttp.NewPeerHandler`, which also
serves `/members`, `/version`, ...) all use a protocol `P` that only agrees with `raftProto ν` under
`/raft`. But `Transport.Handler.spec` gives `handlerOk h (raftProto ν) "/raft"`, while
`mux_handlerOk` needs `handlerOk h P "/raft"`. There is no `handlerOk`/`respW` law for protocols
that agree under a prefix.

With `P = raftProto ν` (`peerAddr_reserve`) the snippet does go through:
1. `NewServeMux` and two `Handle`s give `muxOwn`; `muxOwn_freeze` gives `muxAt`.
2. `Transport.Handler.spec` gives `handlerOk h (raftProto ν)` at `/raft` and `/raft/`.
3. `raftProto_muxAnswers` covers the 404/301 condition of `mux_handlerOk` at `"/"`.
4. `Serve.spec` needs `listenerAt l a`, from the snippet's assumption, and `protoOwn a (raftProto ν)`.

**Fix:** add `Http.respW_agree`: `P.resp R = P'.resp R → respW w R τ P c hs bs ⊣⊢ respW w R τ P' c hs bs`.
Derive `handlerOk_agree : Proto.agreeUnder pfx P P' → handlerOk h P pfx ⊢ handlerOk h P' pfx`, or
state `Transport.Handler`'s post for every `P` agreeing with `raftProto ν` under `/raft`.

## Second tier

1. **The R1 request is false as worded** (`req/go_etcd_io_raft_v3.md`, from 2f, items 2-3).
   - "A `Ready` of node `id` hands out messages with `m.src = id`" is false:
     - a follower forwards a remote `MsgReadIndex` with its original `From` (`raft.go:1784`; it
       comes in through `recvc`, not re-stamped);
     - through `RawNode`, a stepped remote `MsgProp` keeps its `From` (`raft.go:1743`).
   - Restrict the request to `MsgApp`. That part is true: the only constructor is
     `maybeSendAppend` (`raft.go:651-658`), `send` sets `From` (`raft.go:515-517`), and etcd's
     `processMessages` does not touch a `MsgApp`.
   - Item 3 is not needed: the link heartbeat has `To = 0`, and `Transport.Send` skips those.
   - Until R1 adds the `MsgApp` shape law, nothing establishes `Send`'s `sendable` premise. 2d's
     answer (`req/..._rafthttp.md`, item 2) assumes it exists.
2. **`msgChanAt` loses `To = pid` and "`MsgApp` only" for the msgappv2 queue.**
   - `peer.send.spec` does not require `m.to = pid`.
   - `peer.pick.spec` and `streamWriter.writec.spec` return a uniform `msgChanAt ch ν lid`, with no
     peer and no message predicate.
   - So `streamWriter.run` cannot meet `msgAppV2Encoder.encode.spec`'s `m.type = MsgApp ∧ m.to = dst`.
     That premise is load-bearing: the short frame's decoder rebuilds `To := local`.
   - **Fix:** `msgChanAt ch ν lid pid K` with a message predicate `K`; `pick`'s post ties `K m` to
     the channel picked; `peer.send` takes `m.to = pid`.
3. **No source for `Http.readerAt` of a reader that is not HTTP.**
   - `pipeline.post` uses `bytes.NewBuffer(data)` as a request body.
   - `createSnapBody` builds `io.MultiReader` + `ReaderAndCloser`.
   - The server's merged snapshot is an `io.Pipe` reader; snap wraps it in an `ExactReadCloser`.
   - `RoundTrip` needs `readerAt bd ...`, and `readerAt` is net/http's opaque predicate, with no
     intro law. The old boundary had `NewBuffer_ok` and an `io.MultiReader` axiom.
   - **Fix:** boundary specs or laws producing `readerAt`: a buffer whose complete stream is `bs`,
     the composition by `MultiReader`/`ReaderAndCloser`, a pipe. And name an owner (the batch report
     asks "Who owns them?").
4. **The order in `snapshotHandler.ServeHTTP`'s sketch is wrong.**
   - The handler dereferences `m.Snapshot.Metadata` (`http.go:279`) before `SaveDBFrom` reaches
     `EOF`. `servePre`'s body reader has `Pre = True`, so at that point the handler knows nothing
     about the decoded envelope, and "the snapshot is non-nil (`msgSent_snap`)" is not available yet.
   - The spec still holds only through `serveDone`'s panic disjunct, if Goose turns a nil
     dereference into a recoverable `PanicV` (**uncertain**).
   - **Fix:** a prefix knowledge for request bodies (a `Proto` field `bodyPre`, as D42's
     `sreq Pre`), or a sketch that names the panic path.
5. **`protoAt_agree.spec` cannot be realized either.** Lean equality `⌜P = P'⌝` of higher-order
   protocols cannot come from saved protocols, the header's own realization. Nothing in the batch
   uses it: drop it, or state it as `▷` equivalence.
6. **`Serve` never gives `protoOwn a P` back.** A member restarted in-process cannot serve its
   address again: `examples/etcd/leasesnap/leasesnap_test.go:222,332` restart through the
   integration framework, which re-listens on the same peer addresses. Return `protoOwn a P` in
   `Serve`'s post. Handler runs still in flight serve the same `P`, so this is harmless.
7. **A comma in a member's peer URL** (Go behaviour; nonissue candidate).
   - `types.NewURLs` accepts `http://a,b:2380`: `url.Parse` and `SplitHostPort` both succeed (run
     with go1.27.3).
   - The receiver splits `X-PeerURLs` on `","` (`util.go:202`, `http.go:423`), and `AddRemote`'s
     `Logger.Panic` fires (recovered by `Serve`). So `addRemoteFromRequest`'s
     `urlsHosts (split ...) = some hs` cannot be proved from `trCfg`/`urlsAt`.
   - **Fix:** add a no-comma fact to `urlsAt` (types' request).
   - This case is not covered by `nonissues/etcd-rafthttp-addremote-bad-peerurls-panic.md` (that
     one is about a non-member's header); it should be recorded as a nonissue: a precondition real
     configurations meet.
8. **`raftProto`'s request knowledge must exclude `MsgSnap` on `POST /raft`.** `pipelineHandler`
   does no type check (`http.go:103-170`), so without it `recvd`'s snapshot clause cannot be
   proved. The same holds for stream frames (`decodeLoop`'s "no `MsgSnap` comes by a stream").
   State `sendable` in the realization.
9. **`postHdrs` is opaque.** The sender has to prove `onceOnly R` (no idempotency key) to decide the
   ticket branch of `roundTripperOk`. Add a fact about `postHdrs` (or `postHdrs_onceOnly`).

## What is good

- **At most once, checked path by path.**
  - `Transport.Send` hands each message to exactly one of peer or remote (`transport.go`, `Send`).
  - `peer.send` sends without blocking on one picked channel (`peer.go:245-265`).
  - The stream writer encodes each dequeued message once, and on an error or a new connection drops
    the queue: `closeUnlocked` replaces `msgc` (`stream.go:339`) and `run` resets its local `msgc`.
    Late `peer.send`s on the old channel are never read.
  - The pipeline `POST`s once, with no retry (`pipeline.go:97-170`).
  - The stream reader decodes its one response once.
  - A replayed stream `GET` does no harm: the per-frame deposits `inv (msgCredit ∨ tok τ i)` of
    both runs are keyed by the reader's exclusive `tok τ i`. Whichever deposit the reader's
    knowledge names, each token withdraws one credit, and credits are indexed by message value.
- **Wrong-member delivery** is harmless for safety: `Process` checks `To` (`server.go:710-717`),
  and the stream handler checks `X-Raft-To` (`http.go:436-448`). The liveness cost is recorded
  (`nonissues/etcd-rafthttp-misaddressed-403-member-removed.md`).
- **The msgappv2 codec** (`msgappv2_codec.go:87-254`): the encoder and decoder states move in step
  (full frame: term and last index; short frame: `index += len`). The rebuilt message equals `m`
  exactly under `sendable`'s shape. `Msg` has no other field (`raft/v3/Model.lean:267-280`).
- **The snapshot message is closed exactly once**: `SendSnapshot`'s not-found branch, or `send`'s
  deferred `CloseWithError`. The repeated `Close`s of the reader are idempotent pipe closes.
- `Stop`, `RemovePeer` after `Stop`, `UpdatePeer` of an unknown peer, and `Send` to a stopped peer
  are all panic-free, as the specs say. `trRunning`'s split rules out `AddPeer` after `Stop`.
- Moving the old D38b ticket rule to "no ticket for `GET`" is right, and the replay analysis in the
  header is accurate.

## Snippets

| snippet | verdict | proof sketch / blocker |
|---|---|---|
| `ReqStartTransport` | provable, given the provisional stats/types/snap specs | `Start` gives `isTransport`, `trRunning 1`; `AddRemote`/`AddPeer` with `urlsHosts`/`peerAddr` from the assumptions |
| `ReqSendReady` | provable under its `Assumes:` | needs R1's `MsgApp` shape law (2nd tier, item 1); `Send` with `outMsg` per message |
| `ReqMembership` | provable | `AddPeer` of `self` is harmless; no spec excludes it |
| `ReqConnected` | provable | `ActivePeers` post `0 ≤ cnt` |
| `ReqStop` | provable | `Stop` takes `trRunning 1`; later `Send`/`RemovePeer` need only `isTransport` |
| `ReqSendMergedSnapshot` | provable modulo snap's `NewMessage` keeping `Http.readerAt` (2nd tier, item 3) | `outSnap` from snap's `NewMessage`; `SendSnapshot` |
| `Receiver.Process` | **not provable** (F6) | |
| `ReqServePeer` | provable only for `P = raftProto ν` (F7) | |

## Targets ranked by need of revision

1. `SpecPlan/Spec/net/http/Api.lean`, `Serve.lean`, `NewListener.lean` (rafthttp's): F1, F2, F3, and
   second-tier items 3, 5, 6.
2. `SpecPlan/Spec/.../rafthttp/Api.lean`: F4, F7 (with Http), and second-tier items 2 and 8.
3. The snapshot path: the snap request and `snapshotHandler.ServeHTTP`'s sketch (F5, second-tier
   item 4).
4. `examples/specreq/rafthttp/receive.go` (F6, F7).
5. `req/go_etcd_io_raft_v3.md` from 2f (second-tier item 1), and the types request (second-tier
   item 7).
6. The internal queue specs `peer.send`, `peer.pick`, `streamWriter.writec` (second-tier item 2).
7. The other internal specs: sound as far as I checked.

## Verdict

Not done. Seven first-tier findings:
- three unsound trust-boundary statements (F1, F2, F3);
- two laws or requests nothing can realize or that are false of the code (F4, F5);
- two snippets that cannot be proved (F6, F7).

The core design of the transport (the at-most-once argument, the codec shape, the ticket rule
narrowed to `onceOnly`) is sound. The fixes are local and do not change its client-facing shape.
