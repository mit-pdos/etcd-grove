/-
# rafthttp, etcd's raft transport (batch 2f): the vocabulary

What etcd's server may use of rafthttp (`Transport`: `Start`, `Handler`, `Send`, `SendSnapshot`,
`AddPeer`, `AddRemote`, `RemovePeer`, `RemoveAllPeers`, `UpdatePeer`, `ActiveSince`, `ActivePeers`,
`Stop`, and the test hooks `CutPeer`, `MendPeer`, `Pause`, `Resume`), and what rafthttp's own
functions are specified over (the internal section). The specs are the files beside this one.

## The shape, in words

A **raft network** `ν : Net` is the transport layer of one raft cluster `ν.γ` (R1's
`Raft.Cluster`): every member's `Transport` is started on the same `ν`. The client allocates it
(`net_alloc`) with the meaning of the database images snapshots carry (`snapImg ν i bs`: "`bs` is
an image a sender certified for a snapshot of index `i`", whatever persistent fact the client
chooses: for etcd's server, the backend of the committed state through `i`).

**Delivery.** `Send` takes, for each message `m` (raft's `Ready` messages), its `msgSent ν.γ m` and
its `msgCredit ν.γ m` (R1); `SendSnapshot` takes a `MsgSnap`'s with its database reader, whose
complete streams are `snapImg` images. Each message is delivered **at most once**, to the member
serving the URL its `To` names, as a call of that member's `Raft.Process` with a fresh copy of `m`
and the same two facts (`recvd`); a `MsgSnap`'s database is saved in the receiver's snapshot
directory first (the client's `saveOk` update fired: `ν.dbIn`). Messages may be lost and reordered; nothing is promised about
`ReportUnreachable`/`ReportSnapshot` beyond their being calls of the receiver's contract
(liveness only). The receiver's `Raft` is the client's (`raftOk`): `Process` must accept such a
message (it checks `To` itself: etcd's answers `403` to a message for another member).

**At most once** (the answer to R1's question, `reviews/R1-completeness-1.md` S8): every path
dequeues a message once. `peer.send` puts it on one channel (a stream writer's `msgc` or the
pipeline's), non-blocking (full: dropped); a stream writer encodes it once on its one live
connection (a broken connection's queue is dropped with the channel, `closeUnlocked`); the reader
decodes each frame of its one response once; the pipeline `POST`s it once, with no retry, and Go's
client never replays a `POST` (`Request.isReplayable`); a `GET` it may replay (a stream's dial)
opens a second handler run whose bytes the client never reads. So etcd's `γ.dup = false` is sound
over rafthttp; the proof carries the one-shot credit through the HTTP boundary by a ticket (pipeline,
snapshot) or the reader's per-frame tokens (streams), below.

**Addresses.** The closed world of the HTTP boundary (`Spec/net/http/Api.lean`): a member's peer
URLs are reserved for a protocol that agrees with rafthttp's `raftProto ν` under `/raft`
(`peerAddr ν a`), and only members' transports send to them. Every URL the client gives the
transport (`AddPeer`, `AddRemote`, `UpdatePeer`, the local `URLs` advertised in `X-PeerURLs`) has
such a host; the client (the server's membership) keeps that fact for its members' URLs.

**Lifecycle.** `Start` turns the client's `Transport` struct into `isTransport t ν id`
(persistent: every method is safe for concurrent use) and `trRunning t 1` (fractional): `AddPeer`
takes a fraction (it panics after `Stop`), `Stop` the whole. Methods taking the transport's read
lock (`Send`, `ActiveSince`, `ActivePeers`, `Get`, `CutPeer`, `MendPeer`, `Pause`, `Resume`) take
the caller's `threadTok` and give it back (`notes/bounds-plan.md`: the transport turns it into a
reader slot of its `RWMutex`).

## Intended realization (rafthttp's proof)

- `Net`: the names of the cluster's raft protocol state for transport: a registry of stream
  readers' token maps (a ghost map from request names to the reader's per-frame tokens, as the
  old `streamRegInv`), `snapImg` a saved predicate fixed at `net_alloc`.
- `raftProto ν` (the HTTP protocol of `/raft`): a `POST /raft` request (no idempotency key:
  `onceOnly`) whose complete body is a protobuf encoding of a message `m`, **not a `MsgSnap`**
  (`sendable`), with `msgSent` and a deposit `inv (msgCredit m ∨ reqTicket τ)` (withdrawn once with
  the ticket the handler receives); a `POST /raft/snapshot` whose body's every prefix (`bodyPre`) is
  a prefix of a message frame of a `MsgSnap` (the same facts) followed by a stream of an image `img`
  with `snapImg ν i img`, and whose complete body is such; a
  `GET /raft/stream/{msgapp,message}/<B>` with `X-Raft-To` naming the dialed member and `τ` naming
  the reader's token map in the registry, whose `200` responses are prefixes of a chain of frames
  (the codec's: `msgFrame`, or msgappv2's from the initial state) of messages each a link
  heartbeat or a message to `B` with `msgSent` and a deposit `inv (msgCredit ∨ tok τ i)` for its
  frame index `i`; headers `X-Server-Version` a parsable version (the dialer's `MustParse`); and
  for every other request and status, nothing (any response, the mux's `404`/`301` included).
- `isTransport t ν id`: the struct's read-only fields (`ID = id`, `Raft` with `raftOk`, the
  round trippers' `roundTripperOk`, the logger, the stats), and an `RWMutex` whose invariant holds
  the `peers`/`remotes` maps with each value's `peerAt`/`remoteAt` and stop right, and the provers;
  `trRunning`: a fractional token against which the invariant's "maps non-nil" is kept.
- The peers' and remotes' goroutines: the pipeline workers (a `WaitGroup` backed by their thread
  tokens), the stream writers and readers (each with a `done` channel whose last payload gives back
  their resources), the two `Process` loops per peer. The handlers run on `Serve`'s goroutines.

## Requirement snippets

`examples/specreq/rafthttp/`: `transport.go` (`ReqStartTransport`: the server's literal, `Start`,
the remotes and peers; `ReqSendReady`: a `Ready`'s messages, a `MsgSnap` diverted; `ReqMembership`:
add, update, remove, reset on a snapshot; `ReqConnected`: `ActiveSince`/`ActivePeers` as health
heuristics through the `Transporter` interface; `ReqStop`; `ReqErrorC`), `snapshot.go`
(`ReqSendMergedSnapshot`: `SendSnapshot`, then the close notification; `ReqInstallReceived`: a
received `MsgSnap`'s file opened by index), `receive.go` (`Receiver`: a `Raft` that steps a message
addressed to it; `ReqServePeer`: the handler on a peer mux beside other endpoints;
`ReqServeRoot`: the handler served at the root; `ReqRestartServe`: serve, close, listen and serve
again with a second transport of the same member).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.Api
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp
public import Spec.go_etcd_io.raft.v3.Api
public import Spec.net.http.Api
public import Spec.go_uber_org.zap.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft

/-! ## Ghost names -/

/-- A raft network's own ghost names (opaque). -/
opaque NetNames : Type := Unit

/-- A stream's type (`streamType`): `streamTypeMsgAppV2` (`"msgappv2"`) or `streamTypeMessage`
(`"message"`). -/
inductive StreamTy where
  | msgAppV2
  | message
  deriving DecidableEq

/-- The Go value of a stream type (`streamType` is a `string`). -/
def StreamTy.str : StreamTy → GoString
  | .msgAppV2 => go!"msgappv2"
  | .message => go!"message"

/-- The stream path's prefix of a type (`streamType.endpoint`). -/
def StreamTy.endpoint : StreamTy → GoString
  | .msgAppV2 => go!"/raft/stream/msgapp"
  | .message => go!"/raft/stream/message"

/-! ## Pure facts -/

/-- **A message the transport may send for member `lid`** (`Send`'s premise, besides raft's
facts): not a `MsgSnap` (those go by `SendSnapshot`: the pipeline would deliver it without its
database), and a `MsgApp` of raft's shape from `lid` (the msgappv2 stream's short frame carries
only the entries and the commit, and the receiver rebuilds `From`, `To`, `Term`, `LogTerm`,
`Index` from its state and leaves the other fields zero: `msgappv2_codec.go`). A message to `0` is
skipped (etcd's server marks the messages it diverts so). -/
def sendable (lid : w64) (m : Msg) : Prop :=
  m.to ≠ W64 0 →
    m.type ≠ MsgSnap ∧
    (m.type = MsgApp → m.src = lid ∧ m.vote = W64 0 ∧ m.snapshot = none ∧ m.reject = false ∧
      m.rejectHint = W64 0 ∧ m.context = [])

/-- The link heartbeat (`linkHeartbeatMessage`): a `MsgHeartbeat` from and to `0`, which no raft
node sends (raft's messages are from a non-zero id). -/
def isLinkHeartbeat (m : Msg) : Prop := m.type = MsgHeartbeat ∧ m.src = W64 0 ∧ m.to = W64 0

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A raft network**: the transport layer of the raft cluster `γ`, with the client's two
meanings fixed at its allocation (round 1, F4: fields, not saved predicates): `img i b`, what a
database image sent with a snapshot of index `i` is (for etcd: the backend holding the committed
state through `i`); `dbIn i`, what a receiver's `Process` learns of a `MsgSnap` of index `i` once
its image was saved in the snapshot directory (the client's: its invariant over 2e's `snapDbs`). -/
structure Net (GF : BundledGFunctors) where
  γ : Raft.Cluster
  names : NetNames
  img : w64 → Snap.BeImage → IProp GF
  dbIn : w64 → IProp GF

/-! ## Provisional: other batches' vocabulary

The statements below need predicates of packages whose batches state them alongside (`snap`,
`v2stats`: 2e; `client/pkg/v3/types`: 1c; the server's error channel: 2d). These declarations
stand for them until they exist (`notes/specs-only/req/*.md`, "from 2f"): at integration they are
replaced by those batches' names, over the same meaning. -/

/-- (v2stats, 2e; integration I4: 2e's `V2stats.isServerStats`) The server's `*ServerStats`
(persistent; its methods lock). -/
abbrev serverStatsOk (s : Loc) : IProp GF := V2stats.isServerStats s

/-- (v2stats, 2e; integration I4: 2e's `V2stats.leaderStatsOwn`, which `NewLeaderStats` gives) The
leader's `*LeaderStats` (exclusive to the transport: it adds followers and deletes them from the map
under its own lock, `nonissues/etcd-rafthttp-leaderstats-followers-race`). -/
abbrev leaderStatsOwn (s : Loc) : IProp GF := V2stats.leaderStatsOwn s

/-- (v2stats, 2e; integration I4: 2e's `V2stats.isFollowerStats`) A follower's `*FollowerStats`
from `LeaderStats.Follower` (persistent). -/
abbrev followerStatsOk (s : Loc) : IProp GF := V2stats.isFollowerStats s

-- (integration I4) `urlsHosts`, `urlsAt` were provisional here: now 1c's `Types.urlsHosts`,
-- `Types.urlsAt` (`client/pkg/v3/types/Api.lean`).

/-- (types, 1c; round 1) **No URL string of `hs`'s source contains a comma** (the receiver splits
`X-PeerURLs` on `","`: `nonissues/etcd-rafthttp-peerurl-comma-split.md`): a fact `urlsAt` gives. -/
opaque urlsNoComma (sl : GoSlice) : IProp GF := iprop(True)

/-- (snap, 2e/2f) **The bytes `bs` are a stream of image `img`** (pure, opaque; 2e's `dbReader r
img` is a reader yielding such bytes). -/
opaque imgBytes (img : Snap.BeImage) (bs : List w8) : Prop := True

/-- (snap, 2e) **The merged message's fields** (persistent, read-only): its raft message `ml`, its
reader `rc` (2e's `isMessage` should carry them: `req/..._snap.md`, "from 2f", round 1). -/
opaque snapMsgOwn (mp ml : Loc) (rc : GoInterface) : IProp GF := iprop(True)

/-- (server, 2d) **The server's error channel** `ch` (`chan error`, persistent): any goroutine may
send any error on it without blocking (`select` with `default`: `reportCriticalError`). -/
opaque errChanOk (ch : GoChan) : IProp GF := iprop(True)

/-! ## The client-facing vocabulary -/

/-- **`img` is a database image certified for a snapshot of index `i`** in network `ν` (persistent;
its meaning is the client's, `ν.img`). -/
def snapImg (ν : Net GF) (i : w64) (img : Snap.BeImage) : IProp GF := iprop(□ ν.img i img)

/-- **rafthttp's HTTP protocol** for the paths under `/raft` (see the header). -/
opaque raftProto (ν : Net GF) : Http.Proto GF :=
  ⟨fun _ _ => iprop(True), fun _ _ _ => iprop(True), fun _ _ _ => iprop(True),
    fun _ _ _ _ _ => iprop(True)⟩

/-- **`P` is compatible with rafthttp's protocol** (round 1, F7 and completeness F1): it agrees with
`raftProto ν` on `/raft` and its subtree, and allows the mux's `404`/`301` elsewhere (a peer port's
protocol serving other endpoints beside rafthttp's). -/
def raftCompat (ν : Net GF) (P : Http.Proto GF) : Prop :=
  Http.Proto.agreeUnder go!"/raft" P (raftProto ν) ∧
  Http.Proto.agreeUnder go!"/raft/" P (raftProto ν) ∧
  ∀ R τ, ¬ Http.pathUnder go!"/raft" R.path → ¬ Http.pathUnder go!"/raft/" R.path →
    (⊢ □ P.resp R τ (W64 404) [] []) ∧ (⊢ □ P.resp R τ (W64 301) [] [])

/-- **`a` is a peer address of `ν`** (persistent): reserved (`Http.reserve`) for a protocol
compatible with `raftProto ν`. -/
def peerAddr (ν : Net GF) (a : GoString) : IProp GF :=
  iprop(∃ P : Http.Proto GF, Http.protoAt a P ∗ ⌜raftCompat ν P⌝)

/-- **What a received message carries** (to a receiver of network `ν`): raft's facts, and for a
`MsgSnap` the client's `dbIn` of its snapshot's index (round 1, F5 and completeness F3: given by
the client's own save update, which `SaveDBFrom` fired over 2e's `snapDbs` with an image the sender
certified; whatever file `SaveDBFrom` kept, the client's invariant says what it holds). -/
def recvd (ν : Net GF) (m : Msg) : IProp GF :=
  iprop(msgSent ν.γ m ∗ msgCredit ν.γ m ∗
    (if m.type = MsgSnap then
      iprop(∃ s : Snapshot, ⌜m.snapshot = some s⌝ ∗ ν.dbIn s.index)
     else iprop(True)))

/-- **The client's save update** for the snapshot directory `sd` (persistent): for any image the
sender certified for index `i`, an update saving it (2e's `saveAt`: kept if a file of `i` is
there) whose commit gives `ν.dbIn i`. What `SaveDBFrom` fires. -/
def saveOk (ν : Net GF) (sd : GoString) : IProp GF :=
  iprop(□ ∀ (i : w64) (img : Snap.BeImage), □ ν.img i img -∗
    AU <{ ∃∃ (F : Nat → Option Snap.BeImage), Snap.snapDbs sd F }> @ ⊤, ∅
      <{ Snap.snapDbs sd (Snap.saveAt F (uint.nat i) img), COMM ν.dbIn i }>)

/-- **An error `Process` may return** (persistent): `nil`, or an error whose `Error()` returns, on
which `errors.As` against `writerToResponse` returns, and whose `WriteTo(w)` (if it has one) writes
some response on a writer whose protocol allows any (the pipeline and snapshot handlers' answers).
Introduced by `procErr_nil`, `procErr_nodeErr` (raft's errors) and the server's `HTTPError`'s law
(2d's). -/
opaque procErr (err : GoInterface) : IProp GF := iprop(True)

/-- **The receiver's `Raft`** `r` for member `id` of `ν` (persistent; the
client's, a bundle as `sync.isLocker`): `Process(ctx, m)` of a fresh message (owned) with what a
received message carries (`recvd`), on a thread with its token: returns an error (`procErr`) and the
token; `IsIDRemoved(x)` (with a token: etcd's reads its membership under a lock): some boolean;
`ReportUnreachable(x)`, `ReportSnapshot(x, st)`: return. -/
def raftOk (ν : Net GF) (id : w64) (r : GoInterface) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜r = interface.ok i⌝ ∗
    (□ ∀ (ctx : GoInterface) (ml : Loc) (m : Msg) (Ψ : val → IProp GF),
      Context.ctxOk ctx -∗ msgPts ml (DFrac.own 1) m -∗ recvd ν m -∗ threadTok -∗
      ▷ (∀ err : GoInterface, procErr err -∗ threadTok -∗ Ψ #err) -∗
      WP (App (App (Val #(methods i.ty go!"Process" i.v)) (Val #ctx)) (Val #ml)) {{ Ψ }}) ∗
    (□ ∀ (x : w64) (Ψ : val → IProp GF),
      threadTok -∗ ▷ (∀ b : Bool, threadTok -∗ Ψ #b) -∗
      WP (App (Val #(methods i.ty go!"IsIDRemoved" i.v)) (Val #x)) {{ Ψ }}) ∗
    (□ ∀ (x : w64) (Ψ : val → IProp GF),
      ▷ Ψ #() -∗ WP (App (Val #(methods i.ty go!"ReportUnreachable" i.v)) (Val #x)) {{ Ψ }}) ∗
    (□ ∀ (x st : w64) (Ψ : val → IProp GF),
      ▷ Ψ #() -∗
      WP (App (App (Val #(methods i.ty go!"ReportSnapshot" i.v)) (Val #x)) (Val #st)) {{ Ψ }}))

/-- **A message handed to the transport of member `lid`** at `ml`: a share of its memory (the
transport's for good: the writer goroutines marshal it later), and, unless it is skipped (`To` is
`0`), raft's facts and the transport's premise. -/
def outMsg (ν : Net GF) (lid : w64) (ml : Loc) (m : Msg) : IProp GF :=
  iprop((∃ dq, msgPts ml dq m) ∗ ⌜sendable lid m⌝ ∗
    (if m.to = W64 0 then iprop(True) else iprop(msgSent ν.γ m ∗ msgCredit ν.γ m)))

/-- **A merged snapshot message handed to the transport**: the `snap.Message` with its raft
message (a `MsgSnap` with raft's facts and a snapshot) and its reader, whose complete streams are
`snapImg` images of the snapshot's index. -/
def outSnap (ν : Net GF) (mp : Loc) : IProp GF :=
  iprop(∃ (ml : Loc) (rc : GoInterface) (m : Msg) (s : Snapshot) (dq : DFrac) (sz : w64)
      (img : Snap.BeImage),
    snapMsgOwn mp ml rc ∗ Snap.isMessage mp m.to sz ∗ Snap.msgClose mp ∗
    msgPts ml dq m ∗ ⌜m.type = MsgSnap ∧ m.snapshot = some s⌝ ∗
    msgSent ν.γ m ∗ msgCredit ν.γ m ∗ Snap.dbReader rc img ∗ snapImg ν s.index img)

/-- **A started transport** `t` of member `id` of `ν` (persistent). -/
opaque isTransport (t : Loc) (ν : Net GF) (id : w64) : IProp GF := iprop(True)

/-- **The transport `t` is not stopped** (fractional; `Stop` takes it whole, `AddPeer` a share). -/
opaque trRunning (t : Loc) (q : Qp) : IProp GF := iprop(True)

/-- **A `Transporter` interface value** holding a started transport (persistent; the server's
`r.transport`, read by `util.go`'s heuristics through the interface). -/
def transporterOk (tp : GoInterface) (ν : Net GF) (id : w64) : IProp GF :=
  iprop(∃ t : Loc, ⌜tp = interface.mkOk
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty) #t⌝ ∗
    isTransport t ν id)

/-- **The fields `Start` needs of a `Transport` literal** `tv` for member `tv.ID` of `ν`: a logger
(or none), its receiver's `Raft` with the snapshotter, the stats, the error channel, its own peer
URLs (each a peer address of `ν`: they are advertised in `X-PeerURLs`), an unlocked mutex. The
other fields are any (`Start` sets the round trippers, maps and probers; `TLSInfo` and
`DialTimeout` only decide whether `Start` fails). -/
def trCfg (tv : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport) (ν : Net GF) :
    IProp GF :=
  iprop((⌜tv.Logger' = null⌝ ∨ Zap.isLogger tv.Logger') ∗
    raftOk ν tv.ID' tv.Raft' ∗ (∃ sd, Snap.isSnapshotter tv.Snapshotter' sd ∗ saveOk ν sd) ∗
    serverStatsOk tv.ServerStats' ∗ leaderStatsOwn tv.LeaderStats' ∗ errChanOk tv.ErrorC' ∗
    (∃ hs, Types.urlsAt tv.URLs' hs ∗ urlsNoComma tv.URLs' ∗ [∗list] a ∈ hs, peerAddr ν a) ∗
    ⌜tv.mu' = zero_val _root_.Perennial.sync.RWMutex⌝)

/-! ## Internal (rafthttp's own functions; no client sees them) -/

/-- (internal) A started `*peer` `p` of the transport of `lid` for peer `pid` (persistent). -/
opaque peerAt (p : Loc) (ν : Net GF) (lid pid : w64) : IProp GF := iprop(True)

/-- (internal) The right to stop peer `p` once (exclusive; in the transport's map invariant). -/
opaque peerStopRight (p : Loc) : IProp GF := iprop(True)

/-- (internal) A `Peer` interface value holding a started `*peer`. -/
def peerIface (pv : GoInterface) (ν : Net GF) (lid pid : w64) : IProp GF :=
  iprop(∃ p : Loc, ⌜pv = interface.mkOk
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer.ty) #p⌝ ∗
    peerAt p ν lid pid)

/-- (internal) A started `*remote` (persistent) and its stop right (exclusive). -/
opaque remoteAt (g : Loc) (ν : Net GF) (lid pid : w64) : IProp GF := iprop(True)
opaque remoteStopRight (g : Loc) : IProp GF := iprop(True)

/-- (internal) A `*pipeline` literal before `start` (exclusive: `startPeer`'s, `startRemote`'s), a
started one (persistent), its stop right, and one of its four workers' shares (`handle`'s). -/
opaque pipeFresh (pl : Loc) (ν : Net GF) (lid pid : w64) : IProp GF := iprop(True)
opaque pipeAt (pl : Loc) (ν : Net GF) (lid pid : w64) : IProp GF := iprop(True)
opaque pipeStopRight (pl : Loc) : IProp GF := iprop(True)
opaque pipeWorker (pl : Loc) : IProp GF := iprop(True)

/-- (internal) **A message queue** `ch` of the transport of `lid` to peer `pid` (a stream writer's
`msgc`, a pipeline's; persistent): every value sent on it is a message with its `outMsg` facts,
`To = pid`, and `K` (the msgappv2 writer's: a `MsgApp`; round 1, second tier 2). Sends are
non-blocking (`select` with `default`). -/
opaque msgChanAt (ch : GoChan) (ν : Net GF) (lid pid : w64) (K : Msg → Prop) : IProp GF :=
  iprop(True)

/-- (internal) **A receive queue** `ch` of member `lid` (a peer's `recvc`/`propc`; persistent):
every value is a fresh message with what a received message carries (`recvd`). -/
opaque recvChanAt (ch : GoChan) (ν : Net GF) : IProp GF := iprop(True)

/-- (internal) A started `*streamWriter` (persistent), its stop right; one attached (pending)
connection's right. -/
opaque swAt (cw : Loc) (ν : Net GF) (lid pid : w64) (K : Msg → Prop) : IProp GF := iprop(True)
opaque swStopRight (cw : Loc) : IProp GF := iprop(True)
/-- (internal) What `run` owns (the loop's local state: the encoder, the live connection). -/
opaque swRun (cw : Loc) : IProp GF := iprop(True)

/-- (internal) **An outgoing connection** `*outgoingConn` at `c` for the stream of type `t` from
`lid` to `pid` (exclusive): the stream handler's response writer after its `200` (committed, a
stream response of `raftProto ν` to `pid`'s `GET`), with the right to close it once, which gives
the writer back to the handler (through its close notifier). -/
opaque outConn (c : Loc) (ν : Net GF) (lid pid : w64) (t : StreamTy) : IProp GF := iprop(True)

/-- (internal) A `*streamReader` literal before `start` (exclusive), a started one (persistent),
its stop right, and what `run`/`decodeLoop` own. -/
opaque srFresh (cr : Loc) (ν : Net GF) (lid pid : w64) : IProp GF := iprop(True)
opaque srAt (cr : Loc) (ν : Net GF) (lid pid : w64) : IProp GF := iprop(True)
opaque srStopRight (cr : Loc) : IProp GF := iprop(True)
opaque srRun (cr : Loc) : IProp GF := iprop(True)

/-- (internal) **A dialed stream's body** `rd` of type `t` from `pid` to `lid` (exclusive): a `200`
response of `raftProto ν` to the reader's `GET`, read from its start, with the reader's per-frame
tokens. -/
opaque streamBody (rd : GoInterface) (ν : Net GF) (lid pid : w64) (t : StreamTy) : IProp GF :=
  iprop(True)

/-- (internal) A `*snapshotSender` (persistent) and its stop right. -/
opaque ssAt (s : Loc) (ν : Net GF) (lid pid : w64) : IProp GF := iprop(True)
opaque ssStopRight (s : Loc) : IProp GF := iprop(True)

/-- (internal) A `*urlPicker` (persistent): every URL it picks has a peer address of `ν` as host.
-/
opaque pickerAt (pk : Loc) (ν : Net GF) : IProp GF := iprop(True)

/-- (internal) A `*peerStatus` (persistent). -/
opaque statusAt (s : Loc) : IProp GF := iprop(True)

/-- (internal) A `*closeNotifier` (persistent), and the right to close it once (exclusive). -/
opaque cnAt (n : Loc) : IProp GF := iprop(True)
opaque cnCloseRight (n : Loc) : IProp GF := iprop(True)

/-- (internal) **A writer** `w` (an `io.Writer`: a stream's response writer, a `bytes.Buffer`)
that has written `bs`, and may write bytes `ys` when `Ok (bs ++ ys)` (persistent knowledge the
receiving side reads). Exclusive. -/
opaque writerAt (w : GoInterface) (Ok : List w8 → IProp GF) (bs : List w8) : IProp GF :=
  iprop(True)

/-- (internal, provisional: raftpb's, 3h) **`e` is a protobuf encoding of `m`** (`proto.Marshal`'s
output; `proto.Unmarshal` of it gives `m` back, below `2 ^ 63` bytes). -/
opaque pbEncodes (e : List w8) (m : Msg) : Prop := True

/-- (internal) **The message codec's frame** of an encoding `e`: its length, eight bytes
big-endian, then `e` (`messageEncoder`). -/
opaque msgFrame (e : List w8) : List w8 := []

/-- (internal) **The msgappv2 codec's frame** of `m` from state `st` (the last `(term, index)`)
on the stream from `lid` to `pid`, and the next state: a heartbeat, an `AppEntries` frame (`m` a
`MsgApp` at the state's term and index: its entries and commit), or a full frame. -/
opaque v2Frame (st : w64 × w64) (lid pid : w64) (m : Msg) (fb : List w8) (st' : w64 × w64) :
    Prop := True

/-- (internal) **Bytes after a reader's position are a prefix of a chain of msgappv2 frames** from
state `st` on the stream from `src` to `dst` (what the decoder needs not to panic: its lengths and
entries are an encoder's). -/
opaque v2Compat (st : w64 × w64) (src dst : w64) (ys : List w8) : Prop := True

/-- (internal) A `*messageEncoder` writing on `w` (persistent: its one field). -/
opaque msgEncAt (enc : Loc) (w : GoInterface) : IProp GF := iprop(True)

/-- (internal) A `*messageDecoder` reading `rd` (persistent: its one field). -/
opaque msgDecAt (dec : Loc) (rd : GoInterface) : IProp GF := iprop(True)

/-- (internal) A `*msgAppV2Encoder` writing on `w` for the stream from `src` to `dst`, at codec state
`st` (exclusive: its buffers and state). -/
opaque v2EncAt (enc : Loc) (w : GoInterface) (src dst : w64) (st : w64 × w64) : IProp GF :=
  iprop(True)

/-- (internal) A `*msgAppV2Decoder` reading `rd` for the stream from `src` to `dst`, at codec state
`st` (exclusive). -/
opaque v2DecAt (dec : Loc) (rd : GoInterface) (src dst : w64) (st : w64 × w64) : IProp GF :=
  iprop(True)

/-- (internal) What a writer of the transport's lock holds (`removePeer`'s caller): the `peers` and
`remotes` maps with their entries' rights. Exclusive. -/
opaque trMaps (t : Loc) (ν : Net GF) (id : w64) : IProp GF := iprop(True)

/-- (internal) A `*pipelineHandler`, `*snapshotHandler`, `*streamHandler` of the transport of `lid`
(persistent: their fields). -/
opaque phAt (h : Loc) (ν : Net GF) (lid : w64) : IProp GF := iprop(True)
opaque shAt (h : Loc) (ν : Net GF) (lid : w64) : IProp GF := iprop(True)
opaque sthAt (h : Loc) (ν : Net GF) (lid : w64) : IProp GF := iprop(True)

/-- (internal) What `streamWriter.mu` guards (`closer`, `working`, `msgc`), held under the lock;
likewise `streamReader.mu`'s (`paused`, `closer`). Exclusive. -/
opaque swLocked (cw : Loc) : IProp GF := iprop(True)
opaque srLocked (cr : Loc) : IProp GF := iprop(True)

/-- (internal) One of the transport's probers (`probing.NewProber`'s; persistent). -/
opaque proberAt (p : GoInterface) : IProp GF := iprop(True)

/-- (internal) **A snapshot request** `r` from `lid` to `pid` (a `POST /raft/snapshot` built by
`createPostRequest` on a body from `createSnapBody`, with its protocol knowledge and ticket):
exclusive, what `snapshotSender.post` gives `RoundTrip`. -/
opaque snapReq (r : Loc) (ν : Net GF) (lid pid : w64) : IProp GF := iprop(True)

/-- (internal) **A snapshot request body** `bd` for message `m` (exclusive): a reader whose complete
streams are the message frame of an encoding of `m` followed by a `snapImg` image of its index. -/
opaque snapBodyAt (bd : GoInterface) (ν : Net GF) (m : Msg) : IProp GF := iprop(True)

/-- (internal, provisional: semver) A `*semver.Version` (persistent, read-only). -/
opaque semverAt (v : Loc) : IProp GF := iprop(True)

/-- (internal, provisional: semver) `semver.MustParse(s)` does not panic. -/
opaque semverParses (s : GoString) : Prop := True

/-- (internal) A version header value `serverVersion`/`minClusterVersion` accept without
panicking: empty (read as `2.0.0`) or a version. -/
def verHdrOk (s : GoString) : Prop := s = [] ∨ semverParses s

/-- (internal) The headers `createPostRequest` sets on a request from `from` of cluster `cid` with
content type `ct`, advertising the peer URLs with hosts `hs`. -/
opaque postHdrs (ct : GoString) (frm cid : w64) (hs : List GoString) :
    List (GoString × GoString) := []

/-- (internal) rafthttp's `POST`s are once-only (no idempotency key among `postHdrs`). -/
def postHdrs_onceOnly.spec : Prop :=
  ∀ ct frm cid hs (host path : GoString),
    Http.onceOnly ⟨go!"POST", host, path, postHdrs ct frm cid hs⟩

/-- (internal) `setPeerURLsHeader` turned `hdr` into `hdr'` (an `X-PeerURLs` naming the URLs with
hosts `hs`, or unchanged for `nil` URLs). -/
opaque peerURLsSet (hs : List GoString) (hdr hdr' : List (GoString × GoString)) : Prop := True

end vocab

/-! ## Laws

Obligations of rafthttp's proof (the client-facing ones first), used by its clients. -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.raft.v3.Assumptions]

def persistent.spec : Prop :=
  (∀ ν i img, Persistent (snapImg (GF := GF) ν i img)) ∧
  (∀ ν sd, Persistent (saveOk (GF := GF) ν sd)) ∧
  (∀ tp ν id, Persistent (transporterOk (GF := GF) tp ν id)) ∧
  (∀ ν a, Persistent (peerAddr (GF := GF) ν a)) ∧
  (∀ err, Persistent (procErr (GF := GF) err)) ∧
  (∀ ν id r, Persistent (raftOk (GF := GF) ν id r)) ∧
  (∀ t ν id, Persistent (isTransport (GF := GF) t ν id))

def trRunning_fractional.spec : Prop := ∀ t, Fractional (trRunning (GF := GF) t)

/-- **A new network** for cluster `γ`, with the client's meanings of database images and of a saved
snapshot (round 1, F4: the fields are what the client chose, literally). -/
def net_alloc.spec : Prop :=
  ∀ (γ : Raft.Cluster) (Img : w64 → Snap.BeImage → IProp GF) (DbIn : w64 → IProp GF),
    ⊢ (|==> ∃ ν : Net GF, ⌜ν.γ = γ ∧ ν.img = Img ∧ ν.dbIn = DbIn⌝ : IProp GF)

/-- **Reserve a peer address** for `ν`'s raft protocol (the whole address; a server composing
other protocols on its peer port reserves with `Http.reserve` and a `raftCompat` protocol). -/
def peerAddr_reserve.spec : Prop :=
  ∀ (ν : Net GF) (a : GoString),
    Http.addrFree (GF := GF) a ⊢ |==> peerAddr ν a ∗ Http.protoAt a (raftProto ν)

/-- `raftProto` is compatible with itself (its mux's answers off `/raft`). -/
def raftCompat_self.spec : Prop := ∀ ν : Net GF, raftCompat ν (raftProto ν)

/-- **2e's image reader is a body reader** whose complete stream is a stream of the image (what
`createSnapBody` hands `io.MultiReader`; trusted with 2e's `dbReader`). -/
def dbReader_readerAt.spec : Prop :=
  ∀ (rc : GoInterface) (img : Snap.BeImage),
    Snap.dbReader (GF := GF) rc img ⊢
      Http.readerAt rc (fun _ => iprop(True)) (fun bs => iprop(⌜imgBytes img bs⌝)) []

/-- **A body read after its envelope, whose complete streams are an image's bytes, is 2e's image
reader** (what `snapshotHandler` hands `SaveDBFrom`). -/
def readerAt_dbReader.spec : Prop :=
  ∀ (rd : GoInterface) (Pre Φ : List w8 → IProp GF) (r : List w8) (img : Snap.BeImage),
    Http.readerAt (GF := GF) rd Pre Φ r ∗ □ (∀ B, Φ (r ++ B) -∗ ⌜imgBytes img B⌝) ⊢
      Snap.dbReader rd img

/-- **The package's variables** (scope: no one writes them after initialization, which etcdmain
meets by clamping the flags to their defaults; embed's `--raft-read-timeout` below `3ns` does not,
`nonissues/etcd-embed-raft-read-timeout-ticker-panic.md`): `ConnReadTimeout`, `ConnWriteTimeout`
are read-only, at least `5s`; the error variables are fixed errors. -/
def vars_init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ⊢
    (∃ d : w64, globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.ConnReadTimeout ↦□ d ∗
      ⌜5000000000 ≤ sint.Z d⌝) ∗
    (∃ d : w64, globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.ConnWriteTimeout ↦□ d ∗
      ⌜5000000000 ≤ sint.Z d⌝) ∗
    (∃ e : GoInterface,
      errIs go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.ErrClusterIDMismatch e ∗
      Http.errOk e ∗ ⌜e ≠ interface.nil⌝)

/-- `nil` is a `Process` error. -/
def procErr_nil.spec : Prop := ⊢ procErr (GF := GF) interface.nil

/-- raft's node errors (`node.Step`'s: `nil`, `ErrStopped`, the context's) are `Process` errors
(the pipeline handler panics on them but `nil`: `Serve` recovers it). -/
def procErr_nodeErr.spec : Prop :=
  ∀ n ctx err, Raft.nodeErr (GF := GF) n ctx err ⊢ procErr err

/-- **`raftProto` allows the mux's own answers** to the paths under `/raft` no pattern of
`Handler()`'s mux routes. -/
def raftProto_muxAnswers.spec : Prop :=
  ∀ (ν : Net GF) (R : Http.HReq) τ,
    (⊢ □ (raftProto (GF := GF) ν).resp R τ (W64 404) [] []) ∧
    (⊢ □ (raftProto (GF := GF) ν).resp R τ (W64 301) [] [])

/-- (internal) **A writer's `Write(b)`** with permission for every prefix of `b`: writes a prefix
`n` of `b`, all unless it fails. Realized for a stream's connection from `Http.respW_write.spec`
(the protocol's prefix-closed `resp`) and for a `bytes.Buffer` (any `Ok`; it never fails). -/
def writerAt_write.spec : Prop :=
  ∀ (w : GoInterface) (i : GoInterfaceOk) (Ok : List w8 → IProp GF) (bs : List w8) (b : GoSlice)
    (ys : List w8) (dq : DFrac),
  w = interface.ok i →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ writerAt w Ok bs ∗ b ↦*{dq} ys ∗
      □ (∀ ys', ⌜ys' <+: ys⌝ -∗ Ok (bs ++ ys')) }}
    (App (Val #(methods i.ty go!"Write" i.v)) (Val #b))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      b ↦*{dq} ys ∗ ⌜uint.nat n ≤ ys.length ∧ (err = interface.nil → uint.nat n = ys.length)⌝ ∗
      writerAt w Ok (bs ++ ys.take (uint.nat n)) ∗ Http.errOk err }}

end laws

end Rafthttp
end EtcdGrove
end Perennial
