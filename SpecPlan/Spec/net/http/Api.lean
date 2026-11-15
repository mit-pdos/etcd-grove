/-
# net/http over TCP: the HTTP boundary (batch 2f, for rafthttp): a trust boundary

`net/http` is translated names-only: every statement here and in this directory is **assumed**.
They restate the boundary the user reviewed for rafthttp (`specs-ref/notes/rafthttp-http-boundary.md`,
2026-10-22; D38b, D42 and stage 5e's header model, `specs-ref/notes/rafthttp-plan.md`), over opaque
predicates, with one correction (below, "Tickets") and one generalization (below, "Generations":
an address's protocol is a family over the local generation, second crash pass). Why each is true of
Go's `net/http` over TCP is said where it is stated.

## The model

* **Requests as sent** (`HReq`): method, host (the `host:port` of the URL), path, headers (as set).
  The body is a reader the client hands to `NewRequest` (or none).
* **An address's protocol** (`Proto`): what the program's clients may send to that address and
  what its server may answer. `hreq R τ` (persistent knowledge of a request's line and headers,
  under the client's chosen ghost name `τ`), `bodyPre R τ B` (of every prefix `B` of its body
  read so far), `body R τ B` (of its complete body `B`), and
  `resp R τ st hs w` (of a response with status `st`, committed headers `hs`, after the handler
  wrote the bytes `w`; prefix-closed in `w`, an obligation of whoever defines a protocol). All are
  used under `□`: only **persistent** knowledge crosses the wire.
* **The closed world** (the user's decision 1, 2026-10-22; round 1, F3: tied to the bound socket).
  A listener is the socket a bind made: `net.Listen`/`NewListener` give `listenerAt l a` for the
  address string `a` the socket is bound at (the given one, or for port `0` the actual one the bind
  chose, `l.Addr()`). An address string's protocols are fixed once for the run (`reserve`: the
  environment's `addrFree a` becomes the persistent `protoFam a F`, one protocol `F L` per local
  generation `L`; it may precede the bind, since a member sends to its peers before they listen):
  in a generation `L` the address serves `protoAt a (F L)` (`protoFam_at`), and `Serve` on a
  listener at `a` serves `protoAt a P`'s `P`. Every request a handler on that listener reads was
  sent by a client of the program through `RoundTrip` to a host string with `protoAt _ P` that
  reaches the socket; so the handler gets the facts the client proved. A rebind of `a` (a member
  restarted after a stop) serves the same `P` (`protoAt` is persistent, and the family set once); a
  rebind after a crash serves the next generation's member of the family. **The environment's
  physical premise**: `addrFree` is issued for at most
  one string per socket (the strings the program dials its peers by are the ones their listeners
  are bound at: no two reserved strings, as `localhost:p` and `127.0.0.1:p`, name one socket),
  never for a port-`0` string, and no proxy relays peer traffic (rafthttp's round trippers use
  `ProxyFromEnvironment`: the deployment sets none for peer URLs). Port `0` needs nothing more: only
  the actual string the bind reports can be reserved and dialed.
* **Generations** (second crash pass, F-server-boot F3). A crash (Perennial's crash rule: the whole
  program's machine) closes every socket and every connection, and nothing is replayed across it:
  a request a handler of generation `L` reads was sent by a `RoundTrip` of generation `L`, over a
  connection of `L`. So an address's protocol may differ per generation, and a protocol whose
  predicates name generation-local vocabulary (a member's lease view, `EtcdModel.leaseViewLb`, which
  a crash does not carry) is reserved as the family of its instances at each generation's heap
  (`fun L => P (hG := ⟨hG.goose_globalGS, L⟩)`); a protocol of global vocabulary only is a constant
  family. The family, not a protocol, crosses a crash (`protoFam_gen`); `protoAt` is the current
  generation's. (Repair3-boot's `protoAt_gen`, one protocol for the run, is withdrawn: a client
  address's etcd contract names per-generation lease views, so the restarted member could not serve
  the first generation's contract, nor reserve its own, F-server-boot F3.)
* **Bodies are prefixes** (D42). A body reader yields successive pieces whose concatenation is a
  prefix of what the sender's side produced (the client's body reader; the handler's writes);
  `EOF` only at the end of a complete stream (HTTP/1.1 framing, chunked or with a length, makes a
  truncated body an `ErrUnexpectedEOF` or another error, never `EOF`); an error at any time.
* **The response's status and headers are the handler's** (decisions 2 and 4): the status it set,
  and its committed headers but for the keys Go's server sets itself (`srvKeys`).
* **Tickets** (D38b, corrected here). A request that Go's client never replays (`onceOnly`: a
  non-empty method other than `GET`, `HEAD`, `OPTIONS`, `TRACE`, with neither `Idempotency-Key` nor
  `X-Idempotency-Key` present, whatever their value: `Request.isReplayable` tests presence,
  `Header.has`, and with no key a non-idempotent method is never replayable, rewindable body or
  not) is handled at most once: `RoundTrip` takes the client's exclusive
  `reqTicket τ` and its handler receives it. **A replayable request may be handled twice** (a `GET`
  on a reused connection whose response read fails is retried: `persistConn.shouldRetryRequest`,
  `transportReadFromServerError`): its handler receives no ticket. (The old boundary gave every
  handler the ticket, `GET`s included, which a replayed `GET` makes false.) Responses need no
  ticket: `RoundTrip` returns at most one handler run's response, and a body reader is read by its
  one owner.
* **Handler runs borrow their caller's thread tokens** (round 1, F1; the repository's decision
  for grpc's handler pool, `specs-ref/notes/STATUS.md`, "Soundness bugs: grpc.serve's handler
  pool"). `Serve`'s caller gives it a pool of `n` of its own thread tokens (`handlerPool p n`, made
  from `threadToks n`, `handlerPool_alloc`); each handler run draws one for its life and returns it
  at its end. The physical premise: net/http runs at most `n` handlers of one `Serve` at once, a
  bound the adequacy theorem fixes (each handler is a goroutine, so concurrent handlers are live
  threads, which `threadBound` bounds). No token comes from nothing. A handler may panic: `Serve` recovers it and drops the connection (`conn.serve`'s
  deferred `recover`), so a handler's contract is a WP whose result may be a panic.
* **Failures.** Any `RoundTrip`, body read, `Write` may fail at any time (a cancelled request
  context makes them fail); `Flush` returns.

## Vocabulary

Pure: `HReq`, `Proto`, `hdrGet`, `hdrSet`, `canonKey`, `srvKeys`, `hdrView`, `onceOnly`.
Resources: `addrFree a` (exclusive, the environment's), `protoFam a F` (persistent, the run's),
`protoAt a P` (persistent, the current generation's),
`listenerAt l a` (exclusive: a listener bound at `a`), `listenerCloser l` (persistent),
`handlerPool p n` (exclusive), `reqTicket τ` (exclusive),
`reqOwn r R bd` (a client's request being built), `hdrMap hm hs` (an owned header map),
`readerAt rd Pre Φ r` (a body reader having yielded `r`), `respAt resp st hs rd` (a client's
response), `srvReq r R` (a received request, persistent), `respW w R τ P c hs bs` (a handler's
response writer), `muxOwn m L` (a `ServeMux` being built). Bundles (an interface's contract, as
`sync.isLocker`): `roundTripperOk rt`, `handlerOk h P pfx`.

Intended realization: a trusted model of the network (a global ghost map from addresses to saved
protocol families, set once, `addrFree a` the exclusive fragment of `a`'s unset key and `protoFam a
F` the discarded fragment of its set value; `protoAt a P := ∃ F, protoFam a F ∗ ⌜F
hG.goose_localGS = P⌝`; per connection, ghost byte streams of the generation that made it), with
these as its facts; it stays a boundary (net/http is not verified here).

## Specs (this directory)

`Serve`, `Listen` (`net.Listen`), `Listener.Close`, `NewServeMux`, `ServeMux.Handle`, `NewRequest`, `Request.WithContext`, `Header.Set`,
`Header.Get`, `Error`, `Transport.CloseIdleConnections`; the bundles' methods (`RoundTrip`, a body's
`Read`/`Close`, a response writer's `Header`/`WriteHeader`/`Write`/`Flush`) are inside their
bundles. Laws: `reserve`, `protoFam_at`, `protoFam_gen` (second crash pass; repair3-boot's
`protoAt_gen` withdrawn), `addrFree_gen` (repair3-boot), `addrFree_protoAt_excl` (second crash pass,
F-server-boot F5), `handlerPool_alloc`, `reqTicket_alloc`, `reqTicket_excl`,
`mux_handlerOk`, `respW_agree`, `handlerOk_agree`, `handlerOk_narrow`, `NewBuffer_reader`,
`MultiReader_reader`, persistence.
-/
module

public import GeneratedProof.net
public import GeneratedProof.net.http
public import GeneratedProof.net.url
public import SpecPlan.Spec.PkgInit.net.http
public import SpecPlan.Spec.context.Api
public import Perennial.Code.io
public import Perennial.Code.bytes

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Http

open Iris Iris.BI
open Classical

/-! ## Pure model -/

/-- **A request as a client sends it**: method, host (`host:port`), path, headers as set (canonical
keys, in order of first setting). -/
structure HReq where
  meth : GoString
  host : GoString
  path : GoString
  hdr : List (GoString × GoString)

/-- A header byte Go's canonicalization handles (a token byte). -/
def hdrTokenByte (c : w8) : Bool :=
  let n := uint.nat c
  decide ((48 ≤ n ∧ n ≤ 57) ∨ (65 ≤ n ∧ n ≤ 90) ∨ (97 ≤ n ∧ n ≤ 122) ∨
    n ∈ [45, 33, 35, 36, 37, 38, 39, 42, 43, 46, 94, 95, 96, 124, 126])

/-- `textproto`'s canonicalization loop: upper-case the first letter and each after `-`. -/
def canonLoop : Bool → List w8 → List w8
  | _, [] => []
  | up, c :: cs =>
    let n := uint.nat c
    let c' : w8 :=
      if up = true ∧ 97 ≤ n ∧ n ≤ 122 then W8 (n - 32)
      else if up = false ∧ 65 ≤ n ∧ n ≤ 90 then W8 (n + 32) else c
    c' :: canonLoop (decide (n = 45)) cs

/-- **`textproto.CanonicalMIMEHeaderKey`**: a key of token bytes canonicalized, any other as is. -/
def canonKey (k : GoString) : GoString := if k.all hdrTokenByte then canonLoop true k else k

/-- `Header.Set(k, v)` on headers `hs`. -/
def hdrSet (hs : List (GoString × GoString)) (k v : GoString) : List (GoString × GoString) :=
  (hs.filter (fun p => decide (p.1 ≠ canonKey k))) ++ [(canonKey k, v)]

/-- `Header.Get(k)`: the value set at `k`, or `""`. -/
def hdrGet (hs : List (GoString × GoString)) (k : GoString) : GoString :=
  ((hs.find? (fun p => decide (p.1 = canonKey k))).map (·.2)).getD []

/-- The keys Go's server sets itself in a response (their values are Go's, not the handler's). -/
def srvKeys : List GoString :=
  [go!"Date", go!"Content-Type", go!"Content-Length",
   go!"Transfer-Encoding", go!"Connection"]

/-- **What a client sees of committed headers** `hs`: the same value at every other key. -/
def hdrView (hs hc : List (GoString × GoString)) : Prop :=
  ∀ k, canonKey k ∉ srvKeys → hdrGet hc k = hdrGet hs k

/-- **A request Go's client never replays** (`Request.isReplayable` false): not `GET`, `HEAD`,
`OPTIONS`, `TRACE`, and no idempotency key. -/
def onceOnly (R : HReq) : Prop :=
  R.meth ≠ [] ∧ R.meth ∉ [go!"GET", go!"HEAD", go!"OPTIONS", go!"TRACE"] ∧
  ∀ p ∈ R.hdr, p.1 ≠ canonKey go!"Idempotency-Key" ∧ p.1 ≠ canonKey go!"X-Idempotency-Key"

/-- `p` is a path under the mux pattern `pfx` (a pattern ending in `/` routes its subtree, any
other only itself; `ServeMux`'s documented rule, the longest pattern winning). -/
def pathUnder (pfx p : GoString) : Prop :=
  p = pfx ∨ (pfx.getLast? = some (W8 47) ∧ pfx <+: p)

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **An address's protocol** (see the header): persistent knowledge of a request (`hreq`), of its
complete body (`body`), and of a response after the handler wrote `w` (`resp`, prefix-closed in
`w`). Each is used under `□`. -/
structure Proto (GF : BundledGFunctors) where
  hreq : HReq → GName → IProp GF
  bodyPre : HReq → GName → List w8 → IProp GF
  body : HReq → GName → List w8 → IProp GF
  resp : HReq → GName → w64 → List (GoString × GoString) → List w8 → IProp GF

/-- **`P` and `P'` agree on the requests under the mux pattern `pfx`** (a server composing
protocols: the peer port's protocol is rafthttp's under `/raft`). -/
def Proto.agreeUnder (pfx : GoString) (P P' : Proto GF) : Prop :=
  ∀ R, pathUnder pfx R.path →
    P.hreq R = P'.hreq R ∧ P.bodyPre R = P'.bodyPre R ∧ P.body R = P'.body R ∧
      P.resp R = P'.resp R

/-! ## Resources -/

/-- **Address `a` is the program's and not yet reserved** (exclusive; the environment's, one per
address and run). -/
opaque addrFree [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (a : GoString) : IProp GF := iprop(True)

/-- **Address `a`'s protocols, one per local generation, are the family `F`** (persistent; set once
for the run, `reserve`; second crash pass, F-server-boot F3). -/
opaque protoFam [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (a : GoString) (F : GooseLocalGS GF → Proto GF) : IProp GF := iprop(True)

/-- **Address `a` serves the protocol `P` in this generation** (persistent; the current generation's
member of `a`'s family, `protoFam_at`). -/
opaque protoAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (a : GoString) (P : Proto GF) : IProp GF := iprop(True)

/-- **The listener `l`, the socket a bind made, bound at the address string `a`** (exclusive;
`net.Listen`'s, rafthttp's `NewListener`'s; `Serve` takes it). -/
opaque listenerAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (l : GoInterface) (a : GoString) : IProp GF := iprop(True)

/-- **The listener `l` may be closed** from any goroutine (persistent: `Listener.Close`). -/
opaque listenerCloser [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (l : GoInterface) : IProp GF := iprop(True)

/-- **A pool of `n` of the caller's thread tokens lent to `Serve`'s handler runs** (exclusive; see
the header). -/
opaque handlerPool [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : GName) (n : Nat) : IProp GF := iprop(True)

/-- **A request's ticket** (exclusive; a client allocates it, `RoundTrip` of a `onceOnly` request
takes it, the request's handler receives it). -/
opaque reqTicket [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (τ : GName) : IProp GF := iprop(True)

/-- **A request the client is building** (`*http.Request` at `r`): its line and headers `R`, its
header map owned (`Header.Set` on `req.Header`), its body reader `bd` (`nil`: none). Exclusive. -/
opaque reqOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) (R : HReq) (bd : GoInterface) : IProp GF := iprop(True)

/-- **An owned header map** `hm` (an `http.Header`) holding `hs`. Exclusive. -/
opaque hdrMap [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (hm : GoMap) (hs : List (GoString × GoString)) : IProp GF := iprop(True)

/-- **A read-only header map** `hm` holding `hs` (a received request's, a client's response's, a
sent request's). Persistent. -/
opaque hdrRO [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (hm : GoMap) (hs : List (GoString × GoString)) : IProp GF := iprop(True)

/-- **A sent request** `r` (after `RoundTrip`), read-only: its line and headers `R` (`r.URL`,
`r.Header` readable for good; Go's `RoundTrip` does not modify it). Persistent. -/
opaque reqRO [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) (R : HReq) : IProp GF := iprop(True)

/-- **A body reader** `rd` (an `io.ReadCloser`) that has yielded `r`: every prefix it yields meets
`Pre` (persistent knowledge), and a complete stream (ended by `EOF`) meets `Φ`. Exclusive. Its
contract (`Read`, `Close`) is `readerAt_read.spec`, `readerAt_close.spec`. -/
opaque readerAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (rd : GoInterface) (Pre Φ : List w8 → IProp GF) (r : List w8) : IProp GF :=
  iprop(True)

/-- **A body reader may be closed from another goroutine** (persistent; Go's response bodies
support a `Close` concurrent with a `Read`, which then fails). -/
opaque readerCloser [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (rd : GoInterface) : IProp GF := iprop(True)

/-- **`w` reads through `rd`** (persistent; integration I3, 4b's request): every `Read(p)` of `w` is
one `Read` of `rd` on a prefix of `p` (`p[:k]`, `k ≤ len(p)`), returning its result (`n`, `err`).
Introduced by the wrappers' owners (4b's `IoUtil.NewLimitedBufferReader.spec`,
`IoUtil.ReaderAndCloser_reader`). -/
opaque readsThrough [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (w rd : GoInterface) : IProp GF := iprop(True)

/-- **`w` closes through `rd`** (persistent): `w`'s `Close()` is `rd`'s. -/
opaque closesThrough [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (w rd : GoInterface) : IProp GF := iprop(True)

/-- **A client's response** `*http.Response` at `resp`: status `st`, headers `hc` (readable for
good), body `rd`. Persistent (the fields are never written by the client). -/
opaque respAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (resp : Loc) (st : w64) (hc : List (GoString × GoString)) (rd : GoInterface) :
    IProp GF := iprop(True)

/-- **A received request** `*http.Request` at `r` (persistent, read-only): line and headers `R`,
body `rd`, `RemoteAddr` some string. -/
opaque srvReq [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) (R : HReq) (rd : GoInterface) : IProp GF := iprop(True)

/-- **A handler's response writer** `w` for request `R` (ticket name `τ`) of protocol `P`: committed
(`c = some st`) or not, its header map `hs` (owned until the commit: `w.Header()`), the bytes `bs`
written. Exclusive; it may be passed to another goroutine (the stream handler's writer goroutine),
and must be given back before the handler returns. -/
opaque respW [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (w : GoInterface) (R : HReq) (τ : GName) (P : Proto GF) (c : Option w64)
    (hs : List (GoString × GoString)) (bs : List w8) : IProp GF := iprop(True)

/-- **A `ServeMux` being built** (exclusive): its patterns and handlers so far. -/
opaque muxOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (m : Loc) (L : List (GoString × GoInterface)) : IProp GF := iprop(True)

/-- **A `ServeMux` built** (persistent): its patterns and handlers, fixed. -/
opaque muxAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (m : Loc) (L : List (GoString × GoInterface)) : IProp GF := iprop(True)

/-- `io.EOF`'s value. -/
def ioEOF (e : GoInterface) : IProp GF := iprop(globalAddr _root_.Perennial.io.EOF ↦□ e)

/-- **An error a client may log or wrap**: `nil`, or one whose `Error()` returns and whose
`Unwrap`/`Is`/`As` chain is well-formed (net/http's and the standard library's errors). Persistent.
-/
opaque errOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (e : GoInterface) : IProp GF := iprop(True)

/-! ## Bundles -/

/-- **A body's prefix knowledge for a response**: the bytes read so far are a prefix of bytes the
handler wrote with the protocol's knowledge. -/
def respPre (P : Proto GF) (R : HReq) (τ : GName) (st : w64) (hs : List (GoString × GoString))
    (r : List w8) : IProp GF :=
  iprop(∃ w, ⌜r <+: w⌝ ∗ □ P.resp R τ st hs w)

/-- **A `RoundTripper`** (`rt`, persistent; rafthttp's from `transport.NewTimeoutTransport`).
`RoundTrip(r)` of a request built for `R` (body `bd` with its reader contract, or none) to an
address `R.host` serving `P`, with the client's knowledge under its name `τ`, and the ticket if the
request is `onceOnly`: an error (the ticket lost), or the response of one handler run of the
request: the status it set, the headers it committed (`hdrView`), its body (prefixes of what that
handler wrote, with the protocol's knowledge). The request is given back read-only (`reqRO`: Go's
`RoundTrip` does not modify it; its body is the transport's, which closes it). -/
def roundTripperOk (rt : GoInterface) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜rt = interface.ok i⌝ ∗
    □ ∀ (r : Loc) (R : HReq) (bd : GoInterface) (τ : GName) (P : Proto GF)
        (Preb Φb : List w8 → IProp GF) (Ψ : val → IProp GF),
      reqOwn r R bd -∗ protoAt R.host P -∗ □ P.hreq R τ -∗
      (if bd = interface.nil then iprop(□ P.body R τ [])
       else iprop(readerAt bd Preb Φb [] ∗ □ (∀ B, Preb B -∗ P.bodyPre R τ B) ∗
         □ (∀ B, Φb B -∗ P.body R τ B))) -∗
      (if onceOnly R then reqTicket τ else iprop(True)) -∗
      ▷ (∀ (resp : Loc) (err : GoInterface),
          reqRO r R ∗ ((⌜err ≠ interface.nil⌝ ∗ errOk err) ∨
           (⌜err = interface.nil⌝ ∗ ∃ (st : w64) (hs hc : List (GoString × GoString))
              (rd : GoInterface),
              ⌜hdrView hs hc⌝ ∗ respAt resp st hc rd ∗ readerCloser rd ∗
              readerAt rd (respPre P R τ st hs) (fun _ => iprop(True)) [])) -∗
          Ψ (PairV #resp #err)) -∗
      WP (App (Val #(methods i.ty go!"RoundTrip" i.v)) (Val #r)) {{ Ψ }})

/-- **What a handler run gets** (`ServeHTTP(w, r)`): a received request under `pfx` with the
client's knowledge, its ticket if `onceOnly`, its body reader carrying the body knowledge at `EOF`,
a fresh response writer (an `http.Flusher`: Go's are), and its goroutine's thread token. -/
def servePre (P : Proto GF) (pfx : GoString) (w : GoInterface) (r : Loc) (R : HReq) (τ : GName)
    (rd : GoInterface) : IProp GF :=
  iprop(⌜pathUnder pfx R.path⌝ ∗ srvReq r R rd ∗ □ P.hreq R τ ∗
    (if onceOnly R then reqTicket τ else iprop(True)) ∗
    readerAt rd (fun B => iprop(□ P.bodyPre R τ B)) (fun B => iprop(□ P.body R τ B)) [] ∗
    respW w R τ P none [] [] ∗ threadTok)

/-- **What a handler run gives back**: the token and the writer, committed, or a panic (`Serve`
recovers it and drops the connection). -/
def serveDone (P : Proto GF) (w : GoInterface) (R : HReq) (τ : GName) (v : val) : IProp GF :=
  iprop(threadTok ∗ ((∃ st hs bs, respW w R τ P (some st) hs bs) ∨
    (⌜v.isPanic = true⌝ ∗ ∃ c hs bs, respW w R τ P c hs bs)))

/-- **A handler serving the requests under the mux pattern `pfx` with protocol `P`** (persistent):
`ServeHTTP` of every run `servePre` describes ends in `serveDone`. -/
def handlerOk (h : GoInterface) (P : Proto GF) (pfx : GoString) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜h = interface.ok i⌝ ∗
    □ ∀ (w : GoInterface) (r : Loc) (R : HReq) (τ : GName) (rd : GoInterface),
      servePre P pfx w r R τ rd -∗
      WP (App (App (Val #(methods i.ty go!"ServeHTTP" i.v)) (Val #w)) (Val #r))
        {{ v, serveDone P w R τ v }})

/-- **An address string with port `0`** (pure, opaque: `net.SplitHostPort`'s port is `0`). -/
opaque portZero (a : GoString) : Prop := False

/-- **A URL `NewRequest` accepts** with any path (pure, opaque): one `url.Parse` returned (a peer
URL from `types.NewURLs`), so its `String()` parses again. -/
opaque urlOk (u : _root_.Perennial.net.url.URL) : Prop := True

/-- **`u.String()`** (pure, opaque: `url.URL.String`'s result). -/
opaque urlStr (u : _root_.Perennial.net.url.URL) : GoString := []

end vocab

/-! ## Laws (assumed) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

def persistent.spec : Prop :=
  (∀ a P, Persistent (protoAt (GF := GF) a P)) ∧
  (∀ a F, Persistent (protoFam (GF := GF) a F)) ∧
  (∀ rd, Persistent (readerCloser (GF := GF) rd)) ∧
  (∀ resp st hc rd, Persistent (respAt (GF := GF) resp st hc rd)) ∧
  (∀ r R rd, Persistent (srvReq (GF := GF) r R rd)) ∧
  (∀ m L, Persistent (muxAt (GF := GF) m L)) ∧
  (∀ l, Persistent (listenerCloser (GF := GF) l)) ∧
  (∀ e, Persistent (errOk (GF := GF) e)) ∧
  (∀ hm hs, Persistent (hdrRO (GF := GF) hm hs)) ∧
  (∀ r R, Persistent (reqRO (GF := GF) r R)) ∧
  (∀ rt, Persistent (roundTripperOk (GF := GF) rt)) ∧
  (∀ h P pfx, Persistent (handlerOk (GF := GF) h P pfx))

/-- **Reserve an address** for a family of protocols, one per generation, once for the run (before
or after its bind). Changes (second crash pass, F-server-boot F3): reserves a family (`protoFam`), was
one protocol (`protoAt a P`, now `protoFam_at` of a constant family `fun _ => P`). -/
def reserve.spec : Prop :=
  ∀ (a : GoString) (F : GooseLocalGS GF → Proto GF), addrFree (GF := GF) a ⊢ |==> protoFam a F

/-- **The current generation's protocol of a reserved address** (second crash pass, F-server-boot
F3): the family's member at this heap's local generation. -/
def protoFam_at.spec : Prop := ∀ (a : GoString) (F : GooseLocalGS GF → Proto GF),
  protoFam (GF := GF) a F ⊢ protoAt a (F hG.goose_localGS)

/-- **An address's reservation is the run's, not a generation's** (repair3-boot; second crash pass:
of the family, F-server-boot F3): the family reserved before a crash is the address's after it, and
an address left free stays free (`addrFree_gen`). Realization: the intended model's global ghost map
from addresses to saved families (the header) is in `GooseGlobalGS`; `F` is a value, the same on both
sides. Repair3-boot's `protoAt_gen` (one protocol for the run) is withdrawn: the protocol is the
generation's (the header, "Generations"). -/
def protoFam_gen.spec : Prop := ∀ (L' : GooseLocalGS GF) (a : GoString) (F : GooseLocalGS GF → Proto GF),
  protoFam (GF := GF) a F ⊣⊢ protoFam (hG := ⟨hG.goose_globalGS, L'⟩) a F

/-- **A reserved address is not free** (second crash pass, F-server-boot F5: what lets a client keep
its own map over reserved addresses, 2e's `srvEp`). True of the model: `addrFree a` is the exclusive
fragment of `a`'s unset key in the set-once map, and `protoAt a P` (at any generation) exists only
once `reserve` has set the key, consuming that fragment; the environment issues `addrFree a` at most
once per address and run (the header's physical premise). Realization: the map's fragments, `a ↪{1}
unset` against `a ↪□ F` (`ghost_map_elem_valid_2`: the fractions `1` and discarded do not combine), a
plain entailment. -/
def addrFree_protoAt_excl.spec : Prop := ∀ (a : GoString) (P : Proto GF),
  addrFree (GF := GF) a ∗ protoAt a P ⊢ iprop(False)

def addrFree_gen.spec : Prop := ∀ (L' : GooseLocalGS GF) (a : GoString),
  addrFree (GF := GF) a ⊣⊢ addrFree (hG := ⟨hG.goose_globalGS, L'⟩) a

/-- **A pool of the caller's thread tokens** for a `Serve`'s handler runs (see the header). -/
def handlerPool_alloc.spec : Prop :=
  ∀ (n : Nat), threadToks (GF := GF) n ⊢ |==> ∃ p, handlerPool p n

def reqTicket_alloc.spec : Prop := ⊢ |==> ∃ τ, reqTicket (GF := GF) τ

def reqTicket_excl.spec : Prop := ∀ τ, reqTicket (GF := GF) τ ∗ reqTicket τ ⊢ iprop(False)

def errOk_nil.spec : Prop := ⊢ errOk (GF := GF) interface.nil

/-- **A body's `Read(p)`**: `n` bytes `ys` into `p`'s first `n`, every prefix yielded meeting
`Pre`; `EOF` only at a complete stream, meeting `Φ`; any other error at any time. -/
def readerAt_read.spec : Prop :=
  ∀ (rd : GoInterface) (i : GoInterfaceOk) (Pre Φ : List w8 → IProp GF) (r : List w8)
    (p : GoSlice) (xs : List w8) (e : GoInterface),
  rd = interface.ok i →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ readerAt rd Pre Φ r ∗ p ↦* xs ∗ ioEOF e }}
    (App (Val #(methods i.ty go!"Read" i.v)) (Val #p))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ ys : List w8, ⌜ys.length = uint.nat n ∧ ys.length ≤ xs.length⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ readerAt rd Pre Φ (r ++ ys) ∗ □ Pre (r ++ ys) ∗
        (⌜err = e⌝ -∗ □ Φ (r ++ ys)) ∗ errOk err }}

/-- **A body's `Close()`** (at most once by its owner, or through `readerCloser` from another
goroutine): returns some error. -/
def readerAt_close.spec : Prop :=
  ∀ (rd : GoInterface) (i : GoInterfaceOk),
  rd = interface.ok i →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ readerCloser rd }}
    (App (Val #(methods i.ty go!"Close" i.v)) (Val #()))
  {{ (err : GoInterface), RET #err; errOk err }}

/-- **A response writer's `Header()`** before the commit: the header map, lent until the commit
(`hdrMap` given back by `respW_hdr_return`); after it, a map whose writes are ignored. -/
def respW_header.spec : Prop :=
  ∀ (w : GoInterface) (i : GoInterfaceOk) R τ (P : Proto GF) c hs bs,
  w = interface.ok i →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ respW w R τ P c hs bs }}
    (App (Val #(methods i.ty go!"Header" i.v)) (Val #()))
  {{ (hm : GoMap), RET #hm;
      (⌜c = none⌝ ∗ hdrMap hm hs ∗
        (∀ hs', hdrMap hm hs' -∗ respW w R τ P none hs' bs)) ∨
      (⌜c ≠ none⌝ ∗ respW w R τ P c hs bs ∗ ∃ hs', hdrMap hm hs') }}

/-- **`WriteHeader(st)`** (`200 ≤ st ≤ 999`: Go panics outside `100`-`999` and does not commit a
`1xx`): commits `st` with the headers set, if the protocol allows it; a second call is ignored. -/
def respW_writeHeader.spec : Prop :=
  ∀ (w : GoInterface) (i : GoInterfaceOk) R τ (P : Proto GF) c hs bs (st : w64),
  w = interface.ok i → 200 ≤ uint.nat st → uint.nat st ≤ 999 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ respW w R τ P c hs bs ∗
      (⌜c = none⌝ -∗ □ P.resp R τ st hs []) }}
    (App (Val #(methods i.ty go!"WriteHeader" i.v)) (Val #st))
  {{ RET #(); respW w R τ P (some (c.getD st)) hs bs }}

/-- **`Write(b)`** (committing `200` first if uncommitted): the protocol must allow the bytes;
writes a prefix `n` of `b`, all unless it fails. -/
def respW_write.spec : Prop :=
  ∀ (w : GoInterface) (i : GoInterfaceOk) R τ (P : Proto GF) c hs bs (b : GoSlice) (ys : List w8)
    (dq : DFrac),
  w = interface.ok i →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ respW w R τ P c hs bs ∗ b ↦*{dq} ys ∗
      □ P.resp R τ (c.getD (W64 200)) hs (bs ++ ys) }}
    (App (Val #(methods i.ty go!"Write" i.v)) (Val #b))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      b ↦*{dq} ys ∗ ⌜uint.nat n ≤ ys.length ∧ (err = interface.nil → uint.nat n = ys.length)⌝ ∗
      respW w R τ P (some (c.getD (W64 200))) hs (bs ++ ys.take (uint.nat n)) ∗ errOk err }}

/-- **`w.(http.Flusher).Flush()`** on a handler's writer: returns (commits `200` if uncommitted,
which the protocol must allow). -/
def respW_flush.spec : Prop :=
  ∀ (w : GoInterface) (i : GoInterfaceOk) R τ (P : Proto GF) c hs bs,
  w = interface.ok i →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ respW w R τ P c hs bs ∗
      (⌜c = none⌝ -∗ □ P.resp R τ (W64 200) hs []) }}
    (App (Val #(methods i.ty go!"Flush" i.v)) (Val #()))
  {{ RET #(); respW w R τ P (some (c.getD (W64 200))) hs bs }}

/-- A handler's writer is an `http.Flusher` (Go's `*response` is: the type assertion in rafthttp's
handlers succeeds). -/
def respW_flusher.spec : Prop :=
  ∀ (w : GoInterface) R τ (P : Proto GF) c hs bs,
  respW (GF := GF) w R τ P c hs bs ⊢ ∃ i : GoInterfaceOk, ⌜w = interface.ok i ∧
    go.typeSetContains i.ty _root_.Perennial.net.http.Flusher.ty = true⌝

/-- **A mux is built** once its patterns are registered (no `Handle` after it is served). -/
def muxOwn_freeze.spec : Prop :=
  ∀ (m : Loc) (L : List (GoString × GoInterface)), muxOwn (GF := GF) m L ⊢ |==> muxAt m L

/-- **A request being built: its `Header` field** (a load of `r.Header` reads `hm`, whose `Set`s
update the request's headers). -/
def reqOwn_header.spec : Prop :=
  ∀ (r : Loc) (R : HReq) (bd : GoInterface),
    reqOwn (GF := GF) r R bd ⊢ ∃ hm : GoMap,
      structFieldRef _root_.Perennial.net.http.Request go!"Header" r ↦□ hm ∗ hdrMap hm R.hdr ∗
      (∀ hs, hdrMap hm hs -∗ reqOwn r { R with hdr := hs } bd)

/-- **A received request's fields**, read-only: `Method`, `URL` (its `Path`), `Header`, `Body`. -/
def srvReq_fields.spec : Prop :=
  ∀ (r : Loc) (R : HReq) (rd : GoInterface),
    srvReq (GF := GF) r R rd ⊢
      structFieldRef _root_.Perennial.net.http.Request go!"Method" r ↦□ R.meth ∗
      (∃ u : Loc, structFieldRef _root_.Perennial.net.http.Request go!"URL" r ↦□ u ∗
        structFieldRef _root_.Perennial.net.url.URL go!"Path" u ↦□ R.path) ∗
      (∃ hm : GoMap, structFieldRef _root_.Perennial.net.http.Request go!"Header" r ↦□ hm ∗
        hdrRO hm R.hdr) ∗
      structFieldRef _root_.Perennial.net.http.Request go!"Body" r ↦□ rd ∗
      (∃ a : GoString, structFieldRef _root_.Perennial.net.http.Request go!"RemoteAddr" r ↦□ a)

/-- **A client's response's fields**, read-only: `StatusCode`, `Header`, `Body`. -/
def respAt_fields.spec : Prop :=
  ∀ (resp : Loc) (st : w64) hc (rd : GoInterface),
    respAt (GF := GF) resp st hc rd ⊢
      structFieldRef _root_.Perennial.net.http.Response go!"StatusCode" resp ↦□ st ∗
      (∃ hm : GoMap, structFieldRef _root_.Perennial.net.http.Response go!"Header" resp ↦□ hm ∗
        hdrRO hm hc) ∗
      structFieldRef _root_.Perennial.net.http.Response go!"Body" resp ↦□ rd

/-- **A sent request's `URL` and `Header`**, read-only. -/
def reqRO_fields.spec : Prop :=
  ∀ (r : Loc) (R : HReq),
    reqRO (GF := GF) r R ⊢
      (∃ u : Loc, structFieldRef _root_.Perennial.net.http.Request go!"URL" r ↦□ u) ∗
      (∃ hm : GoMap, structFieldRef _root_.Perennial.net.http.Request go!"Header" r ↦□ hm ∗
        hdrRO hm R.hdr)

/-- **A response writer depends on its protocol only through the request's responses**. -/
def respW_agree.spec : Prop :=
  ∀ (w : GoInterface) (R : HReq) τ (P P' : Proto GF) c hs bs, P.resp R = P'.resp R →
    respW (GF := GF) w R τ P c hs bs ⊣⊢ respW w R τ P' c hs bs

/-- **A handler serves every protocol agreeing with its own under its pattern** (a mux of the
peer port composes rafthttp's protocol with the other endpoints'). -/
def handlerOk_agree.spec : Prop :=
  ∀ (h : GoInterface) (P P' : Proto GF) (pfx : GoString), Proto.agreeUnder pfx P P' →
    handlerOk (GF := GF) h P pfx ⊢ handlerOk h P' pfx

/-- **A handler of a pattern serves the narrower patterns under it.** -/
def handlerOk_narrow.spec : Prop :=
  ∀ (h : GoInterface) (P : Proto GF) (pfx pfx' : GoString),
    (∀ p, pathUnder pfx' p → pathUnder pfx p) →
    handlerOk (GF := GF) h P pfx ⊢ handlerOk h P pfx'

/-- **`bytes.NewBuffer(b)` as a request body**: a reader whose every prefix is one of `ys` and
whose complete stream is `ys` (it takes the slice). -/
def NewBuffer_reader.spec : Prop :=
  ∀ (b : GoSlice) (ys : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ b ↦* ys }}
    (App (Val (@! _root_.Perennial.bytes.NewBuffer)) (Val #b))
  {{ (bf : Loc), RET #bf;
      readerAt (interface.mkOk (go.GoType.PointerType _root_.Perennial.bytes.Buffer.ty) #bf)
        (fun B => iprop(⌜B <+: ys⌝)) (fun B => iprop(⌜B = ys⌝)) [] }}

/-- **`io.MultiReader(r1, r2)`** of two readers read from their start: prefixes of `r1`'s, then
`r1`'s complete stream followed by `r2`'s prefixes; complete when both are (etcd's
`ioutil.ReaderAndCloser` over it keeps the contract: its `Read` is the reader's). -/
def MultiReader_reader.spec : Prop :=
  ∀ (r1 r2 : GoInterface) (Pre1 Φ1 Pre2 Φ2 : List w8 → IProp GF) (sl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ sl ↦* [r1, r2] ∗
      readerAt r1 Pre1 Φ1 [] ∗ readerAt r2 Pre2 Φ2 [] }}
    (App (Val (@! _root_.Perennial.io.MultiReader)) (Val #sl))
  {{ (mr : GoInterface), RET #mr;
      readerAt mr
        (fun B => iprop(Pre1 B ∨ ∃ B1 B2, ⌜B = B1 ++ B2⌝ ∗ Φ1 B1 ∗ Pre2 B2))
        (fun B => iprop(∃ B1 B2, ⌜B = B1 ++ B2⌝ ∗ Φ1 B1 ∗ Φ2 B2)) [] }}

/-- **A built mux serves its patterns' handlers** (`ServeMux.ServeHTTP`): a request under `pfx` is
routed to the handler of the longest pattern under which its path is, or answered `404`/`301` by
the mux, which the protocol must allow for a path no pattern routes. -/
def mux_handlerOk.spec : Prop :=
  ∀ (m : Loc) (L : List (GoString × GoInterface)) (P : Proto GF) (pfx : GoString),
    (∀ (R : HReq) τ, pathUnder pfx R.path → (∀ pat h, (pat, h) ∈ L → ¬ pathUnder pat R.path) →
      (⊢ □ P.resp R τ (W64 404) [] []) ∧ (⊢ □ P.resp R τ (W64 301) [] [])) →
    muxAt (GF := GF) m L ∗ ([∗list] ph ∈ L, handlerOk ph.2 P ph.1) ⊢
      handlerOk (interface.mkOk (go.GoType.PointerType _root_.Perennial.net.http.ServeMux.ty) #m)
        P pfx

/-- **A wrapper of a body reader is a body reader** with the same knowledge (integration I3, 4b's
request `req/net_http.md`, "from 4b, round 1", item 1): `readerAt_read` of `w` is `readerAt_read` of
`rd` on a prefix of the buffer. -/
def readerAt_wrap.spec : Prop := ∀ (w rd : GoInterface) (Pre Φ : List w8 → IProp GF) (r : List w8),
  readerAt (GF := GF) rd Pre Φ r ∗ readsThrough w rd ⊢ readerAt w Pre Φ r

/-- A wrapper closing through a reader that may be closed concurrently may be too. -/
def readerCloser_wrap.spec : Prop := ∀ (w rd : GoInterface),
  readerCloser (GF := GF) rd ∗ closesThrough w rd ⊢ readerCloser w

def wrap_persistent.spec : Prop :=
  (∀ w rd, Persistent (readsThrough (GF := GF) w rd)) ∧ (∀ w rd, Persistent (closesThrough (GF := GF) w rd))

end laws

end Http
end EtcdGrove
end Perennial
