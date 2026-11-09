/-
# net/http over TCP: the HTTP boundary (batch 2f, for rafthttp): a trust boundary

`net/http` is translated names-only: every statement here and in this directory is **assumed**.
They restate the boundary the user reviewed for rafthttp (`specs-ref/notes/rafthttp-http-boundary.md`,
2026-10-22; D38b, D42 and stage 5e's header model, `specs-ref/notes/rafthttp-plan.md`), over opaque
predicates, with one correction (below, "Tickets"). Why each is true of Go's `net/http` over TCP is
said where it is stated.

## The model

* **Requests as sent** (`HReq`): method, host (the `host:port` of the URL), path, headers (as set).
  The body is a reader the client hands to `NewRequest` (or none).
* **An address's protocol** (`Proto`): what the program's clients may send to that address and
  what its server may answer. `hreq R τ` (persistent knowledge of a request's line and headers,
  under the client's chosen ghost name `τ`), `body R τ B` (of its complete body `B`), and
  `resp R τ st hs w` (of a response with status `st`, committed headers `hs`, after the handler
  wrote the bytes `w`; prefix-closed in `w`, an obligation of whoever defines a protocol). All are
  used under `□`: only **persistent** knowledge crosses the wire.
* **The closed world** (the user's decision 1, 2026-10-22). An address is reserved once, with its
  protocol (`reserve`: the environment's `addrFree a`, one per address and run, becomes the
  persistent `protoAt a Π` and the right to serve it, `protoOwn a Π`). Every request a server of the
  program receives at `a` was sent by a client of the program through `RoundTrip` to `a`, with the
  bytes that client sent; so the handler gets the facts the client proved. (The physical fact: the
  program's peer addresses are its own, and only its members connect to them.)
* **Bodies are prefixes** (D42). A body reader yields successive pieces whose concatenation is a
  prefix of what the sender's side produced (the client's body reader; the handler's writes);
  `EOF` only at the end of a complete stream (HTTP/1.1 framing, chunked or with a length, makes a
  truncated body an `ErrUnexpectedEOF` or another error, never `EOF`); an error at any time.
* **The response's status and headers are the handler's** (decisions 2 and 4): the status it set,
  and its committed headers but for the keys Go's server sets itself (`srvKeys`).
* **Tickets** (D38b, corrected here). A request that Go's client never replays (`onceOnly`: a
  method other than `GET`, `HEAD`, `OPTIONS`, `TRACE` and no `Idempotency-Key` header:
  `Request.isReplayable`) is handled at most once: `RoundTrip` takes the client's exclusive
  `reqTicket τ` and its handler receives it. **A replayable request may be handled twice** (a `GET`
  on a reused connection whose response read fails is retried: `persistConn.shouldRetryRequest`,
  `transportReadFromServerError`): its handler receives no ticket. (The old boundary gave every
  handler the ticket, `GET`s included, which a replayed `GET` makes false.) Responses need no
  ticket: `RoundTrip` returns at most one handler run's response, and a body reader is read by its
  one owner.
* **Handlers run on Serve's goroutines.** `Serve`'s trusted model is an accept loop that forks a
  goroutine per connection (as Go's `srv.Serve` does: `go c.serve(ctx)`), so each handler run holds
  that goroutine's thread token, from the thread fuel like any `go` statement's; it never comes from
  nothing. A handler may panic: `Serve` recovers it and drops the connection (`conn.serve`'s
  deferred `recover`), so a handler's contract is a WP whose result may be a panic.
* **Failures.** Any `RoundTrip`, body read, `Write` may fail at any time (a cancelled request
  context makes them fail); `Flush` returns.

## Vocabulary

Pure: `HReq`, `Proto`, `hdrGet`, `hdrSet`, `canonKey`, `srvKeys`, `hdrView`, `onceOnly`.
Resources: `addrFree a` (exclusive, the environment's), `protoAt a Π` (persistent), `protoOwn a Π`
(exclusive), `listenerAt l a` (exclusive: a listener bound at `a`), `reqTicket τ` (exclusive),
`reqOwn r R bd` (a client's request being built), `hdrMap hm hs` (an owned header map),
`readerAt rd Pre Φ r` (a body reader having yielded `r`), `respAt resp st hs rd` (a client's
response), `srvReq r R` (a received request, persistent), `respW w R τ Π c hs bs` (a handler's
response writer), `muxOwn m L` (a `ServeMux` being built). Bundles (an interface's contract, as
`sync.isLocker`): `roundTripperOk rt`, `handlerOk h Π pfx`.

Intended realization: a trusted model of the network (a global ghost map from addresses to saved
protocols, set once; per connection, ghost byte streams), with these as its facts; it stays a
boundary (net/http is not verified here).

## Specs (this directory)

`Serve`, `NewServeMux`, `ServeMux.Handle`, `NewRequest`, `Request.WithContext`, `Header.Set`,
`Header.Get`, `Error`, `Transport.CloseIdleConnections`; the bundles' methods (`RoundTrip`, a body's
`Read`/`Close`, a response writer's `Header`/`WriteHeader`/`Write`/`Flush`) are inside their
bundles. Laws: `reserve`, `protoAt_agree`, `reqTicket_alloc`, `reqTicket_excl`, `mux_handlerOk`,
persistence.
-/
module

public import GeneratedProof.net.http
public import GeneratedProof.net.url
public import Spec.PkgInit.net.http
public import Spec.context.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Http

open Iris Iris.BI

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
  R.meth ∉ [go!"GET", go!"HEAD", go!"OPTIONS",
    go!"TRACE"] ∧
  hdrGet R.hdr go!"Idempotency-Key" = [] ∧
  hdrGet R.hdr go!"X-Idempotency-Key" = []

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
  body : HReq → GName → List w8 → IProp GF
  resp : HReq → GName → w64 → List (GoString × GoString) → List w8 → IProp GF

/-- **`Π` and `Π'` agree on the requests under the mux pattern `pfx`** (a server composing
protocols: the peer port's protocol is rafthttp's under `/raft`). -/
def Proto.agreeUnder (pfx : GoString) (Π Π' : Proto GF) : Prop :=
  ∀ R, pathUnder pfx R.path →
    Π.hreq R = Π'.hreq R ∧ Π.body R = Π'.body R ∧ Π.resp R = Π'.resp R

/-! ## Resources -/

/-- **Address `a` is the program's and not yet reserved** (exclusive; the environment's, one per
address and run). -/
opaque addrFree (a : GoString) : IProp GF := iprop(True)

/-- **Address `a` serves the protocol `Π`** (persistent; set once, `reserve`). -/
opaque protoAt (a : GoString) (Π : Proto GF) : IProp GF := iprop(True)

/-- **The right to serve `a` with `Π`** (exclusive; `Serve` takes it with `a`'s listener). -/
opaque protoOwn (a : GoString) (Π : Proto GF) : IProp GF := iprop(True)

/-- **The listener `l` bound at `a`** (exclusive; `net.Listen`'s, through rafthttp's `NewListener`
or embed's). -/
opaque listenerAt (l : GoInterface) (a : GoString) : IProp GF := iprop(True)

/-- **A request's ticket** (exclusive; a client allocates it, `RoundTrip` of a `onceOnly` request
takes it, the request's handler receives it). -/
opaque reqTicket (τ : GName) : IProp GF := iprop(True)

/-- **A request the client is building** (`*http.Request` at `r`): its line and headers `R`, its
header map owned (`Header.Set` on `req.Header`), its body reader `bd` (`nil`: none). Exclusive. -/
opaque reqOwn (r : Loc) (R : HReq) (bd : GoInterface) : IProp GF := iprop(True)

/-- **An owned header map** `hm` (an `http.Header`) holding `hs`. Exclusive. -/
opaque hdrMap (hm : GoInterface) (hs : List (GoString × GoString)) : IProp GF := iprop(True)

/-- **A body reader** `rd` (an `io.ReadCloser`) that has yielded `r`: every prefix it yields meets
`Pre` (persistent knowledge), and a complete stream (ended by `EOF`) meets `Φ`. Exclusive. Its
contract (`Read`, `Close`) is `readerAt_read.spec`, `readerAt_close.spec`. -/
opaque readerAt (rd : GoInterface) (Pre Φ : List w8 → IProp GF) (r : List w8) : IProp GF :=
  iprop(True)

/-- **A body reader may be closed from another goroutine** (persistent; Go's response bodies
support a `Close` concurrent with a `Read`, which then fails). -/
opaque readerCloser (rd : GoInterface) : IProp GF := iprop(True)

/-- **A client's response** `*http.Response` at `resp`: status `st`, headers `hc` (readable for
good), body `rd`. Persistent (the fields are never written by the client). -/
opaque respAt (resp : Loc) (st : w64) (hc : List (GoString × GoString)) (rd : GoInterface) :
    IProp GF := iprop(True)

/-- **A received request** `*http.Request` at `r` (persistent, read-only): line and headers `R`,
body `rd`, `RemoteAddr` some string. -/
opaque srvReq (r : Loc) (R : HReq) (rd : GoInterface) : IProp GF := iprop(True)

/-- **A handler's response writer** `w` for request `R` (ticket name `τ`) of protocol `Π`: committed
(`c = some st`) or not, its header map `hs` (owned until the commit: `w.Header()`), the bytes `bs`
written. Exclusive; it may be passed to another goroutine (the stream handler's writer goroutine),
and must be given back before the handler returns. -/
opaque respW (w : GoInterface) (R : HReq) (τ : GName) (Π : Proto GF) (c : Option w64)
    (hs : List (GoString × GoString)) (bs : List w8) : IProp GF := iprop(True)

/-- **A `ServeMux` being built** (exclusive): its patterns and handlers so far. -/
opaque muxOwn (m : Loc) (L : List (GoString × GoInterface)) : IProp GF := iprop(True)

/-- **A `ServeMux` built** (persistent): its patterns and handlers, fixed. -/
opaque muxAt (m : Loc) (L : List (GoString × GoInterface)) : IProp GF := iprop(True)

/-- `io.EOF`'s value. -/
def ioEOF (e : GoInterface) : IProp GF := iprop(globalAddr _root_.Perennial.io.EOF ↦□ e)

/-- **An error a client may log or wrap**: `nil`, or one whose `Error()` returns and whose
`Unwrap`/`Is`/`As` chain is well-formed (net/http's and the standard library's errors). Persistent.
-/
opaque errOk (e : GoInterface) : IProp GF := iprop(True)

/-! ## Bundles -/

/-- **A body's prefix knowledge for a response**: the bytes read so far are a prefix of bytes the
handler wrote with the protocol's knowledge. -/
def respPre (Π : Proto GF) (R : HReq) (τ : GName) (st : w64) (hs : List (GoString × GoString))
    (r : List w8) : IProp GF :=
  iprop(∃ w, ⌜r <+: w⌝ ∗ □ Π.resp R τ st hs w)

/-- **A `RoundTripper`** (`rt`, persistent; rafthttp's from `transport.NewTimeoutTransport`).
`RoundTrip(r)` of a request built for `R` (body `bd` with its reader contract, or none) to an
address `R.host` serving `Π`, with the client's knowledge under its name `τ`, and the ticket if the
request is `onceOnly`: an error (the ticket lost), or the response of one handler run of the
request: the status it set, the headers it committed (`hdrView`), its body (prefixes of what that
handler wrote, with the protocol's knowledge). The request's memory is the transport's for good
(Go: "RoundTrip must always close the body"; the request may be read until the response body is
closed). -/
def roundTripperOk (rt : GoInterface) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜rt = interface.ok i⌝ ∗
    □ ∀ (r : Loc) (R : HReq) (bd : GoInterface) (τ : GName) (Π : Proto GF)
        (Φb : List w8 → IProp GF) (Ψ : val → IProp GF),
      reqOwn r R bd -∗ protoAt R.host Π -∗ □ Π.hreq R τ -∗
      (if bd = interface.nil then □ Π.body R τ []
       else iprop(readerAt bd (fun _ => True) Φb [] ∗ □ (∀ B, Φb B -∗ Π.body R τ B))) -∗
      (if decide (onceOnly R) then reqTicket τ else iprop(True)) -∗
      ▷ (∀ (resp : Loc) (err : GoInterface),
          ((⌜err ≠ interface.nil⌝ ∗ errOk err) ∨
           (⌜err = interface.nil⌝ ∗ ∃ (st : w64) (hs hc : List (GoString × GoString))
              (rd : GoInterface),
              ⌜hdrView hs hc⌝ ∗ respAt resp st hc rd ∗ readerCloser rd ∗
              readerAt rd (respPre Π R τ st hs) (fun _ => True) [])) -∗
          Ψ (PairV #resp #err)) -∗
      WP (App (Val #(methods i.ty go!"RoundTrip" i.v)) (Val #r)) {{ Ψ }})

/-- **A handler serving the requests under the mux pattern `pfx` with protocol `Π`** (persistent).
`ServeHTTP(w, r)` of a received request under `pfx` (with the client's knowledge, its ticket if
`onceOnly`, its body reader carrying the body knowledge at `EOF`) and a fresh response writer (an
`http.Flusher`: Go's are), on a goroutine holding its thread token: it returns the token and the
writer, committed, or panics (`Serve` recovers it and drops the connection). -/
def handlerOk (h : GoInterface) (Π : Proto GF) (pfx : GoString) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜h = interface.ok i⌝ ∗
    □ ∀ (w : GoInterface) (r : Loc) (R : HReq) (τ : GName) (rd : GoInterface),
      ⌜pathUnder pfx R.path⌝ -∗ srvReq r R rd -∗ □ Π.hreq R τ -∗
      (if decide (onceOnly R) then reqTicket τ else iprop(True)) -∗
      readerAt rd (fun _ => True) (fun B => □ Π.body R τ B) [] -∗
      respW w R τ Π none [] [] -∗ threadTok -∗
      WP (App (App (Val #(methods i.ty go!"ServeHTTP" i.v)) (Val #w)) (Val #r))
        {{ v, threadTok ∗ ((∃ st hs bs, respW w R τ Π (some st) hs bs) ∨
            (⌜v.isPanic = true⌝ ∗ ∃ c hs bs, respW w R τ Π c hs bs)) }})

end vocab

/-! ## Laws (assumed) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

def persistent.spec : Prop :=
  (∀ a Π, Persistent (protoAt (GF := GF) a Π)) ∧
  (∀ rd, Persistent (readerCloser (GF := GF) rd)) ∧
  (∀ resp st hc rd, Persistent (respAt (GF := GF) resp st hc rd)) ∧
  (∀ r R rd, Persistent (srvReq (GF := GF) r R rd)) ∧
  (∀ m L, Persistent (muxAt (GF := GF) m L)) ∧
  (∀ e, Persistent (errOk (GF := GF) e)) ∧
  (∀ rt, Persistent (roundTripperOk (GF := GF) rt)) ∧
  (∀ h Π pfx, Persistent (handlerOk (GF := GF) h Π pfx))

/-- **Reserve an address** for a protocol, once. -/
def reserve.spec : Prop :=
  ∀ (a : GoString) (Π : Proto GF), addrFree (GF := GF) a ⊢ |==> protoAt a Π ∗ protoOwn a Π

/-- One reservation per address. -/
def protoAt_agree.spec : Prop :=
  ∀ a (Π Π' : Proto GF), protoAt (GF := GF) a Π ∗ protoAt a Π' ⊢ iprop(⌜Π = Π'⌝)

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
  ∀ (w : GoInterface) (i : GoInterfaceOk) R τ (Π : Proto GF) c hs bs,
  w = interface.ok i →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ respW w R τ Π c hs bs }}
    (App (Val #(methods i.ty go!"Header" i.v)) (Val #()))
  {{ (hm : GoInterface), RET #hm;
      (⌜c = none⌝ ∗ hdrMap hm hs ∗
        (∀ hs', hdrMap hm hs' -∗ respW w R τ Π none hs' bs)) ∨
      (⌜c ≠ none⌝ ∗ respW w R τ Π c hs bs ∗ ∃ hs', hdrMap hm hs') }}

/-- **`WriteHeader(st)`** (`200 ≤ st ≤ 999`: Go panics outside `100`-`999` and does not commit a
`1xx`): commits `st` with the headers set, if the protocol allows it; a second call is ignored. -/
def respW_writeHeader.spec : Prop :=
  ∀ (w : GoInterface) (i : GoInterfaceOk) R τ (Π : Proto GF) c hs bs (st : w64),
  w = interface.ok i → 200 ≤ uint.nat st → uint.nat st ≤ 999 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ respW w R τ Π c hs bs ∗
      (⌜c = none⌝ -∗ □ Π.resp R τ st hs []) }}
    (App (Val #(methods i.ty go!"WriteHeader" i.v)) (Val #st))
  {{ RET #(); respW w R τ Π (some (c.getD st)) hs bs }}

/-- **`Write(b)`** (committing `200` first if uncommitted): the protocol must allow the bytes;
writes a prefix `n` of `b`, all unless it fails. -/
def respW_write.spec : Prop :=
  ∀ (w : GoInterface) (i : GoInterfaceOk) R τ (Π : Proto GF) c hs bs (b : GoSlice) (ys : List w8)
    (dq : DFrac),
  w = interface.ok i →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ respW w R τ Π c hs bs ∗ b ↦*{dq} ys ∗
      □ Π.resp R τ (c.getD (W64 200)) hs (bs ++ ys) }}
    (App (Val #(methods i.ty go!"Write" i.v)) (Val #b))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      b ↦*{dq} ys ∗ ⌜uint.nat n ≤ ys.length ∧ (err = interface.nil → uint.nat n = ys.length)⌝ ∗
      respW w R τ Π (some (c.getD (W64 200))) hs (bs ++ ys.take (uint.nat n)) ∗ errOk err }}

/-- **`w.(http.Flusher).Flush()`** on a handler's writer: returns (commits `200` if uncommitted,
which the protocol must allow). -/
def respW_flush.spec : Prop :=
  ∀ (w : GoInterface) (i : GoInterfaceOk) R τ (Π : Proto GF) c hs bs,
  w = interface.ok i →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ respW w R τ Π c hs bs ∗
      (⌜c = none⌝ -∗ □ Π.resp R τ (W64 200) hs []) }}
    (App (Val #(methods i.ty go!"Flush" i.v)) (Val #()))
  {{ RET #(); respW w R τ Π (some (c.getD (W64 200))) hs bs }}

/-- A handler's writer is an `http.Flusher` (Go's `*response` is: the type assertion in rafthttp's
handlers succeeds). -/
def respW_flusher.spec : Prop :=
  ∀ (w : GoInterface) R τ (Π : Proto GF) c hs bs,
  respW (GF := GF) w R τ Π c hs bs ⊢ ∃ i : GoInterfaceOk, ⌜w = interface.ok i ∧
    go.typeSetContains i.ty _root_.Perennial.net.http.Flusher.ty = true⌝

/-- **A built mux serves its patterns' handlers** (`ServeMux.ServeHTTP`): a request under `pfx` is
routed to the handler of the longest pattern under which its path is, or answered `404`/`301` by
the mux, which the protocol must allow for a path no pattern routes. -/
def mux_handlerOk.spec : Prop :=
  ∀ (m : Loc) (L : List (GoString × GoInterface)) (Π : Proto GF) (pfx : GoString),
    (∀ (R : HReq) τ, pathUnder pfx R.path → (∀ pat h, (pat, h) ∈ L → ¬ pathUnder pat R.path) →
      ⊢ □ Π.resp R τ (W64 404) [] [] ∧ ⊢ □ Π.resp R τ (W64 301) [] []) →
    muxAt (GF := GF) m L ∗ ([∗list] ph ∈ L, handlerOk ph.2 Π ph.1) ⊢
      handlerOk (interface.mkOk (go.GoType.PointerType _root_.Perennial.net.http.ServeMux.ty) #m)
        Π pfx

end laws

end Http
end EtcdGrove
end Perennial
