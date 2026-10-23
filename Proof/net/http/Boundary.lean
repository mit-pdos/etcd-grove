/-
**The HTTP boundary of rafthttp** (D33 (A), stage 2; `notes/rafthttp-http-boundary.md`, reviewed by
the user 2026-10-22). Lean-first. **A draft for review**: definitions and the statements of the
boundary's specs (`…_spec : Prop`), not yet axioms, and no proof relies on them.

The model (the note's points 1-6):
* An `HReq` is what a client sends: method, host (the address `http://host` names), path, headers
  (as set, in order) and body bytes.
* An `HttpNet` fixes, for the whole run, each address's protocol (`Proto`): a persistent predicate
  `req` on the requests sent to it and `resp` on a request, the status its handler set and the
  bytes the handler wrote. A program's peer addresses are its own (`netAddrFree`); every request a
  server of the program receives comes from a client of the program that went through
  `RoundTrip` (the closed-world statement, accepted 2026-10-22), so the handler gets `□ req R` of
  the request `R` it receives, and the client gets `□ resp R st w` of the response's status and of
  the bytes it reads (a prefix of `w`).
* Body streams are prefixes; a request body's reader returns `EOF` only at the end. Any operation
  may fail with an error.
* The response's status is the one the handler set (revised 2026-10-22: a `403`/`410` is
  `errMemberRemoved`, which matters in a dynamic cluster).
* (2026-10-23, D33b, the user's choice) **A request is handled at most once**: `RoundTrip` takes a
  fresh exclusive ghost ticket (`reqTicket γk`) and the handler of the request receives it; the
  protocols are indexed by the ticket's name. Go's client never replays a `POST`
  (`Request.isReplayable`), and its server runs one handler per request it reads. What a one-shot
  payload needs: the receiver withdraws a deposit with the ticket, so only once.
* A handler's contract is a WP whose postcondition also covers a panic (`Serve` recovers it), and
  each invocation borrows one of `httpProcSlots` resources (the concurrency bound, a physical fact:
  each handler is a goroutine with its own stack).

`http.Request` and `http.Response` are axiomatized types (Goose does not translate their
structs): the predicates speak of their fields' addresses.
-/
module

public import Proof.net.InvNet
public import GeneratedProof.net.http
public import GeneratedProof.net.url
public import Perennial.Code.io
public import Perennial.Code.bytes
public import Perennial.Code.encoding.binary
public import Perennial.Proof.ProofPrelude
public import Perennial.Ghost.DGhostVar
public import Proof.unicode.utf8.Valid

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace http

open Iris Iris.BI

/-- **A request as a client sends it** (see the file header). -/
structure HReq where
  meth : GoString
  host : GoString
  path : GoString
  hdr : List (GoString × GoString)
  body : List w8

section fields
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The field `f` of the `*http.Request` at `r`. -/
abbrev reqF (f : GoString) (r : Loc) : Loc :=
  structFieldRef _root_.Perennial.net.http.Request f r

/-- The field `f` of the `*url.URL` at `u`. -/
abbrev urlF (f : GoString) (u : Loc) : Loc :=
  structFieldRef _root_.Perennial.net.url.URL f u

/-- The field `f` of the `*http.Response` at `r`. -/
abbrev respF (f : GoString) (r : Loc) : Loc :=
  structFieldRef _root_.Perennial.net.http.Response f r

end fields

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An address's protocol** (persistent predicates; see the file header). -/
structure Proto (GF : BundledGFunctors) where
  req : HReq → GName → IProp GF
  req_pers : ∀ R γk, Persistent (req R γk)
  resp : HReq → GName → w64 → List w8 → IProp GF
  resp_pers : ∀ R γk st w, Persistent (resp R γk st w)

instance Proto.req_persistent (P : Proto GF) (R : HReq) (γk : GName) : Persistent (P.req R γk) :=
  P.req_pers R γk

instance Proto.resp_persistent (P : Proto GF) (R : HReq) (γk : GName) (st : w64) (w : List w8) :
    Persistent (P.resp R γk st w) :=
  P.resp_pers R γk st w

/-- **The program's HTTP network**: each address's protocol, fixed for the run. -/
structure HttpNet (GF : BundledGFunctors) where
  proto : GoString → Proto GF

/-- **A request's ticket** (exclusive; D33b): allocated fresh by the client, given up to
`RoundTrip`, received by the handler of the request. -/
def reqTicket (γk : GName) : IProp GF := dghostVar γk (DFrac.own 1) ()

/-- A ticket is exclusive. -/
theorem reqTicket_excl (γk : GName) : reqTicket (GF := GF) γk ∗ reqTicket γk ⊢ False := by
  unfold reqTicket
  iintro ⟨H1, H2⟩
  ihave %Hbad := dghostVar_valid_2 γk () _ () _ $$ H1 H2
  exfalso
  have h := DFrac.valid_own_op Hbad.1
  exact absurd h (by decide)

/-- A fresh ticket. -/
theorem reqTicket_alloc : ⊢ |==> ∃ γk, reqTicket (GF := GF) γk := by
  unfold reqTicket
  iapply dghostVar_alloc

/-- The concurrency bound (D21 M2's `netProcSlots`, the user's (A)): at most `2 ^ 29` handlers at
once. -/
def httpProcSlots : Nat := 2 ^ 29

/-- **The URL string naming `host` and `path`** (opaque, pure): what
`url.URL{Scheme: "http", Host: host, Path: path}.String()` returns. -/
opaque urlOf (host path : GoString) : GoString

/-- `io.EOF`'s value (`io`'s package variable). -/
def ioEOF (e : GoInterface) : IProp GF := globalAddr _root_.Perennial.io.EOF ↦□ e

instance ioEOF_persistent (e : GoInterface) : Persistent (ioEOF (GF := GF) e) := by
  unfold ioEOF; infer_instance

/-! ### The client's side -/

/-! ### Headers -/

/-- **A header key canonicalized** (opaque, pure): `textproto.CanonicalMIMEHeaderKey`, which
`Header.Set` and `Header.Get` apply to their key. -/
opaque canonKey (k : GoString) : GoString

/-- `Header.Set(k, v)`'s effect on the list of (canonical key, value) pairs: `k`'s values
replaced by `v`. -/
def hdrSet (hs : List (GoString × GoString)) (k v : GoString) : List (GoString × GoString) :=
  hs.filter (fun kv => kv.1 ≠ canonKey k) ++ [(canonKey k, v)]

/-- `Header.Get(k)`: the first value of `k` (canonical), or `""`. -/
def hdrGet (hs : List (GoString × GoString)) (k : GoString) : GoString :=
  ((hs.find? (fun kv => kv.1 = canonKey k)).map Prod.snd).getD ""

/-- **A header map `hm` holding `hs`** (exclusive; a request's headers being built, or a response
writer's). -/
opaque hdrOwn (hm : Loc) (hs : List (GoString × GoString)) : IProp GF

/-- The header map `hm` of a received request, holding `hs` (opaque). -/
opaque hdrAtRaw (hm : Loc) (hs : List (GoString × GoString)) : IProp GF

/-- **A received request's header map `hm`, holding `hs`** (persistent): `Get` reads it. -/
def hdrAt (hm : Loc) (hs : List (GoString × GoString)) : IProp GF := iprop(□ hdrAtRaw hm hs)

instance hdrAt_persistent (hm : Loc) (hs : List (GoString × GoString)) :
    Persistent (hdrAt (GF := GF) hm hs) := by
  unfold hdrAt; infer_instance


/-! ### The client's side (continued) -/

/-- **The rest of a request being built** at `r` (exclusive, opaque): its method, URL, body and
context, those of `R` but for the headers, which `reqOwn` keeps in its `Header` map. -/
opaque reqRest (r : Loc) (R : HReq) : IProp GF

/-- **A request being built** at `r` (exclusive): `NewRequest`'s result; its `Header` field holds
the map `hm`, whose `Set`s before `RoundTrip` build `R.hdr`. -/
def reqOwn (r : Loc) (R : HReq) : IProp GF :=
  iprop(∃ hm : Loc, reqF go!"Header" r ↦□ hm ∗ hdrOwn hm R.hdr ∗ reqRest r R)

/-- **An error whose `Error()` returns** (persistent; `nil`, or a value whose `Error` method
returns some string): what net/http's errors are (rafthttp logs them, `err.Error()`). -/
def errStrOk (e : GoInterface) : IProp GF :=
  iprop(⌜e = GoInterface.nil⌝ ∨ ∃ ei : GoInterfaceOk, ⌜e = GoInterface.ok ei⌝ ∗
    □ (∀ Φ : val → IProp GF, ▷ (∀ s : GoString, Φ #s) -∗
      WP (App (Val #(methods ei.ty go!"Error" ei.v)) (Val #())) {{ Φ }}))

instance errStrOk_persistent (e : GoInterface) : Persistent (errStrOk (GF := GF) e) := by
  unfold errStrOk; infer_instance

/-- **A reader holding exactly `bs`** (exclusive; `bytes.NewBuffer(bs)` as an `io.Reader`, or `nil`
for an empty body): what `NewRequest` takes as the body. -/
opaque readerHas (rd : GoInterface) (bs : List w8) : IProp GF

/-- **A response's body reader** for the request `R` to `a`, of status `st`, having read `r`
(exclusive): its reads stay a prefix of what the handler wrote. -/
opaque respReader (H : HttpNet GF) (rd : GoInterface) (R : HReq) (γk : GName) (st : w64)
  (r : List w8) : IProp GF

/-- **A received response** at `resp` for `R`, of status `st` (persistent field facts: its
`StatusCode` is `st`, its `Header` some header map, its `Body` the reader `rd`, not `nil`). -/
def respAt (resp : Loc) (st : w64) (rd : GoInterface) : IProp GF :=
  iprop(respF go!"StatusCode" resp ↦□ st ∗
    (∃ (hm : Loc) (hs : List (GoString × GoString)), respF go!"Header" resp ↦□ hm ∗
      hdrAt (GF := GF) hm hs) ∗
    respF go!"Body" resp ↦□ rd ∗ ⌜rd ≠ GoInterface.nil⌝)

instance respAt_persistent (resp : Loc) (st : w64) (rd : GoInterface) :
    Persistent (respAt (GF := GF) resp st rd) := by
  unfold respAt; infer_instance

/-- **A round tripper of the network `H`** (persistent; what rafthttp's names-only
`NewRoundTripper`/`newStreamRoundTripper` return): `RoundTrip` of a request built for `R`, with
its ticket `γk` and `□ (H.proto R.host).req R γk`, either fails or returns a response whose status
`st` is the handler's (with `□ ∃ w, resp R γk st w`) and whose body reader starts at `[]`; the
request is the caller's again (`RoundTrip` must not modify it). -/
def roundTripperOk (H : HttpNet GF) (rt : GoInterface) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜rt = GoInterface.ok ti⌝ ∗
    □ (∀ (r : Loc) (R : HReq) (γk : GName),
      {{ reqOwn r R ∗ reqTicket γk ∗ □ (H.proto R.host).req R γk }}
        (App (Val #(methods ti.ty go!"RoundTrip" ti.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); reqOwn r R ∗
          (⌜err ≠ GoInterface.nil⌝ ∗ errStrOk err ∨
           ⌜err = GoInterface.nil⌝ ∗ ∃ (st : w64) (rd : GoInterface),
            respAt resp st rd ∗ (□ ∃ w, (H.proto R.host).resp R γk st w) ∗
            respReader H rd R γk st []) }}))

instance roundTripperOk_persistent (H : HttpNet GF) (rt : GoInterface) :
    Persistent (roundTripperOk H rt) := by
  unfold roundTripperOk; infer_instance

/-! ### The server's side -/

/-- **A received request** at `r` (persistent field facts): its `Method`, `URL` (a `*url.URL` whose
`Path` is `R.path`), `Header` (`hdrAt` of `R.hdr`), `RemoteAddr` (some ASCII string: the server
writes the peer's `ip:port`) and `Body` (the reader `rd`, never `nil`: the server sets `NoBody`
for an empty one). -/
def reqAt (r : Loc) (R : HReq) (rd : GoInterface) : IProp GF :=
  iprop(reqF go!"Method" r ↦□ R.meth ∗
    (∃ u : Loc, reqF go!"URL" r ↦□ u ∗
      urlF go!"Path" u ↦□ R.path) ∗
    (∃ hm : Loc, reqF go!"Header" r ↦□ hm ∗ hdrAt hm R.hdr) ∗
    (∃ ra : GoString, reqF go!"RemoteAddr" r ↦□ ra ∗ ⌜asciiStr ra⌝) ∗
    reqF go!"Body" r ↦□ rd ∗ ⌜rd ≠ GoInterface.nil⌝)

instance reqAt_persistent (r : Loc) (R : HReq) (rd : GoInterface) :
    Persistent (reqAt (GF := GF) r R rd) := by
  unfold reqAt; infer_instance

/-- **A request body's reader** for `R`, having read `r` (exclusive): reads stay a prefix of
`R.body`; `EOF` only once all of it is read. -/
opaque bodyReader (rd : GoInterface) (R : HReq) (r : List w8) : IProp GF

/-- **A response writer** for the request `R` to `a`, with the status set (`none` before
`WriteHeader`) and the bytes written `w` (exclusive; it may be passed to another goroutine, as the
stream handler does). -/
opaque respWriter (H : HttpNet GF) (wr : GoInterface) (a : GoString) (R : HReq) (γk : GName)
  (st : Option w64) (w : List w8) : IProp GF

/-- **A handler of the address `a`** (persistent), lending each invocation the resource `Rs`:
`ServeHTTP` of any request the network delivers to `a`, with its ticket, its body reader and a
fresh response writer (a non-`nil` interface value, an `http.Flusher`: the server's writers are),
returns `Rs` (or panics, giving it back too: `Serve` recovers the panic). -/
def handlerOk (H : HttpNet GF) (a : GoString) (Rs : IProp GF) (h : GoInterface) : IProp GF :=
  iprop(∃ hi : GoInterfaceOk, ⌜h = GoInterface.ok hi⌝ ∗
    □ (∀ (wi : GoInterfaceOk) (r : Loc) (R : HReq) (γk : GName) (rd : GoInterface),
      reqAt r R rd -∗ ⌜R.host = a⌝ -∗ □ (H.proto a).req R γk -∗ reqTicket γk -∗
        bodyReader rd R [] -∗ respWriter H (GoInterface.ok wi) a R γk none [] -∗
        ⌜go.typeSetContains wi.ty _root_.Perennial.net.http.Flusher.ty = true⌝ -∗ Rs -∗
        WP (App (App (Val #(methods hi.ty go!"ServeHTTP" hi.v)) (Val #(GoInterface.ok wi)))
          (Val #r)) {{ _v, Rs }}))

/-! ### The specs (statements for review; see the file header) -/

/-- `http.Serve(l, h)` on the listener bound at `a`, with a handler of `a` and `httpProcSlots`
copies of the resource its invocations borrow: returns an error if it returns (it serves each
request on its own goroutine). -/
def Serve_spec (H : HttpNet GF) : Prop :=
  ∀ (l h : GoInterface) (a : GoString) (Rs : IProp GF),
    ⊢ {{ netListenerAt (GF := GF) l a ∗ handlerOk H a Rs h ∗
          [∗list] _x ∈ List.replicate httpProcSlots (), Rs }}
        (App (App (Val (@! _root_.Perennial.net.http.Serve)) (Val #l)) (Val #h))
      {{ (err : GoInterface), RET #err; True }}

/-- A request body's `Read(p)`: some `n` bytes `ys` (into `p`'s first `n`), still a prefix of the
body; `EOF` only at the end. -/
def bodyRead_spec : Prop :=
  ∀ (rd : GoInterface) (ri : GoInterfaceOk) (R : HReq) (r : List w8) (p : GoSlice)
    (xs : List w8) (e : GoInterface),
    rd = GoInterface.ok ri →
    ⊢ {{ bodyReader (GF := GF) rd R r ∗ p ↦* xs ∗ ioEOF e }}
        (App (Val #(methods ri.ty go!"Read" ri.v)) (Val #p))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
          ∃ ys : List w8, ⌜ys.length = sint.nat n ∧ r ++ ys <+: R.body ∧
            (err = e → r ++ ys = R.body)⌝ ∗
          p ↦* (ys ++ xs.drop ys.length) ∗ bodyReader rd R (r ++ ys) }}

/-- A response body's `Read(p)`: some bytes, still a prefix of some `w` the handler wrote with
`□ resp R st w`. -/
def respRead_spec (H : HttpNet GF) : Prop :=
  ∀ (rd : GoInterface) (ri : GoInterfaceOk) (R : HReq) (γk : GName) (st : w64) (r : List w8)
    (p : GoSlice) (xs : List w8),
    rd = GoInterface.ok ri →
    ⊢ {{ respReader H rd R γk st r ∗ p ↦* xs }}
        (App (Val #(methods ri.ty go!"Read" ri.v)) (Val #p))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
          ∃ ys : List w8, ⌜ys.length = sint.nat n⌝ ∗
          (□ ∃ w, ⌜r ++ ys <+: w⌝ ∗ (H.proto R.host).resp R γk st w) ∗
          p ↦* (ys ++ xs.drop ys.length) ∗ respReader H rd R γk st (r ++ ys) }}

/-- `ResponseWriter.Write(b)`: needs the protocol of what has then been written; may fail. -/
def respWrite_spec (H : HttpNet GF) : Prop :=
  ∀ (wr : GoInterface) (wi : GoInterfaceOk) (a : GoString) (R : HReq) (γk : GName)
    (st : Option w64) (w : List w8) (b : GoSlice) (bs : List w8) (dq : DFrac),
    wr = GoInterface.ok wi →
    ⊢ {{ respWriter H wr a R γk st w ∗ b ↦*{dq} bs ∗
          □ (H.proto a).resp R γk (st.getD (W64 200)) (w ++ bs) }}
        (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #b))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
          b ↦*{dq} bs ∗ respWriter H wr a R γk (some (st.getD (W64 200))) (w ++ bs) }}

/-- `ResponseWriter.WriteHeader(st)` before any write: sets the status, which needs the protocol
of the (still empty) response with it. -/
def respWriteHeader_spec (H : HttpNet GF) : Prop :=
  ∀ (wr : GoInterface) (wi : GoInterfaceOk) (a : GoString) (R : HReq) (γk : GName) (st : w64),
    wr = GoInterface.ok wi →
    ⊢ {{ respWriter H wr a R γk none [] ∗ □ (H.proto a).resp R γk st [] }}
        (App (Val #(methods wi.ty go!"WriteHeader" wi.v)) (Val #st))
      {{ RET #(); respWriter H wr a R γk (some st) [] }}

/-- `http.NewRequest(method, url, body)`, with a body reader holding `bs` and a URL naming `host`
and `path` (`urlOf`, the URL `url.URL{Scheme: "http", Host: host, Path: path}.String()` gives, as
rafthttp builds them): a request of method, host, path and body, no headers. (2026-10-23, stage 4d)
No error for `GET` or `POST`: `NewRequest` fails only on an invalid method or a URL that does not
parse, and the string of a parsed URL's host and a path parses. -/
def NewRequest_spec : Prop :=
  ∀ (meth u : GoString) (body : GoInterface) (bs : List w8) (host path : GoString),
    u = urlOf host path → (meth = go!"POST" ∨ meth = go!"GET") →
    ⊢ {{ readerHas (GF := GF) body bs }}
        (App (App (App (Val (@! _root_.Perennial.net.http.NewRequest)) (Val #meth)) (Val #u))
          (Val #body))
      {{ (r : Loc), RET (PairV #r #GoInterface.nil); reqOwn r ⟨meth, host, path, [], bs⟩ }}

/-- `hm.Set(k, v)` (`http.Header`'s, a method of the map type) on a header map being built. -/
def HeaderSet_spec : Prop :=
  ∀ (hm : Loc) (hs : List (GoString × GoString)) (k v : GoString),
    ⊢ {{ hdrOwn (GF := GF) hm hs }}
        (App (App (Val (hm @!! _root_.Perennial.net.http.Header.ty @!! go!"Set")) (Val #k))
          (Val #v))
      {{ RET #(); hdrOwn hm (hdrSet hs k v) }}

/-- `hm.Get(k)` on a received request's header map. -/
def HeaderGet_spec : Prop :=
  ∀ (hm : Loc) (hs : List (GoString × GoString)) (k : GoString),
    ⊢ {{ hdrAt (GF := GF) hm hs }}
        (App (Val (hm @!! _root_.Perennial.net.http.Header.ty @!! go!"Get")) (Val #k))
      {{ RET #(hdrGet hs k); True }}

/-- `w.Header()` of a response writer: a header map the handler may `Set` freely (the client's
view of response headers is unconstrained). -/
def RespHeader_spec (H : HttpNet GF) : Prop :=
  ∀ (wr : GoInterface) (wi : GoInterfaceOk) (a : GoString) (R : HReq) (γk : GName)
    (st : Option w64) (w : List w8),
    wr = GoInterface.ok wi →
    ⊢ {{ respWriter H wr a R γk st w }}
        (App (Val #(methods wi.ty go!"Header" wi.v)) (Val #()))
      {{ (hm : Loc), RET #hm; respWriter H wr a R γk st w ∗ ∃ hs, hdrOwn hm hs }}

/-- **A reader of the bytes `B`** (persistent, D33b): its `Read` from a state `Src r` (`r` read so
far; `io.EOF`'s value `e`) reads `ys`, still a prefix of `B`, and returns `EOF` (`e`) only once `r ++ ys = B` -- the
`io.Reader` contract of a request body (`bodyRead_spec`) and of any reader wrapping one. -/
def prefixReaderOk (rd : GoInterface) (Src : List w8 → IProp GF) (B : List w8) (e : GoInterface) :
    IProp GF :=
  iprop(∃ ri : GoInterfaceOk, ⌜rd = GoInterface.ok ri⌝ ∗
    □ (∀ (r : List w8) (p : GoSlice) (xs : List w8),
      {{ Src r ∗ p ↦* xs ∗ ioEOF e }}
        (App (Val #(methods ri.ty go!"Read" ri.v)) (Val #p))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
          ∃ ys : List w8, ⌜ys.length = sint.nat n ∧ r ++ ys <+: B ∧ (err = e → r ++ ys = B)⌝ ∗
          p ↦* (ys ++ xs.drop ys.length) ∗ Src (r ++ ys) }}))

instance prefixReaderOk_persistent (rd : GoInterface) (Src : List w8 → IProp GF) (B : List w8)
    (e : GoInterface) : Persistent (prefixReaderOk rd Src B e) := by
  unfold prefixReaderOk; infer_instance

/-- `io.ReadAll(rd)` of a reader of `B` (D33b: over any reader keeping the prefix contract, a
request body's or a wrapper's): the whole of `B`, or an error. -/
def ReadAll_spec : Prop :=
  ∀ (rd : GoInterface) (Src : List w8 → IProp GF) (B : List w8) (e : GoInterface),
    ⊢ {{ prefixReaderOk rd Src B e ∗ Src [] ∗ ioEOF e }}
        (App (Val (@! _root_.Perennial.io.ReadAll)) (Val #rd))
      {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
          ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗ sl ↦* B }}

/-- `io.ReadFull(rd, p)` of a response body: `len(p)` bytes, still a prefix of what the handler
wrote, or an error. -/
def ReadFull_resp_spec (H : HttpNet GF) : Prop :=
  ∀ (rd : GoInterface) (R : HReq) (γk : GName) (st : w64) (r : List w8) (p : GoSlice)
    (xs : List w8),
    ⊢ {{ respReader H rd R γk st r ∗ p ↦* xs }}
        (App (App (Val (@! _root_.Perennial.io.ReadFull)) (Val #rd)) (Val #p))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
          ∃ ys : List w8, ⌜ys.length = sint.nat n ∧ (err = GoInterface.nil → n = p.len)⌝ ∗
          (□ ∃ w, ⌜r ++ ys <+: w⌝ ∗ (H.proto R.host).resp R γk st w) ∗
          p ↦* (ys ++ xs.drop ys.length) ∗ respReader H rd R γk st (r ++ ys) }}

/-- `w.(http.Flusher).Flush()` on a response writer: returns (it matters for latency, not for
safety). -/
def Flush_spec (H : HttpNet GF) : Prop :=
  ∀ (wr : GoInterface) (wi : GoInterfaceOk) (a : GoString) (R : HReq) (γk : GName)
    (st : Option w64) (w : List w8),
    wr = GoInterface.ok wi →
    ⊢ {{ respWriter H wr a R γk st w }}
        (App (Val #(methods wi.ty go!"Flush" wi.v)) (Val #()))
      {{ RET #(); respWriter H wr a R γk st w }}

/-- `http.Error(w, msg, code)` before any write: the status `code`, the body `msg` and a newline. -/
def Error_spec (H : HttpNet GF) : Prop :=
  ∀ (wr : GoInterface) (a : GoString) (R : HReq) (γk : GName) (msg : GoString) (code : w64),
    ⊢ {{ respWriter H wr a R γk none [] ∗ □ (H.proto a).resp R γk code (msg ++ [W8 10]) }}
        (App (App (App (Val (@! _root_.Perennial.net.http.Error)) (Val #wr)) (Val #msg))
          (Val #code))
      {{ RET #(); respWriter H wr a R γk (some code) (msg ++ [W8 10]) }}

/-! ### The pipeline's client side (rafthttp stage 4d) -/

/-- `bytes.NewBuffer(b)` (`bytes`, names-only): a reader holding `b`'s bytes, which it takes. -/
def NewBuffer_spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8),
    ⊢ {{ (b ↦* bs : IProp GF) }}
        (App (Val (@! _root_.Perennial.bytes.NewBuffer)) (Val #b))
      {{ (rd : Loc), RET #rd;
          readerHas (interface.mkOk (go.GoType.PointerType _root_.Perennial.bytes.Buffer.ty) #rd) bs }}

/-- `r.WithContext(ctx)` of a request being built: a shallow copy, the same request (for a
non-`nil` context). -/
def WithContext_spec : Prop :=
  ∀ (r : Loc) (R : HReq) (ctx : GoInterfaceOk),
    ⊢ {{ reqOwn (GF := GF) r R }}
        (App (Val (r @!! go.GoType.PointerType _root_.Perennial.net.http.Request.ty @!! go!"WithContext"))
          (Val #(GoInterface.ok ctx)))
      {{ (r' : Loc), RET #r'; reqOwn r' R }}

/-- `io.ReadAll(rd)` of a response body: some bytes read (a prefix of what the handler wrote,
`respRead_spec`'s), or an error. -/
def ReadAll_resp_spec (H : HttpNet GF) : Prop :=
  ∀ (rd : GoInterface) (R : HReq) (γk : GName) (st : w64),
    ⊢ {{ respReader H rd R γk st [] }}
        (App (Val (@! _root_.Perennial.io.ReadAll)) (Val #rd))
      {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
          ∃ bs : List w8, sl ↦* bs ∗ respReader H rd R γk st bs ∗ errStrOk err }}

/-- A response body's `Close()`: some error. -/
def RespClose_spec (H : HttpNet GF) : Prop :=
  ∀ (rd : GoInterface) (ri : GoInterfaceOk) (R : HReq) (γk : GName) (st : w64) (r : List w8),
    rd = GoInterface.ok ri →
    ⊢ {{ respReader H rd R γk st r }}
        (App (Val #(methods ri.ty go!"Close" ri.v)) (Val #()))
      {{ (err : GoInterface), RET #err; True }}

/-! ### Routing (`http.ServeMux`) -/

/-- A pattern matches a path (Go's `ServeMux` for plain path patterns, as rafthttp registers):
a pattern ending in `/` matches its subtree, any other only itself. -/
def patMatches (pat path : GoString) : Bool :=
  if pat.getLast? = some (W8 47) then pat.isPrefixOf path else pat == path

/-- The pattern a path is routed to: the longest registered pattern that matches it. -/
def route (pats : List GoString) (path : GoString) : Option GoString :=
  (pats.filter (fun p => patMatches p path)).foldl
    (fun best p => match best with
      | none => some p
      | some b => if b.length < p.length then some p else some b) none

/-- **A mux being built** at `m` (exclusive): its registrations so far. -/
opaque muxOwn (m : Loc) (regs : List (GoString × GoInterface)) : IProp GF

/-- `http.NewServeMux()`: an empty mux. -/
def NewServeMux_spec : Prop :=
  ⊢ {{ (True : IProp GF) }}
      (App (Val (@! _root_.Perennial.net.http.NewServeMux)) (Val #()))
    {{ (m : Loc), RET #m; muxOwn m [] }}

/-- `m.Handle(pat, h)`: the registration appended (a pattern registered twice panics in Go; the
callers register distinct ones, which the precondition states). -/
def Handle_spec : Prop :=
  ∀ (m : Loc) (regs : List (GoString × GoInterface)) (pat : GoString) (h : GoInterface),
    ⊢ {{ muxOwn (GF := GF) m regs ∗ ⌜pat ∉ regs.map Prod.fst⌝ }}
        (App (App (Val (m @!! go.GoType.PointerType _root_.Perennial.net.http.ServeMux.ty @!!
          go!"Handle")) (Val #pat)) (Val #h))
      {{ RET #(); muxOwn m (regs ++ [(pat, h)]) }}

/-- **A handler of `a` for the requests routed to `pat`** (persistent): as `handlerOk`, for the
requests whose path `route` sends to `pat`. -/
def handlerFor (H : HttpNet GF) (a : GoString) (Rs : IProp GF) (pats : List GoString)
    (pat : GoString) (h : GoInterface) : IProp GF :=
  iprop(∃ hi : GoInterfaceOk, ⌜h = GoInterface.ok hi⌝ ∗
    □ (∀ (wi : GoInterfaceOk) (r : Loc) (R : HReq) (γk : GName) (rd : GoInterface),
      reqAt r R rd -∗ ⌜R.host = a ∧ route pats R.path = some pat⌝ -∗ □ (H.proto a).req R γk -∗
        reqTicket γk -∗ bodyReader rd R [] -∗ respWriter H (GoInterface.ok wi) a R γk none [] -∗
        ⌜go.typeSetContains wi.ty _root_.Perennial.net.http.Flusher.ty = true⌝ -∗ Rs -∗
        WP (App (App (Val #(methods hi.ty go!"ServeHTTP" hi.v)) (Val #(GoInterface.ok wi)))
          (Val #r)) {{ _v, Rs }}))

/-- **A built mux is a handler of `a`** (the mux's dispatch, stated as what its `ServeHTTP` does):
each registered handler handles what is routed to it; a request routed nowhere (or redirected,
for a path not in `ServeMux`'s clean form) gets the mux's own `404`/`301` response, which the
protocol must allow. -/
def mux_handlerOk_spec (H : HttpNet GF) : Prop :=
  ∀ (m : Loc) (regs : List (GoString × GoInterface)) (a : GoString) (Rs : IProp GF),
    ⊢ muxOwn (GF := GF) m regs -∗
      ([∗list] reg ∈ regs, handlerFor H a Rs (regs.map Prod.fst) reg.1 reg.2) -∗
      (□ ∀ (R : HReq) (γk : GName) (st : w64) (w : List w8),
        ⌜route (regs.map Prod.fst) R.path = none⌝ → (H.proto a).req R γk -∗
          (H.proto a).resp R γk st w) -∗
      handlerOk H a Rs (interface.mkOk (go.GoType.PointerType
        _root_.Perennial.net.http.ServeMux.ty) #m)

/-! ### URLs -/

/-- `u.String()` of a `url.URL` with only `Scheme = "http"`, `Host` and `Path` set: `urlOf`. -/
def URLString_spec : Prop :=
  ∀ (u : _root_.Perennial.net.url.URL),
    u.Scheme' = go!"http" → u.Opaque' = "" → u.User' = null → u.Fragment' = "" →
    u.RawQuery' = "" → u.RawPath' = "" → u.RawFragment' = "" → u.ForceQuery' = false →
    u.OmitHost' = false →
    ⊢ {{ (True : IProp GF) }}
        (App (Val (u @!! _root_.Perennial.net.url.URL.ty @!! go!"String")) (Val #()))
      {{ RET #(urlOf u.Host' u.Path'); True }}

/-! `encoding/binary`'s `Write` and `Read` of an integer (the codecs' length prefixes) are
`Spec/encoding/binary/{WriteUint64,WriteUint8,ReadUint64}.lean`. -/

/-- A request body's reader keeps the prefix contract (`bodyRead_spec`). -/
theorem bodyReader_prefixOk (hR : bodyRead_spec (GF := GF)) (rd : GoInterface) (R : HReq)
    (e : GoInterface) (hrd : rd ≠ GoInterface.nil) :
    ⊢ prefixReaderOk (GF := GF) rd (bodyReader rd R) R.body e := by
  cases rd with
  | nil => exact absurd rfl hrd
  | ok ri =>
    unfold prefixReaderOk
    iexists ri
    isplitr
    · ipureintro; rfl
    iintro !> %r %p %xs %Φ !> ⟨Hs, Hp, #He⟩ HΦ
    iapply (hR _ ri R r p xs e rfl) $$ [$Hs $Hp $He]
    iexact HΦ

end defs

end http
end EtcdGrove
end Perennial
