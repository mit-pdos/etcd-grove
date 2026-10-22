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

`http.Request` and `http.Response` are axiomatized types (Goose does not translate their
structs): the predicates speak of their fields' addresses.
-/
module

public import Proof.net.InvNet
public import GeneratedProof.net.http
public import GeneratedProof.net.url
public import Perennial.Code.io
public import Perennial.Proof.ProofPrelude

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

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An address's protocol** (persistent predicates; see the file header). -/
structure Proto (GF : BundledGFunctors) where
  req : HReq → IProp GF
  req_pers : ∀ R, Persistent (req R)
  resp : HReq → w64 → List w8 → IProp GF
  resp_pers : ∀ R st w, Persistent (resp R st w)

/-- **The program's HTTP network**: each address's protocol, fixed for the run. -/
structure HttpNet (GF : BundledGFunctors) where
  proto : GoString → Proto GF

/-- **The URL string naming `host` and `path`** (opaque, pure): what
`url.URL{Scheme: "http", Host: host, Path: path}.String()` returns. -/
opaque urlOf (host path : GoString) : GoString

/-- `io.EOF`'s value (`io`'s package variable). -/
def ioEOF (e : GoInterface) : IProp GF := globalAddr _root_.Perennial.io.EOF ↦□ e

/-! ### The client's side -/

/-- **A request being built** at `r` (exclusive): `NewRequest`'s result, its headers `Set` before
`RoundTrip`. The record `R` is what will be sent. -/
opaque reqOwn (r : Loc) (R : HReq) : IProp GF

/-- **A reader holding exactly `bs`** (exclusive; `bytes.NewBuffer(bs)` as an `io.Reader`, or `nil`
for an empty body): what `NewRequest` takes as the body. -/
opaque readerHas (rd : GoInterface) (bs : List w8) : IProp GF

/-- **A response's body reader** for the request `R` to `a`, of status `st`, having read `r`
(exclusive): its reads stay a prefix of what the handler wrote. -/
opaque respReader (H : HttpNet GF) (rd : GoInterface) (R : HReq) (st : w64) (r : List w8) :
  IProp GF

/-- **A received response** at `resp` for `R`, of status `st` (persistent field facts: its
`StatusCode` is `st`, its `Header` some header map, its `Body` the reader `rd`). -/
opaque respAt (resp : Loc) (st : w64) (rd : GoInterface) : IProp GF

/-- **A round tripper of the network `H`** (persistent; what rafthttp's names-only
`NewRoundTripper`/`newStreamRoundTripper` return): `RoundTrip` of a request built for `R` with
`□ (H.proto R.host).req R` either fails or returns a response whose status `st` is the handler's
(with `□ ∃ w, resp R st w`) and whose body reader starts at `[]`. -/
def roundTripperOk (H : HttpNet GF) (rt : GoInterface) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜rt = GoInterface.ok ti⌝ ∗
    □ (∀ (r : Loc) (R : HReq),
      {{ reqOwn r R ∗ □ (H.proto R.host).req R }}
        (App (Val #(methods ti.ty go!"RoundTrip" ti.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          ⌜err ≠ GoInterface.nil⌝ ∨
          ⌜err = GoInterface.nil⌝ ∗ ∃ (st : w64) (rd : GoInterface),
            respAt resp st rd ∗ (□ ∃ w, (H.proto R.host).resp R st w) ∗
            respReader H rd R st [] }}))

/-! ### The server's side -/

/-- **A received request** at `r` (persistent field facts): its `Method`, `URL` (with `Path`),
`Header` (whose `Get` returns the value last set by the client, or `""`), `RemoteAddr` and `Body`
(the reader `rd`) are those of `R`. -/
opaque reqAt (r : Loc) (R : HReq) (rd : GoInterface) : IProp GF

/-- **A request body's reader** for `R`, having read `r` (exclusive): reads stay a prefix of
`R.body`; `EOF` only once all of it is read. -/
opaque bodyReader (rd : GoInterface) (R : HReq) (r : List w8) : IProp GF

/-- **A response writer** for the request `R` to `a`, with the status set (`none` before
`WriteHeader`) and the bytes written `w` (exclusive; it may be passed to another goroutine, as the
stream handler does). -/
opaque respWriter (H : HttpNet GF) (wr : GoInterface) (a : GoString) (R : HReq) (st : Option w64)
  (w : List w8) : IProp GF

/-- **A handler of the address `a`** (persistent): `ServeHTTP` of any request the network
delivers to `a`, with its body reader and a fresh response writer, returns (a panic is recovered
by `Serve`, so its postcondition is any). -/
def handlerOk (H : HttpNet GF) (a : GoString) (h : GoInterface) : IProp GF :=
  iprop(∃ hi : GoInterfaceOk, ⌜h = GoInterface.ok hi⌝ ∗
    □ (∀ (wr : GoInterface) (r : Loc) (R : HReq) (rd : GoInterface),
      {{ reqAt r R rd ∗ ⌜R.host = a⌝ ∗ □ (H.proto a).req R ∗ bodyReader rd R [] ∗
          respWriter H wr a R none [] }}
        (App (App (Val #(methods hi.ty go!"ServeHTTP" hi.v)) (Val #wr)) (Val #r))
      {{ (v : val), RET v; True }}))

/-! ### The specs (statements for review; see the file header) -/

/-- `http.Serve(l, h)` on the listener bound at `a`, with a handler of `a`: returns an error if
it returns (it serves each request on its own goroutine). -/
def Serve_spec (H : HttpNet GF) : Prop :=
  ∀ (l h : GoInterface) (a : GoString),
    ⊢ {{ netListenerAt (GF := GF) l a ∗ handlerOk H a h }}
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
  ∀ (rd : GoInterface) (ri : GoInterfaceOk) (R : HReq) (st : w64) (r : List w8) (p : GoSlice)
    (xs : List w8),
    rd = GoInterface.ok ri →
    ⊢ {{ respReader H rd R st r ∗ p ↦* xs }}
        (App (Val #(methods ri.ty go!"Read" ri.v)) (Val #p))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
          ∃ ys : List w8, ⌜ys.length = sint.nat n⌝ ∗
          (□ ∃ w, ⌜r ++ ys <+: w⌝ ∗ (H.proto R.host).resp R st w) ∗
          p ↦* (ys ++ xs.drop ys.length) ∗ respReader H rd R st (r ++ ys) }}

/-- `ResponseWriter.Write(b)`: needs the protocol of what has then been written; may fail. -/
def respWrite_spec (H : HttpNet GF) : Prop :=
  ∀ (wr : GoInterface) (wi : GoInterfaceOk) (a : GoString) (R : HReq) (st : Option w64)
    (w : List w8) (b : GoSlice) (bs : List w8) (dq : DFrac),
    wr = GoInterface.ok wi →
    ⊢ {{ respWriter H wr a R st w ∗ b ↦*{dq} bs ∗
          □ (H.proto a).resp R (st.getD (W64 200)) (w ++ bs) }}
        (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #b))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
          b ↦*{dq} bs ∗ respWriter H wr a R (some (st.getD (W64 200))) (w ++ bs) }}

/-- `ResponseWriter.WriteHeader(st)` before any write: sets the status, which needs the protocol
of the (still empty) response with it. -/
def respWriteHeader_spec (H : HttpNet GF) : Prop :=
  ∀ (wr : GoInterface) (wi : GoInterfaceOk) (a : GoString) (R : HReq) (st : w64),
    wr = GoInterface.ok wi →
    ⊢ {{ respWriter H wr a R none [] ∗ □ (H.proto a).resp R st [] }}
        (App (Val #(methods wi.ty go!"WriteHeader" wi.v)) (Val #st))
      {{ RET #(); respWriter H wr a R (some st) [] }}

/-- `http.NewRequest(method, url, body)`, with a body reader holding `bs` and a URL naming `host`
and `path` (`urlOf`, the URL `url.URL{Scheme: "http", Host: host, Path: path}.String()` gives, as
rafthttp builds them): a request of method, host, path and body, no headers, or an error. -/
def NewRequest_spec : Prop :=
  ∀ (meth u : GoString) (body : GoInterface) (bs : List w8) (host path : GoString),
    u = urlOf host path →
    ⊢ {{ readerHas (GF := GF) body bs }}
        (App (App (App (Val (@! _root_.Perennial.net.http.NewRequest)) (Val #meth)) (Val #u))
          (Val #body))
      {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
          ⌜err ≠ GoInterface.nil⌝ ∨
          ⌜err = GoInterface.nil⌝ ∗ reqOwn r ⟨meth, host, path, [], bs⟩ }}

/-- `req.Header.Set(k, v)` on a request being built: the header recorded. (The translation loads
`req.Header`, a map, and calls `Header.Set` on it; the statement is of the two steps' effect, its
exact form fixed when the client's proofs need it.) -/
def reqHeaderSet_effect (r : Loc) (R : HReq) (k v : GoString) : IProp GF :=
  iprop(reqOwn r R -∗ reqOwn r { R with hdr := R.hdr ++ [(k, v)] })

/-- `io.ReadAll(rd)` of a request body: the whole body, or an error. -/
def ReadAll_body_spec : Prop :=
  ∀ (rd : GoInterface) (R : HReq) (e : GoInterface),
    ⊢ {{ bodyReader (GF := GF) rd R [] ∗ ioEOF e }}
        (App (Val (@! _root_.Perennial.io.ReadAll)) (Val #rd))
      {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
          ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗ sl ↦* R.body }}

/-- `io.ReadFull(rd, p)` of a response body: `len(p)` bytes, still a prefix of what the handler
wrote, or an error. -/
def ReadFull_resp_spec (H : HttpNet GF) : Prop :=
  ∀ (rd : GoInterface) (R : HReq) (st : w64) (r : List w8) (p : GoSlice) (xs : List w8),
    ⊢ {{ respReader H rd R st r ∗ p ↦* xs }}
        (App (App (Val (@! _root_.Perennial.io.ReadFull)) (Val #rd)) (Val #p))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
          ∃ ys : List w8, ⌜ys.length = sint.nat n ∧ (err = GoInterface.nil → n = p.len)⌝ ∗
          (□ ∃ w, ⌜r ++ ys <+: w⌝ ∗ (H.proto R.host).resp R st w) ∗
          p ↦* (ys ++ xs.drop ys.length) ∗ respReader H rd R st (r ++ ys) }}

/-- `w.(http.Flusher).Flush()` on a response writer: returns (it matters for latency, not for
safety). -/
def Flush_spec (H : HttpNet GF) : Prop :=
  ∀ (wr : GoInterface) (wi : GoInterfaceOk) (a : GoString) (R : HReq) (st : Option w64)
    (w : List w8),
    wr = GoInterface.ok wi →
    ⊢ {{ respWriter H wr a R st w }}
        (App (Val #(methods wi.ty go!"Flush" wi.v)) (Val #()))
      {{ RET #(); respWriter H wr a R st w }}

end defs

end http
end EtcdGrove
end Perennial
