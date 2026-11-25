/-
**The vocabulary of net/http's server over a user handler, and of a raw HTTP/1.1 client**
(httpdriver, 2026-11-24; `notes/library-drivers.md`, "net/http's driver"): phase 7 S5's draft
vocabulary (`notes/phase7-plan.md`, "S5 draft signatures"; `SpecPlan/Spec/net/http/Api.lean`),
defined. **Interim**: the specs over it (`Serve.spec`, `ServeMux.ServeHTTP.spec`,
`ServeMux.HandleFunc.spec`, `ReadResponse.spec_resp`) are trust-boundary axioms until S5 proves
them; S5 refines these definitions (where they differ from its draft: "Departures" below).

## Requests (pure)

* `HReq`: a request as written: method, `Host`, path, and its other header lines in order (with its
  `Content-Length` line, if any; never its `Host` line).
* `reqWire R B`: its wire, as a raw client writes it: `METHOD PATH HTTP/1.1\r\n`, the `Host` line,
  the other lines, the empty line, the body `B`.
* `reqOk R B`: a request the server reads as written: a method token other than `CONNECT`, `HEAD`,
  `PRI` (`methOk`), a path the model's URI parser leaves alone (`reqPath`), header lines the model
  reads as they are (`hdrBlockOk`), none of the keys that change how the server reads or answers
  (`reqKeysOut`: `Transfer-Encoding` (a chunked body is not modelled), `Expect`, `Connection`,
  `Trailer`, `Upgrade`, `Te`, and `Pragma`: `readRequest` adds `Cache-Control: no-cache` for
  `Pragma: no-cache`), a `Host` the server accepts (`hostByte`, `ValidHostHeader`), at most 500 header
  lines counting `Host` (`maxHeaderValueCount`: more get a `431`), a `Content-Length` line with `B`'s length (decimal) or none and no
  body, a head within the server's read limit (`2 ^ 20` bytes, as `Serve.spec_rpc`'s path) and a body
  shorter than `2 ^ 60` bytes.
* `ReqSlot`: what a dialer writes for one request: a request `(R, τ, B)` (`τ` the client's ghost name
  for it) or junk `j` (`junkOk`: a non-empty line, ended by `"\n"`, not starting with `"\r"` (after a
  `POST` the server discards leading CR and LF bytes), whose third field (`parseReqLine`) does not start
  with `"HTTP/"`, so that the server rejects it at its request line; only as the last slot).
  `slotsWire L`: the slots' wires in order.

## Responses (pure)

* `Resp`: a response as the server writes it: status, reason phrase, header lines, body, and whether
  its body is delimited by the connection's end (`close`, net/http's own `400` answer) or by its
  `Content-Length` (every handler's response whose framing a client reads).
  `respHeadWire st reason hc`: `HTTP/1.1 <st> <reason>\r\n`, the lines, the empty line;
  `respWire ρ`: the head and the body.
* `respOk ρ`: a response the model's `ReadResponse` reads as written: a status `200`-`999`, a reason of
  printable bytes, header lines it reads as they are, no `Transfer-Encoding` (a chunked body is not
  modelled), `Trailer` or `Pragma` (`fixPragmaCacheControl` would add a line), a `Connection` line only
  `close` (which `ReadResponse` deletes from its map: `dropConn`), and a `Content-Length` line with the body's length for a status with a body (none and no
  body for `204`/`304`), or, if `close`, no `Content-Length`.
* `badResp`: net/http's `400` answer (`net.rpc.badReqAns`), close-delimited.
* `srvKeys`: the keys whose values the server sets itself (`SpecPlan`'s); `hdrView hs hc`: the
  written header lines `hc` agree with the handler's `hs` at every other key; `hdrsOk hs`: header
  lines a handler may commit (lines the model writes as they are, none of the keys that change the
  framing, and `Pragma`: `Content-Length`, `Transfer-Encoding`, `Connection`, `Trailer`, `Pragma`).
* `pathUnder pfx p` (`SpecPlan`'s), `pathClean p` (`cleanPath(p) = p`: no empty, `.` or `..` segment
  but a trailing empty one), `notFoundBody` (`NotFound`'s body), `muxRedirect Ps p` (the mux's `307`).

## An address's protocol

* `HProto GF`: `SpecPlan`'s (`hreq`, `bodyPre`, `body`, `resp`), with `respEnd` (C6 below).
* `HttpProtoGS`: the name of the registry of connections (a ghost map from a connection to the name
  of its slots' mono-list), `httpRegInv` its invariant (every registered connection's dialer gave up
  its fresh token, as net/rpc's `regInv`); `httpConn cn γ` (persistent).
* `httpReqP P` (what a dialer writes): a prefix of the wire of its slots (lower bound of the
  connection's mono-list), each request with `□ P.hreq R τ`, `□ P.bodyPre R τ B'` for every prefix
  `B'` of its body, `□ P.body R τ B`.
* `httpRespP P` (what an acceptor writes): a prefix of the wire of its answers, the `i`-th answering
  the `i`-th slot: a handler's complete response (`ans ρ`: `respOk`, not close-delimited, with
  `hdrView hs ρ.hc`, `□ P.resp` and `□ P.respEnd` of the request at `ρ`'s status, `hs` and body), a
  chunked response's head (`chunked`: the handler wrote more than `2048` bytes before it returned,
  `□ P.resp` of them; anything may follow it), or net/http's `400` answer (`bad`, last).
* `protoLis la P` (persistent): a listener address `la` whose every address serves `P`
  (`lisProto la (httpReqP P) (httpRespP P)`), and the registry.

## A handler's view (`handlerOk`)

A handler is parametric in the representation of its response writer and body reader (so that the
server gets back its own state: S5 instantiates them with its invariants):
* `RespSt`: the writer's state: committed status (`none` before the commit), header lines, bytes
  written, and whether no write failed.
* `respOps w R τ P I`: the writer `w`'s methods over the representation `I`: `Header()` before the
  commit (the header map, `hdrOwn`, lent until given back), `WriteHeader(st)` before the commit
  (`200 ≤ st ≤ 999`, a status with a body, `hdrsOk`, `□ P.resp … st hs []`), `Write(b)` (committing
  `200` if uncommitted; `□ P.resp … (bs ++ ys)`; all written, or an error with a prefix written and
  the writer failed).
* `bodyOps rd R τ P S E`: the request body `rd` reads by `io.readerOk` with the state `S` and the
  errors' evidence `E`: every prefix read meets `P.bodyPre`, and `io.EOF` comes with `P.body`.
* `srvReq r R rd` (persistent): the request's `Method`, `URL` (the URL of `R.path` alone: the model's
  parse of a `reqPath`), `RequestURI` (`R.path`), `Host`, protocol (`HTTP/1.1`), `Header` (`hdrRO`,
  read-only, the lines of `R.hdr`), `Body` (`rd`) and `RemoteAddr`: what the handler and the
  `ServeMux` read. `reqMuxFields r`: the fields the `ServeMux` writes (`Pattern`, `pat`, `matches`),
  owned.
* `servePre`: what a run gets (`R.path` a `reqPath` under `pfx`, a `methOk` method, `srvReq`,
  `reqMuxFields`, `□ P.hreq R τ`, the writer
  and body reader at their start, the connection goroutine's thread token); `serveDone`: what it
  gives back (the token, the body reader's state, and the writer committed with `□ P.respEnd` of what
  it wrote, or failed, or a panic).
* `handlerOk h P pfx` (persistent): `h.ServeHTTP` of every run.

## Departures from S5's draft (for its ledger)

* C6 `HProto.respEnd`: knowledge of a handler's complete response (`serveDone` gives it; a client
  reading a body to its `EOF` learns it). The draft's `resp` is prefix knowledge only, so a client
  could not conclude that a body read to its end is the handler's whole body.
* Handlers are parametric in the writer's and the body reader's representation (`handlerOk`'s `∀ I S
  E`), and `serveDone` gives back the body reader's state: the server reads the body after the handler
  returns (`finishRequest` closes it).
* No `reqTicket` in `servePre` (no request here is replayed; S5 adds it: a handler proved without it
  meets S5's `handlerOk`).
* `httpReqP` asks for a slot's facts at the slot's first byte (a raw client knows its whole request);
  the draft's asks for `P.body` only at the body's end (the Transport's streamed bodies).
* Junk slots (a request the server rejects at its request line) and the close-delimited `400` answer.
-/
module

public import Net.Proof.net.http.MuxDefs
public import Net.Proof.net.http.WireDefs
public import GooseLang.Ext.Net.Proto
public import Perennial.Proof.io.Reader
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.GhostMap

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net

namespace net.http

/-! ## The protocol -/

/-- See the file header. -/
structure HProto (GF : BundledGFunctors) where
  hreq : HReq → GName → IProp GF
  bodyPre : HReq → GName → List w8 → IProp GF
  body : HReq → GName → List w8 → IProp GF
  resp : HReq → GName → w64 → List HdrLine → List w8 → IProp GF
  respEnd : HReq → GName → w64 → List HdrLine → List w8 → IProp GF

/-- The name of the registry of HTTP connections (see the file header). -/
class HttpProtoGS where
  reg : GName

def httpRegN : Namespace := nroot.@"net.http.reg"

/-- What an acceptor writes for one slot (see the file header). -/
inductive RespSlot where
  | ans (ρ : Resp)
  | chunked (st : w64) (reason : List w8) (hc : List HdrLine)
  | bad

/-- An answer's wire (a chunked answer's: its head). -/
def respSlotWire : RespSlot → List w8
  | .ans ρ => respWire ρ
  | .chunked st reason hc => respHeadWire st reason hc
  | .bad => respWire badResp

/-- The answers' wires in order. -/
def respsWire (Rs : List RespSlot) : List w8 := (Rs.map respSlotWire).flatten

/-- An answer that ends what is known of the stream (a chunked answer's body, or the `400` answer). -/
def RespSlot.last : RespSlot → Bool
  | .ans _ => false
  | .chunked .. => true
  | .bad => true

/-- `bs` is a prefix of the answers' wire, or extends it after a chunked answer; only the last
answer may end the stream. -/
def respsCover (Rs : List RespSlot) (bs : List w8) : Prop :=
  (∀ (i : Nat) (x : RespSlot), Rs[i]? = some x → x.last = true → i + 1 = Rs.length) ∧
  (bs <+: respsWire Rs ∨
    (∃ st reason hc, Rs.getLast? = some (.chunked st reason hc) ∧ respsWire Rs <+: bs))

section proto
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF] [π : NetProtoGS]
variable [hπ : HttpProtoGS]

include Gg

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- See the file header. -/
def httpRegInv : IProp GF :=
  iprop(∃ M : GMap Nat GName, ghostMapAuth hπ.reg 1 M ∗
    [∗map] cn ↦ _γ ∈ M, connFresh (Gg := Gg) cn false)

/-- Connection `cn`'s slots are the mono-list `γ` (persistent). -/
def httpConn (cn : Nat) (γ : GName) : IProp GF := ghostMapElem hπ.reg cn .discard γ

instance httpConn_persistent (cn : Nat) (γ : GName) : Persistent (httpConn (GF := GF) cn γ) := by
  unfold httpConn; infer_instance

/-- A slot's facts (see the file header). -/
def slotFacts (P : HProto GF) : ReqSlot → IProp GF
  | .inl (R, τ, B) => iprop(□ P.hreq R τ ∗ □ (∀ B', ⌜B' <+: B⌝ -∗ P.bodyPre R τ B') ∗ □ P.body R τ B)
  | .inr _ => iprop(True)

instance slotFacts_persistent (P : HProto GF) (s : ReqSlot) :
    Persistent (slotFacts P s) := by
  rcases s with ⟨R, τ, B⟩ | j <;> unfold slotFacts <;> infer_instance

/-- See the file header. -/
def httpReqP (P : HProto GF) : Net.Proto GF := fun cn bs =>
  iprop(∃ (γ : GName) (L : List ReqSlot), httpConn cn γ ∗ monoListLbOwn γ L ∗
    ⌜slotsOk L ∧ bs <+: slotsWire L⌝ ∗ [∗list] s ∈ L, slotFacts P s)

/-- The facts of the `i`-th answer `x`, of the slots `L` (see the file header). -/
def respFacts (P : HProto GF) (L : List ReqSlot) (i : Nat) : RespSlot → IProp GF
  | .ans ρ => iprop(∃ (R : HReq) (τ : GName) (B : List w8) (hs : List HdrLine),
      ⌜L[i]? = some (.inl (R, τ, B)) ∧ respOk ρ ∧ ρ.close = false ∧ hdrView hs ρ.hc⌝ ∗
      □ P.resp R τ ρ.st hs ρ.body ∗ □ P.respEnd R τ ρ.st hs ρ.body)
  | .chunked st _ hc => iprop(∃ (R : HReq) (τ : GName) (B : List w8) (hs : List HdrLine)
      (w : List w8), ⌜L[i]? = some (.inl (R, τ, B)) ∧ hdrView hs hc ∧ 2048 < w.length⌝ ∗
      □ P.resp R τ st hs w)
  | .bad => iprop(True)

instance respFacts_persistent (P : HProto GF) (L : List ReqSlot) (i : Nat) (x : RespSlot) :
    Persistent (respFacts P L i x) := by
  cases x <;> unfold respFacts <;> infer_instance

/-- See the file header. -/
def httpRespP (P : HProto GF) : Net.Proto GF := fun cn bs =>
  iprop(∃ Rs : List RespSlot, ⌜respsCover Rs bs⌝ ∗
    (⌜∀ x ∈ Rs, x = .bad⌝ ∨
      ∃ (γ : GName) (L : List ReqSlot), httpConn cn γ ∗ monoListLbOwn γ L ∗
        ⌜Rs.length ≤ L.length⌝ ∗ [∗list] i ↦ x ∈ Rs, respFacts P L i x))

/-- See the file header. -/
def protoLis (la : GoString) (P : HProto GF) : IProp GF :=
  iprop(lisProto (Gg := Gg) la (httpReqP P) (httpRespP P) ∗
    inv httpRegN (httpRegInv))

instance protoLis_persistent (la : GoString) (P : HProto GF) :
    Persistent (protoLis la P) := by
  unfold protoLis; infer_instance

end proto

/-! ## A handler's view -/

/-- See the file header: committed status, header lines, bytes written, no write failed. -/
abbrev RespSt := Option w64 × List HdrLine × List w8 × Bool

section handler
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A read-only header map `m` of the lines `hb` (persistent; see the file header). -/
def hdrRO (m : Loc) (hb : List HdrLine) : IProp GF :=
  iprop(∃ ms : GMap GoString GoSlice, m ↦$□ ms ∗
    ⌜∀ k, (ms !! k).isSome = decide (k ∈ hb.map Prod.fst)⌝ ∗
    [∗list] kv ∈ hb, ∃ s : GoSlice, ⌜ms !! kv.1 = some s⌝ ∗ s ↦*□ ([kv.2] : List GoString))

instance hdrRO_persistent (m : Loc) (hb : List HdrLine) : Persistent (hdrRO (GF := GF) m hb) := by
  unfold hdrRO; infer_instance

/-- See the file header. -/
def srvReq (r : Loc) (R : HReq) (rd : GoInterface) : IProp GF :=
  iprop(structFieldRef net.http.Request go!"Method" r ↦□ R.meth ∗
    (∃ u : Loc, structFieldRef net.http.Request go!"URL" r ↦□ u ∗
      u ↦□ { (_root_.Perennial.zero_val net.url.URL) with Path' := R.path }) ∗
    structFieldRef net.http.Request go!"RequestURI" r ↦□ R.path ∗
    structFieldRef net.http.Request go!"Host" r ↦□ R.host ∗
    structFieldRef net.http.Request go!"Proto" r ↦□ go!"HTTP/1.1" ∗
    structFieldRef net.http.Request go!"ProtoMajor" r ↦□ (W64 1) ∗
    structFieldRef net.http.Request go!"ProtoMinor" r ↦□ (W64 1) ∗
    (∃ hm : Loc, structFieldRef net.http.Request go!"Header" r ↦□ hm ∗ hdrRO hm R.hdr) ∗
    structFieldRef net.http.Request go!"Body" r ↦□ rd ∗
    (∃ ra : GoString, structFieldRef net.http.Request go!"RemoteAddr" r ↦□ ra))

/-- The request's fields a `ServeMux` writes (`findHandler`: `Pattern`, `pat`, `matches`), owned. -/
def reqMuxFields (r : Loc) : IProp GF :=
  iprop(∃ (pt : GoString) (pp : Loc) (ms : GoSlice),
    structFieldRef net.http.Request go!"Pattern" r ↦ pt ∗
    structFieldRef net.http.Request go!"pat" r ↦ pp ∗
    structFieldRef net.http.Request go!"matches" r ↦ ms)

instance srvReq_persistent (r : Loc) (R : HReq) (rd : GoInterface) :
    Persistent (srvReq (GF := GF) r R rd) := by
  unfold srvReq; infer_instance

/-- See the file header. -/
def respOps (w : GoInterface) (R : HReq) (τ : GName) (P : HProto GF) (I : RespSt → IProp GF) :
    IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜w = interface.ok i⌝ ∗
    (□ ∀ (hs : List HdrLine) (bs : List w8) (ok : Bool) (Φ : val → IProp GF),
      I (none, hs, bs, ok) -∗
      ▷ (∀ hm : Loc, hdrOwn hm hs -∗ (∀ hs', hdrOwn hm hs' -∗ I (none, hs', bs, ok)) -∗ Φ #hm) -∗
      WP (App (Val #(methods i.ty go!"Header" i.v)) (Val #())) {{ Φ }}) ∗
    (□ ∀ (hs : List HdrLine) (bs : List w8) (ok : Bool) (st : w64) (Φ : val → IProp GF),
      ⌜200 ≤ uint.nat st ∧ uint.nat st ≤ 999 ∧ bodyAllowed st = true ∧ hdrsOk hs⌝ -∗
      I (none, hs, bs, ok) -∗ □ P.resp R τ st hs [] -∗
      ▷ (I (some st, hs, bs, ok) -∗ Φ #()) -∗
      WP (App (Val #(methods i.ty go!"WriteHeader" i.v)) (Val #st)) {{ Φ }}) ∗
    (□ ∀ (c : Option w64) (hs : List HdrLine) (bs : List w8) (ok : Bool) (b : GoSlice)
        (ys : List w8) (dq : DFrac) (Φ : val → IProp GF),
      ⌜c = none → hdrsOk hs⌝ -∗ I (c, hs, bs, ok) -∗ b ↦*{dq} ys -∗
      □ P.resp R τ (c.getD (W64 200)) hs (bs ++ ys) -∗
      ▷ (∀ (n : w64) (err : GoInterface), b ↦*{dq} ys -∗ ⌜uint.nat n ≤ ys.length⌝ -∗
          ((⌜err = interface.nil ∧ uint.nat n = ys.length⌝ ∗
              I (some (c.getD (W64 200)), hs, bs ++ ys, ok)) ∨
           (⌜err ≠ interface.nil⌝ ∗
              I (some (c.getD (W64 200)), hs, bs ++ ys.take (uint.nat n), false))) -∗
          Φ (PairV #n #err)) -∗
      WP (App (Val #(methods i.ty go!"Write" i.v)) (Val #b)) {{ Φ }}))

instance respOps_persistent (w : GoInterface) (R : HReq) (τ : GName) (P : HProto GF)
    (I : RespSt → IProp GF) : Persistent (respOps (GF := GF) w R τ P I) := by
  unfold respOps; infer_instance

/-- See the file header. -/
def bodyOps (rd : GoInterface) (R : HReq) (τ : GName) (P : HProto GF) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) : IProp GF :=
  iprop(∃ ri : GoInterfaceOk, ⌜rd = interface.ok ri⌝ ∗ io.readerOk ri (fun _ _ => True) S E ∗
    □ (∀ (r : List w8) (e : GoInterface), E r e -∗
      □ P.bodyPre R τ r ∗ (globalAddr io.EOF ↦□ e -∗ □ P.body R τ r)))

instance bodyOps_persistent (rd : GoInterface) (R : HReq) (τ : GName) (P : HProto GF)
    (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF) :
    Persistent (bodyOps (GF := GF) rd R τ P S E) := by
  unfold bodyOps; infer_instance

/-- See the file header. -/
def servePre (P : HProto GF) (pfx : GoString) (w : GoInterface) (r : Loc) (R : HReq) (τ : GName)
    (rd : GoInterface) (I : RespSt → IProp GF) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) : IProp GF :=
  iprop(⌜reqPath R.path ∧ methOk R.meth ∧ pathUnder pfx R.path⌝ ∗ srvReq r R rd ∗ reqMuxFields r ∗
    □ P.hreq R τ ∗
    respOps w R τ P I ∗ I (none, [], [], true) ∗ bodyOps rd R τ P S E ∗ S [] ∗ threadTok)

/-- See the file header. -/
def serveDone (P : HProto GF) (R : HReq) (τ : GName) (I : RespSt → IProp GF)
    (S : List w8 → IProp GF) (v : val) : IProp GF :=
  iprop(threadTok ∗ (∃ r, S r) ∗
    ((∃ st hs bs, I (some st, hs, bs, true) ∗ □ P.respEnd R τ st hs bs) ∨
     (∃ st hs bs, I (some st, hs, bs, false)) ∨
     (⌜v.isPanic = true⌝ ∗ ∃ s, I s)))

/-- See the file header. -/
def handlerOk (h : GoInterface) (P : HProto GF) (pfx : GoString) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜h = interface.ok i⌝ ∗
    □ ∀ (w : GoInterface) (r : Loc) (R : HReq) (τ : GName) (rd : GoInterface)
        (I : RespSt → IProp GF) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF),
      ⌜∀ x, S x ⊢ ⌜x.length < 2 ^ 60⌝⌝ -∗ servePre P pfx w r R τ rd I S E -∗
      WP (App (App (Val #(methods i.ty go!"ServeHTTP" i.v)) (Val #w)) (Val #r))
        {{ v, serveDone P R τ I S v }})

instance handlerOk_persistent (h : GoInterface) (P : HProto GF) (pfx : GoString) :
    Persistent (handlerOk (GF := GF) h P pfx) := by
  unfold handlerOk; infer_instance

/-- `ServeMux`'s redirect of a request for `p` (Go 1.22's matcher, `findHandler`): `p` not clean
(`cleanPath`), or not a pattern, not ending in `/`, and `p ++ "/"` a pattern (`matchOrRedirect`; even
when a shorter subtree pattern routes `p`). Both answer `307` (`StatusTemporaryRedirect`). -/
def muxRedirect (Ps : List GoString) (p : GoString) : Prop :=
  ¬ pathClean p ∨ (p ∉ Ps ∧ p.getLast? ≠ some (W8 47) ∧ p ++ [W8 47] ∈ Ps)

/-- What a mux with the routes `L` needs of a protocol for the requests it answers itself
(`ServeMux.ServeHTTP.spec`), for those a client sent (`P.hreq`): a `307` to a request it redirects
(`muxRedirect`); a `404` with `NotFound`'s body to one it does not redirect and no pattern routes
(`pathUnder`). -/
def muxNoRoute (P : HProto GF) (L : List (GoString × GoInterface)) : Prop :=
  ∀ (R : HReq) (τ : GName), reqPath R.path →
    (muxRedirect (L.map Prod.fst) R.path →
      ∀ (hs : List HdrLine) (w : List w8),
        (P.hreq R τ ⊢ □ P.resp R τ (W64 307) hs w) ∧ (P.hreq R τ ⊢ □ P.respEnd R τ (W64 307) hs w)) ∧
    (¬ muxRedirect (L.map Prod.fst) R.path → (∀ ph ∈ L, ¬ pathUnder ph.1 R.path) →
      (∀ (hs : List HdrLine) (w : List w8), w <+: notFoundBody →
        (P.hreq R τ ⊢ □ P.resp R τ (W64 404) hs w)) ∧
      ∀ hs : List HdrLine, (P.hreq R τ ⊢ □ P.respEnd R τ (W64 404) hs notFoundBody))

end handler

end net.http
end Perennial
