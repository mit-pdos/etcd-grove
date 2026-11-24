/-
**The HTTP boundary's axioms** (rafthttp stage 4e, 2026-10-23; D38a, D38b, D38c): the statements
of `Proof/net/http/Boundary.lean` the proofs use, assumed, and the registration of an address's
protocol. Lean-first. Each is a fact about Go's `net/http`, `io` and `bytes` (read against the
statement's docstring in `Boundary.lean`); the specs not listed (`respRead_spec`, `HeaderGet_spec`)
stay statements until a proof uses them. (prove-http3, 2026-11-21) `ReadFull_stream_ok` is proved
here over Perennial's `io.ReadFull` and `bodyStreamRead_ok`; `Header.Set` and `Get`'s
(`HeaderSet_ok`, `HeaderSetPtr_ok`, `HeaderGetPtr_ok`, `HeaderGetOwnPtr_ok`) are theorems of
`Proof/net/http/Proved.lean`, over net/http's and net/textproto's code.

Soundness of the specs stated for any `HttpNet` (`Error_ok`, ...): their resources
(`respWriter H`, `respReader H`) come only from `Serve` and `RoundTrip`, which need an address's
registered protocol (`httpListenerAt`, `httpProtoAt`): a client and the server of one address
agree on its protocol (the file header of `Boundary.lean`).
-/
module

public import Proof.net.http.Boundary
public import Proof.net.http.Proved
public import Perennial.Proof.io.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace http

open Iris Iris.BI

section axioms
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Reservation** (D39a, 2026-10-23; D38c's registration, split): the right to fix an
address's protocol (`httpProtoFree a`, once per address from program start) fixes it, before the
address's listener exists: a client may then send to the address (`RoundTrip` needs
`httpProtoAt`; before the listener is bound the connection is refused, an error the spec allows).
True of a model with a global ghost map from addresses to saved protocols whose entry for `a` is
set once, with the exclusive `httpProtoFree a`. (http-boundary-fix, 2026-11-14) Of a protocol
that admits the server's own answers (`Proto.srvOk`): `RoundTrip`'s post promises the protocol's
`resp` of whatever status it returns, which may be one Go's server made running no handler (`431`
for headers over `MaxHeaderBytes`, `examples/premisefix/httpsrvstatus`). -/
axiom reserve (a : GoString) (P : Proto GF) (hP : P.srvOk) :
  ⊢ httpProtoFree (GF := GF) a ==∗ httpProtoAt a P ∗ httpProtoOwn a P

/-- **Registration** (D38c, D39a): the address's listener, with the right to serve it with the
address's reserved protocol, serves it with that protocol (the model: the listener bound once,
`net.Listen` consuming `netAddrFree a`; the protocol the ghost map's entry for `a`).

(2026-11-24) It also consumes `netAddrLeft a`, what sets `a`'s net protocols (`net.Listen`'s, beside the
listener): an address served by net/http speaks HTTP, so no program may both register `a` and give `a` net
protocols of its own. Without it a program listened at `a`, set `a`'s protocols from `netAddrLeft` to trivial
ones (`addr_set_proto_tok`), wrote raw bytes to `a` (`dial_au`, `writeP`), and `Serve_ok` promised the
handler `(H.proto a).req R` of a request the protocol excludes (Go panics: `examples/axiomcx/httpaddrleft/`,
`notes/axiom-review/http-register-addrleft.md`). As `bridge.New`'s fix (`notes/decisions.md`). -/
axiom register (l : GoInterface) (a : GoString) (P : Proto GF) :
  ⊢ netListenerAt (GF := GF) l a -∗ netAddrLeft (GF := GF) a -∗ httpProtoOwn a P ==∗ httpListenerAt l a P

/-- (rafthttp stage 6d, 2026-10-24: the examples' members serving their raft handler) `http.Serve`
of a registered listener with a handler of its address's protocol (`Serve_spec`): it serves each
request on its own goroutine, lending it one of `httpProcSlots` copies of the handler's resource,
and returns an error if it returns. It replaces D21 M5's `net/http.Serve` axiom (on the opaque
`raftHandlerOf`): what that axiom asserted of rafthttp's handlers is now proved (`Transport.Handler`,
`handlerOk`), and the deployment fact (the address served by its member's handler) is the
registration's (`register`) and the directory's (`netOwner`). -/
axiom Serve_ok (H : HttpNet GF) : Serve_spec H

/-- A request body's `Read` (`bodyRead_spec`): Go's server body reader of a request's
`Content-Length` or chunked body; a body cut short is `io.ErrUnexpectedEOF`, not `EOF`. -/
axiom bodyRead_ok : bodyRead_spec (GF := GF)

/-- (D42, rafthttp stage 7e: the snapshot handler's) A streamed request body's `Read`
(`bodyStreamRead_spec`): Go's server reader of a chunked body, whose bytes are a prefix of what the
client's reader yielded, `EOF` only where its stream ended (the file header's physical assumption,
`Boundary.lean`). -/
axiom bodyStreamRead_ok : bodyStreamRead_spec (GF := GF)


/-- `ResponseWriter.WriteHeader` of a final status (`respWriteHeader_spec`). -/
axiom respWriteHeader_ok (H : HttpNet GF) : respWriteHeader_spec H

/-- `ResponseWriter.Header()` before the commit (`RespHeader_spec`): the writer's header map, lent. -/
axiom RespHeader_ok : RespHeader_spec (GF := GF)

/-- `io.ReadAll` of a prefix reader (`ReadAll_spec`): it reads until `EOF` or an error. -/
axiom ReadAll_ok : ReadAll_spec (GF := GF)

/-- `Flusher.Flush` of a response writer (`Flush_spec`). -/
axiom Flush_ok (H : HttpNet GF) : Flush_spec H

/-- `http.Error` (`Error_spec`): its headers, `WriteHeader(code)`, `fmt.Fprintln(w, msg)`. -/
axiom Error_ok (H : HttpNet GF) : Error_spec H

/-- `Request.WithContext` (`WithContext_spec`): a shallow copy with the context. -/
axiom WithContext_ok : WithContext_spec (GF := GF)

/-- `io.ReadAll` of a response body (`ReadAll_resp_spec`). -/
axiom ReadAll_resp_ok (H : HttpNet GF) : ReadAll_resp_spec H

/-- A response body's reader gives up its guarantee (`respReadAny_of_spec`; stage 7d). -/
axiom respReadAny_of_ok (H : HttpNet GF) : respReadAny_of_spec H

/-- `io.ReadAll` of a response body read without a guarantee (`ReadAll_any_spec`; stage 7d). -/
axiom ReadAll_any_ok : ReadAll_any_spec (GF := GF)

/-- A response body's `Close` (`RespClose_spec`). -/
axiom RespClose_ok (H : HttpNet GF) : RespClose_spec H

/-- (2026-10-23, stage 5e-3: the stream reader's `dial`) `http.NewRequest` (`NewRequest_spec`). -/
axiom NewRequest_ok : NewRequest_spec (GF := GF)

/-- (stage 5e-3) `url.URL.String` of a plain URL (`URLString_spec`). -/
axiom URLString_ok : URLString_spec (GF := GF)

/-- (rafthttp stage 6e) a request's `URL` field, read-only (`reqURL_spec`). -/
axiom reqURL_ok : reqURL_spec (GF := GF)

/-- (rafthttp stage 6e) `url.URL.String` of any URL (`URLStringAny_spec`; restated 2026-10-27, D22
J-T: a URL of only `http` and a plain host renders as `http://` and the host). -/
axiom URLStringAny_ok : URLStringAny_spec (GF := GF)

/-- (2026-10-23, stage 5f: the stream writer's) `ResponseWriter.Write` (`respWrite_spec`): writes a
prefix of its bytes, all unless it fails (`io.Writer`'s contract). -/
axiom respWrite_ok (H : HttpNet GF) : respWrite_spec H

/-- (stage 5f: the stream reader's) `io.ReadFull` of a response body (`ReadFull_resp_spec`). -/
axiom ReadFull_resp_ok (H : HttpNet GF) : ReadFull_resp_spec H

/-- (stage 5f: the stream reader's `stop`) a response body's `Close` from any goroutine
(`RespCloseAny_spec`; Go's body supports a `Close` concurrent with a `Read`). -/
axiom RespCloseAny_ok : RespCloseAny_spec (GF := GF)

/-- (stage 6c: `rafthttp.Transport.Stop`) closing a `*http.Transport` round tripper's idle
connections (`CloseIdleConnections_spec`). -/
axiom CloseIdleConnections_ok (H : HttpNet GF) : CloseIdleConnections_spec H

/-- (stage 6c: `rafthttp.Transport.Handler`) `http.NewServeMux()` (`NewServeMux_spec`). -/
axiom NewServeMux_ok : NewServeMux_spec (GF := GF)

/-- (stage 6c) `m.Handle(pat, h)` of a pattern not yet registered (`Handle_spec`). -/
axiom Handle_ok : Handle_spec (GF := GF)

/-- (stage 6c) a built mux's dispatch (`mux_handlerOk_spec`). -/
axiom mux_handlerOk_ok (H : HttpNet GF) : mux_handlerOk_spec H

end axioms

section readFull
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [io_sem : _root_.Perennial.io.Assumptions] [errors_sem : _root_.Perennial.errors.Assumptions]

open Iris.ProofMode

/-- (D42, stage 7e: the snapshot handler's envelope) `io.ReadFull` of a streamed request body
(`ReadFull_stream_spec`): Perennial's `io.ReadFull` (prove-http3, 2026-11-21; until then an axiom)
over the body's `Read`s (`bodyStreamRead_ok`), the reader's contract `io.readerOk` with its
errors' `errStrOk`; `io.ErrUnexpectedEOF` is an `errors.New` error. -/
theorem ReadFull_stream_ok : ReadFull_stream_spec (GF := GF) := by
  intro rd Pre Φs r p xs
  iintro %Φ !> ⟨#Hpkg, Hs, Hp⟩ HΦ
  unfold bodyStream
  icases Hs with ⟨Hs, %Hpre⟩
  cases rd with
  | nil => exact absurd rfl Hpre.2
  | ok ri =>
  ihave Hi := _root_.Perennial.io.isInit_access $$ Hpkg
  unfold _root_.Perennial.io.isInit
  iNamed Hi
  iunfold _root_.Perennial.errors.newVar at HEOF HErrUnexpectedEOF
  icases HEOF with ⟨%xe, #He, -⟩
  icases HErrUnexpectedEOF with ⟨%xu, #Hu, #_, #HuM⟩
  ihave #Hrd : _root_.Perennial.io.readerOk ri (fun _ _ => True)
      (bodyStream (GoInterface.ok ri) Pre Φs) (fun _ e => errStrOk e) $$ []
  · unfold _root_.Perennial.io.readerOk
    iintro !> %r' %p' %xs' %Ψ !> ⟨-, Hs', Hp'⟩ HΨ
    ihave %Hl0 := ownSlice_len _ _ _ $$ Hp'
    iapply (bodyStreamRead_ok _ ri Pre Φs r' p' xs' _ rfl) $$ [$Hs' $Hp']
    · unfold ioEOF; iexact He
    iintro !> %n %err ⟨%ys, %Hy, Hp', Hs', #Herr, %Hpt⟩
    ihave %Hl1 := ownSlice_len _ _ _ $$ Hp'
    iapply HΨ
    iexists ys
    iframe Hp' Hs'
    isplitr
    · ipureintro
      refine ⟨Hy.1, ?_⟩
      have := Hl1.1
      rw [List.length_append, List.length_drop, ← Hl0.1] at this
      omega
    isplitr
    · unfold _root_.Perennial.io.errAt
      cases err with
      | nil => ileft; ipureintro; rfl
      | ok ei => iright; imodintro; iexact Herr
    · ipureintro; exact Hpt
  wp_apply (_root_.Perennial.io.wp_ReadFull ri (fun _ _ => True) (bodyStream (GoInterface.ok ri) Pre Φs)
      (fun _ e => errStrOk e) r p xs _ _) $$ [Hs Hp]
    as %n %err ⟨%ys, %Hys, Hp, Hs, #Hres⟩
  · iframe Hrd He Hu Hp
    isplitr
    · ipureintro; intro _ _; trivial
    unfold bodyStream; iframe Hs; ipureintro; exact Hpre
  unfold bodyStream
  icases Hs with ⟨Hs, %Hpre'⟩
  iapply HΦ
  iexists ys
  iframe Hp
  unfold _root_.Perennial.io.readFullRes
  icases Hres with (%Hok | ⟨%e, %He', #HE⟩)
  · iframe Hs
    isplitr
    · ipureintro; exact ⟨Hys.1, Hys.2, fun _ => Hok.1, Hpre'.1⟩
    isplitr
    · ipureintro; exact Hpre'
    rw [Hok.2]; iapply errStrOk_nil
  · have hnn : err ≠ GoInterface.nil := by
      by_cases h : e = interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #xe ∧ ys ≠ []
      · rw [He'.2.2.1 h]; intro h'; cases h'
      · rw [He'.2.2.2 h]; exact He'.2.1
    iframe Hs
    isplitr
    · ipureintro; exact ⟨Hys.1, Hys.2, fun h => absurd h hnn, Hpre'.1⟩
    isplitr
    · ipureintro; exact Hpre'
    by_cases h : e = interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #xe ∧ ys ≠ []
    · rw [He'.2.2.1 h]
      iapply errorString_errStrOk xu go!"unexpected EOF" $$ HuM
    · rw [He'.2.2.2 h]
      iexact HE

end readFull

end http
end EtcdGrove
end Perennial
