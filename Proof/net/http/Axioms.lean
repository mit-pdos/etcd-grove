/-
**The HTTP boundary's axioms** (rafthttp stage 4e, 2026-10-23; D33a, D33b, D33c): the statements
of `Proof/net/http/Boundary.lean` the proofs use, assumed, and the registration of an address's
protocol. Lean-first. Each is a fact about Go's `net/http`, `io` and `bytes` (read against the
statement's docstring in `Boundary.lean`); the specs not listed (`Serve_spec`, `respRead_spec`,
`HeaderGet_spec`, the mux's) stay statements until a proof uses them.

Soundness of the specs stated for any `HttpNet` (`Error_ok`, ...): their resources
(`respWriter H`, `respReader H`) come only from `Serve` and `RoundTrip`, which need an address's
registered protocol (`httpListenerAt`, `httpProtoAt`): a client and the server of one address
agree on its protocol (the file header of `Boundary.lean`).
-/
module

public import Proof.net.http.Boundary

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace http

open Iris Iris.BI

section axioms
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Reservation** (D34a, 2026-10-23; D33c's registration, split): the right to fix an
address's protocol (`httpProtoFree a`, once per address from program start) fixes it, before the
address's listener exists: a client may then send to the address (`RoundTrip` needs
`httpProtoAt`; before the listener is bound the connection is refused, an error the spec allows).
True of a model with a global ghost map from addresses to saved protocols whose entry for `a` is
set once, with the exclusive `httpProtoFree a`. -/
axiom reserve (a : GoString) (P : Proto GF) :
  ⊢ httpProtoFree (GF := GF) a ==∗ httpProtoAt a P ∗ httpProtoOwn a P

/-- **Registration** (D33c, D34a): the address's listener, with the right to serve it with the
address's reserved protocol, serves it with that protocol (the model: the listener bound once,
`net.Listen` consuming `netAddrFree a`; the protocol the ghost map's entry for `a`). -/
axiom register (l : GoInterface) (a : GoString) (P : Proto GF) :
  ⊢ netListenerAt (GF := GF) l a -∗ httpProtoOwn a P ==∗ httpListenerAt l a P

/-- A request body's `Read` (`bodyRead_spec`): Go's server body reader of a request's
`Content-Length` or chunked body; a body cut short is `io.ErrUnexpectedEOF`, not `EOF`. -/
axiom bodyRead_ok : bodyRead_spec (GF := GF)

/-- `ResponseWriter.WriteHeader` of a final status (`respWriteHeader_spec`). -/
axiom respWriteHeader_ok (H : HttpNet GF) : respWriteHeader_spec H

/-- `Header.Set` (`HeaderSet_spec`): `textproto.MIMEHeader.Set` of the canonical key. -/
axiom HeaderSet_ok : HeaderSet_spec (GF := GF)

/-- `ResponseWriter.Header()` before the commit (`RespHeader_spec`): the writer's header map, lent. -/
axiom RespHeader_ok : RespHeader_spec (GF := GF)

/-- `Header.Get` through a pointer (`HeaderGetPtr_spec`): the map's `Get`. -/
axiom HeaderGetPtr_ok : HeaderGetPtr_spec (GF := GF)

/-- `Header.Set` through a pointer (`HeaderSetPtr_spec`): the map's `Set`. (Stage 5e-3.) -/
axiom HeaderSetPtr_ok : HeaderSetPtr_spec (GF := GF)

/-- `io.ReadAll` of a prefix reader (`ReadAll_spec`): it reads until `EOF` or an error. -/
axiom ReadAll_ok : ReadAll_spec (GF := GF)

/-- `Flusher.Flush` of a response writer (`Flush_spec`). -/
axiom Flush_ok (H : HttpNet GF) : Flush_spec H

/-- `http.Error` (`Error_spec`): its headers, `WriteHeader(code)`, `fmt.Fprintln(w, msg)`. -/
axiom Error_ok (H : HttpNet GF) : Error_spec H

/-- `bytes.NewBuffer` (`NewBuffer_spec`). -/
axiom NewBuffer_ok : NewBuffer_spec (GF := GF)

/-- `Request.WithContext` (`WithContext_spec`): a shallow copy with the context. -/
axiom WithContext_ok : WithContext_spec (GF := GF)

/-- `io.ReadAll` of a response body (`ReadAll_resp_spec`). -/
axiom ReadAll_resp_ok (H : HttpNet GF) : ReadAll_resp_spec H

/-- A response body's `Close` (`RespClose_spec`). -/
axiom RespClose_ok (H : HttpNet GF) : RespClose_spec H

/-- (2026-10-23, stage 5e-3: the stream reader's `dial`) `http.NewRequest` (`NewRequest_spec`). -/
axiom NewRequest_ok : NewRequest_spec (GF := GF)

/-- (stage 5e-3) `url.URL.String` of a plain URL (`URLString_spec`). -/
axiom URLString_ok : URLString_spec (GF := GF)

/-- (2026-10-23, stage 5f: the stream writer's) `ResponseWriter.Write` (`respWrite_spec`): writes a
prefix of its bytes, all unless it fails (`io.Writer`'s contract). -/
axiom respWrite_ok (H : HttpNet GF) : respWrite_spec H

/-- (stage 5f: the stream reader's) `io.ReadFull` of a response body (`ReadFull_resp_spec`). -/
axiom ReadFull_resp_ok (H : HttpNet GF) : ReadFull_resp_spec H

/-- (stage 5f: the stream reader's `stop`) a response body's `Close` from any goroutine
(`RespCloseAny_spec`; Go's body supports a `Close` concurrent with a `Read`). -/
axiom RespCloseAny_ok : RespCloseAny_spec (GF := GF)

/-- (stage 5e-3) `nil` is a reader of no bytes, an empty request body (`readerHas`'s docstring,
`NewRequest`'s `nil` body). -/
axiom readerHas_nil : ⊢ readerHas (GF := GF) GoInterface.nil []

end axioms

end http
end EtcdGrove
end Perennial
