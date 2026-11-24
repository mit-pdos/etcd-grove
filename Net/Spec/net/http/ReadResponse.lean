/-
`http.ReadResponse(b, req)` on a `CONNECT` answer (net/rpc's `DialHTTPPath`, the one caller here):
`b` a `*bufio.Reader` (`bufio.ownReader`, nothing delivered yet) of a stream reader `ri` that
makes progress (`io.readerStreamNE ri S E`: no `(0, nil)` read, so bufio never gives up with
`io.ErrNoProgress` and then reads on) whose bytes are, as long as it is read, a prefix of net/rpc's answer
`connectAns` (`"HTTP/1.0 200 Connected to Go RPC\n\n"`) or of net/http's server's `400` answer
`badReqAns` (to a request it could not read: `"HTTP/1.1 400 Bad Request"`, a `Content-Type` and a
`Connection: close` header line, its body), and that delivers nothing after an error
(the law over `E` and `S`: after an error at `r`, the stream stays at `r`; a connection's, by the
net extension's sticky read errors, D1 v3.5), `req` the request `{Method: "CONNECT"}`. It returns an error (some error, non-nil:
the stream's, `io.ErrUnexpectedEOF`, a malformed line's), or a response whose `Status` is either not
`"200 Connected to Go RPC"` (the `400` answer's is `"400 Bad Request"`) or is it, and then the reader
has delivered exactly `connectAns` (the status line and the empty header block, each up to its `"\n"`:
a line cut by an error does not parse as a whole one, since nothing follows the error). The model's
head parser (`textproto_model.go`) and `readTransfer` (the answer's body, read to the connection's
end, is not read here). `httpEnv` (`Net/Proof/net/http/Defs.lean`) is the package state the parse
reads. Proved in `Net/Proof/net/http/ReadResponse.lean`.

`http.ReadResponse(b, nil)` on a stream of responses (`ReadResponse.spec_resp`; httpdriver,
2026-11-24): `b` a `*bufio.Reader` that has delivered `D` (`bufio.ownReader`) of a stream reader `ri`
that makes progress (`io.readerStreamNE ri S E`), whose bytes past `D` are, as long as it is read,
nothing yet, or a prefix of the wire of a response `ρ` the model reads as written (`respOk`,
`ProtoDefs.lean`: no chunked body) or, for one delimited by its `Content-Length`, that wire followed by
more, with the caller's persistent knowledge `Q ρ` of it (the law over `S`); and that delivers nothing
after an error (the law over `E` and `S`, as the `CONNECT` spec's). It returns an error (with the
reader), or a response with `ρ`'s status, its header lines (`hdrOwn`, the client's, without a
`Connection: close` line, `dropConn`) and a body reader
(`io.readerOk`, by the contract `SB`, `EB` it gives, from `SB []`, shorter than `2 ^ 60` bytes): an
`io.EOF` of it comes with `Q ρ` of a response `ρ` with that head whose body is the bytes read (one
delimited by its `Content-Length`) or extends them (a close-delimited one, read to the stream's end),
and gives back the reader, past the response (`D ++` its head `++` the body read), for the next
`ReadResponse` on the connection. The model's head parser, `readTransfer` and its body reader
(`body` over `io.LimitReader`, or over the reader itself to its end). Interim trust-boundary axiom
(`Net/Proof/net/http/ReadResponse.lean`), retired by phase 7's S5 (the client half: `ReadResponse` on
general heads).
-/
module

public import Net.Proof.net.http.Defs
public import Proof.io.ReaderStreamNE
public import Net.Proof.net.http.ProtoDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- See the file header. -/
abbrev ReadResponse.spec : Prop :=
  ∀ (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (req : Loc) (rq : net.http.Request),
  {{ httpEnv ∗ EtcdGrove.io.readerStreamNE ri S E ∗ EtcdGrove.bufio.ownReader b ri S E [] ∗
      (□ ∀ r, S r -∗ ⌜r <+: net.rpc.connectAns ∨ r <+: net.rpc.badReqAns⌝) ∗
      (□ ∀ (r r' : List w8) (err : GoInterface), E r err -∗ S r' -∗ ⌜r <+: r' → r' = r⌝) ∗
      req ↦ rq ∗ ⌜rq.Method' = go!"CONNECT"⌝ }}
    (App (App (Val (@! net.http.ReadResponse)) (Val #b)) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err ≠ interface.nil⌝) ∨
      (⌜err = interface.nil⌝ ∗ ∃ rv : net.http.Response, resp ↦ rv ∗
        (⌜rv.Status' ≠ net.rpc.connectedStatus⌝ ∨
          ⌜rv.Status' = net.rpc.connectedStatus⌝ ∗
            EtcdGrove.bufio.ownReader b ri S E net.rpc.connectAns)) }}

/-- See the file header. -/
abbrev ReadResponse.spec_resp : Prop :=
  ∀ (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (D : List w8) (Q : Resp → IProp GF) (eof : GoInterface),
  {{ httpEnv ∗ globalAddr io.EOF ↦□ eof ∗ EtcdGrove.io.readerStreamNE ri S E ∗
      EtcdGrove.bufio.ownReader b ri S E D ∗
      (□ ∀ r, S r -∗ ⌜r <+: D⌝ ∨ ∃ ρ : Resp, ⌜respOk ρ ∧
          (r <+: D ++ respWire ρ ∨ (ρ.close = false ∧ D ++ respWire ρ <+: r))⌝ ∗ □ Q ρ) ∗
      (□ ∀ (r r' : List w8) (err : GoInterface), E r err -∗ S r' -∗ ⌜r <+: r' → r' = r⌝) }}
    (App (App (Val (@! net.http.ReadResponse)) (Val #b)) (Val #(null : Loc)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err ≠ interface.nil⌝ ∗ ∃ D', EtcdGrove.bufio.ownReader b ri S E D') ∨
      (⌜err = interface.nil⌝ ∗ ∃ (rv : net.http.Response) (st : w64) (reason : List w8)
          (hc : List HdrLine) (cl : Bool) (hm : Loc) (bi : GoInterfaceOk)
          (SB : List w8 → IProp GF) (EB : List w8 → GoInterface → IProp GF),
        resp ↦ rv ∗ ⌜rv.StatusCode' = st ∧ rv.Header' = hm ∧ rv.Body' = interface.ok bi⌝ ∗
        hdrOwn hm (dropConn hc) ∗ io.readerOk bi (fun _ _ => True) SB EB ∗ SB [] ∗
        ⌜∀ x, SB x ⊢ iprop(⌜x.length < 2 ^ 60⌝)⌝ ∗
        (□ ∀ (x : List w8) (e : GoInterface), EB x e -∗ ⌜e = eof⌝ -∗
          ∃ ρ : Resp, ⌜ρ.st = st ∧ ρ.reason = reason ∧ ρ.hc = hc ∧ ρ.close = cl ∧
            (if cl then x <+: ρ.body else x = ρ.body)⌝ ∗ □ Q ρ) ∗
        (∀ (x : List w8) (e : GoInterface), SB x -∗ □ EB x e -∗ ⌜e = eof⌝ -∗
          EtcdGrove.bufio.ownReader b ri S E (D ++ respHeadWire st reason hc ++ x))) }}

end spec

end net.http
end Perennial
