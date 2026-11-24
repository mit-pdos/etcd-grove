/-
`http.ReadResponse(b, req)` on a `CONNECT` answer (net/rpc's `DialHTTPPath`, the one caller here):
`b` a `*bufio.Reader` (`bufio.ownReader`, nothing delivered yet) of a stream reader `ri` that
makes progress (`io.readerStreamNE ri S E`: no `(0, nil)` read, so bufio never gives up with
`io.ErrNoProgress` and then reads on) whose bytes are, as long as it is read, a prefix of net/rpc's answer
`connectAns` (`"HTTP/1.0 200 Connected to Go RPC\n\n"`) or of net/http's server's `400` answer
`badReqAns` (to a request it could not read: `"HTTP/1.1 400 Bad Request"`, a `Content-Type` and a
`Connection: close` header line, its body), and that delivers nothing after an error
(the law over `E` and `S`: after an error at `r`, the stream stays at `r`; a connection's, by the
net extension's sticky read errors, D1 v3.5), whose errors have an `Error()` (`errMsgOk`), `req` the
request `{Method: "CONNECT"}`. It returns an error (non-nil, with an `Error()`: the stream's,
`io.ErrUnexpectedEOF`, a malformed line's `fmt.Errorf`, a header's `textproto.ProtocolError`), or a response whose `Status` is either not
`"200 Connected to Go RPC"` (the `400` answer's is `"400 Bad Request"`) or is it, and then the reader
has delivered exactly `connectAns` (the status line and the empty header block, each up to its `"\n"`:
a line cut by an error does not parse as a whole one, since nothing follows the error). The model's
head parser (`textproto_model.go`) and `readTransfer` (the answer's body, read to the connection's
end, is not read here). `httpEnv` (`Net/Proof/net/http/Defs.lean`) is the package state the parse
reads. Proved in `Net/Proof/net/http/ReadResponse.lean`.
-/
module

public import Net.Proof.net.http.RequestDefs
public import Proof.io.ReaderStreamNE

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
      (□ ∀ (r : List w8) (err : GoInterface), E r err -∗ errMsgOk err) ∗
      req ↦ rq ∗ ⌜rq.Method' = go!"CONNECT"⌝ }}
    (App (App (Val (@! net.http.ReadResponse)) (Val #b)) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err ≠ interface.nil⌝ ∗ errMsgOk err) ∨
      (⌜err = interface.nil⌝ ∗ ∃ rv : net.http.Response, resp ↦ rv ∗
        (⌜rv.Status' ≠ net.rpc.connectedStatus⌝ ∨
          ⌜rv.Status' = net.rpc.connectedStatus⌝ ∗
            EtcdGrove.bufio.ownReader b ri S E net.rpc.connectAns)) }}

end spec

end net.http
end Perennial
