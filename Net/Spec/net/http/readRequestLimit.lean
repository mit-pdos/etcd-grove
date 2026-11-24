/-
`readRequestLimit(b, maxHeaders)` (the model's `request.go`: the request line and the header block
read by the model's `modelReadLine` and `modelReadMIMEHeader`) on net/rpc's `CONNECT` request: `b` a
`*bufio.Reader` (`bufio.ownReader`, nothing delivered yet) of a stream reader that makes progress
(`io.readerStreamNE ri S E`), whose bytes are, as long as it is read, a prefix of `connectReq path`
(`"CONNECT " ++ path ++ " HTTP/1.0\n\n"`, `path` a `reqPath`: the dialer writes nothing more before it
has read the answer), that delivers nothing after an error (the law over `E` and `S`), and whose errors
have an `Error()` method (`errMsgOk`: `readRequestLimit` calls it on the header reader's error);
`maxHeaders` not negative. It returns an error (some error, non-nil: the stream's, `io.ErrUnexpectedEOF`
for its `io.EOF` once the request line is read, a malformed line's, `errTooLarge`), or the request
(`connectReqv`: `CONNECT`, the request URI `path`, `HTTP/1.0`, the URL of path `path`, an empty header,
no body) and `nil`, the reader past the request's bytes. A line cut by an error does not parse as a
whole request: the version `"HTTP/1.0"` is the line's end, and a whole line is followed by the header
block, which the error cuts. `httpEnv` (`Net/Proof/net/http/Defs.lean`) is the package state the
parse reads. Proved in `Net/Proof/net/http/readRequestLimit.lean`.
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
abbrev readRequestLimit.spec : Prop :=
  ∀ (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (path : List w8) (maxH : w64),
  reqPath path → 0 ≤ sint.Z maxH →
  ⊢ httpEnv -∗ EtcdGrove.io.readerStreamNE ri S E -∗
    (□ ∀ r', S r' -∗ ⌜r'.length + 2 ^ 12 < 2 ^ 62⌝) -∗
    (□ ∀ r', S r' -∗ ⌜r' <+: net.rpc.connectReq path⌝) -∗
    (□ ∀ (r1 r2 : List w8) (e : GoInterface), E r1 e -∗ S r2 -∗ ⌜r1 <+: r2 → r2 = r1⌝) -∗
    (□ ∀ (r : List w8) (e : GoInterface), E r e -∗ errMsgOk e) -∗
    {{ EtcdGrove.bufio.ownReader b ri S E [] }}
      (App (App (Val (@! net.http.readRequestLimit)) (Val #b)) (Val #maxH))
    {{ (req : Loc) (err : GoInterface), RET (PairV #req #err);
        ⌜err ≠ interface.nil⌝ ∨
        (⌜err = interface.nil⌝ ∗ connectReqv req path ∗
          EtcdGrove.bufio.ownReader b ri S E (net.rpc.connectReq path)) }}

end spec

end net.http
end Perennial
