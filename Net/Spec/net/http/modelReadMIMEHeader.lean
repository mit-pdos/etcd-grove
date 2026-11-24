/-
`modelReadMIMEHeader(b, maxHeaders)` (the model's textproto `readMIMEHeader`, `textproto_model.go`) on
a header block `hb` the model reads as it is (`hdrBlockOk`: distinct canonical names, printable values
without space at their ends; `Net/Proof/net/http/Defs.lean`), at most `maxHeaders` lines: `b` a
`*bufio.Reader` at `r` over a stream reader that makes progress and delivers nothing after an error
(the law over `E` and `S`), whose bytes past `r` are, as long as it is read, a prefix of the block's
(`hdrWire hb eol`, its empty line `eol ++ "\n"`) followed by anything (`rest`): an error (a pointer's
value a location, `io.ptrTyped`, which `ReadResponse` needs to compare it with `io.EOF`; the stream's,
with `E`'s evidence, or a `textproto.ProtocolError` for a line cut by one), or `nil` and the map of
the block (`hdrOwn`), the reader past the block. (The header blocks of net/rpc's answer, empty, and of
net/http's `400` answer, `ReadResponse`; of net/rpc's `CONNECT` request, empty, `readRequestLimit`.)
`httpEnv`: `fmt`'s initialization (a `ProtocolError`'s message) and httpguts' table, which
`ValidHeaderFieldName` reads (a line's name). Proved in
`Net/Proof/net/http/modelReadMIMEHeader.lean`.
-/
module

public import Net.Proof.net.http.Defs
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
abbrev modelReadMIMEHeader.spec : Prop :=
  ∀ (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (r : List w8) (hb : List HdrLine) (eol rest : List w8) (maxH : w64),
  hdrBlockOk hb → (eol = [] ∨ eol = [W8 13]) → (hb.length : Int) ≤ sint.Z maxH →
  ⊢ httpEnv -∗ EtcdGrove.io.readerStreamNE ri S E -∗
    (□ ∀ r', S r' -∗ ⌜r'.length + 2 ^ 12 < 2 ^ 62⌝) -∗
    (□ ∀ r', S r' -∗ ⌜r <+: r' → r' <+: r ++ hdrWire hb eol ++ rest⌝) -∗
    (□ ∀ (r1 r2 : List w8) (e : GoInterface), E r1 e -∗ S r2 -∗ ⌜r1 <+: r2 → r2 = r1⌝) -∗
    {{ EtcdGrove.bufio.ownReader b ri S E r }}
      (App (App (Val (@! net.http.modelReadMIMEHeader)) (Val #b)) (Val #maxH))
    {{ (m : Loc) (err : GoInterface), RET (PairV #m #err);
        (⌜err ≠ interface.nil ∧ _root_.Perennial.io.ptrTyped err⌝ ∗ mimeErr E err) ∨
        (⌜err = interface.nil⌝ ∗ hdrOwn m hb ∗
          EtcdGrove.bufio.ownReader b ri S E (r ++ hdrWire hb eol)) }}

end spec

end net.http
end Perennial
