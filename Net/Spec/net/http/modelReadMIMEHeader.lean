/-
`modelReadMIMEHeader(b, maxHeaders)` (the model's textproto `readMIMEHeader`, `textproto_model.go`) on
a head with no header lines: `b` a `*bufio.Reader` at `r` over a stream reader that makes progress,
whose bytes are, as long as it is read, a prefix of `r ++ "\n"`: an error (a pointer's value a
location, `io.ptrTyped`: `ReadResponse` compares it with `io.EOF`), or an empty map and `nil`,
the reader past the `"\n"`. (The header block of net/rpc's answer, `ReadResponse`.) Proved in
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
    (r : List w8) (maxH : w64),
  ⊢ EtcdGrove.io.readerStreamNE ri S E -∗ (□ ∀ r', S r' -∗ ⌜r'.length + 2 ^ 12 < 2 ^ 62⌝) -∗
    (□ ∀ r', S r' -∗ ⌜r' <+: r ++ [W8 10]⌝) -∗
    {{ EtcdGrove.bufio.ownReader b ri S E r }}
      (App (App (Val (@! net.http.modelReadMIMEHeader)) (Val #b)) (Val #maxH))
    {{ (m : Loc) (err : GoInterface), RET (PairV #m #err);
        ⌜err ≠ interface.nil ∧ _root_.Perennial.io.ptrTyped err⌝ ∨
        (⌜err = interface.nil⌝ ∗ m ↦$ (∅ : GMap GoString GoSlice) ∗
          EtcdGrove.bufio.ownReader b ri S E (r ++ [W8 10])) }}

end spec

end net.http
end Perennial
