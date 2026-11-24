/-
`modelReadLine(b)` (the model's textproto `ReadLine`, `textproto_model.go`), `b` a `*bufio.Reader`
(`bufio.ownReader`) over a stream reader that makes progress (`io.readerStreamNE`): the bytes `l` up to
the next `"\n"` (none in `l`): with it, `l` without a final `"\r"` (`dropCR`) and `nil`, the reader
past the `"\n"`; or cut by an error `e` of the stream there (`io.errAt E (r ++ l) e`: with `E`'s
evidence, and typed, what comparing it with `io.EOF` needs), the reader at `r ++ l`, and then `l`
and `nil` if `l` is not empty, else `""` and `e`. Proved in
`Net/Proof/net/http/modelReadLine.lean`.
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
abbrev modelReadLine.spec : Prop :=
  ∀ (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (r : List w8),
  ⊢ EtcdGrove.io.readerStreamNE ri S E -∗ (□ ∀ r', S r' -∗ ⌜r'.length + 2 ^ 12 < 2 ^ 62⌝) -∗
    {{ EtcdGrove.bufio.ownReader b ri S E r }}
      (App (Val (@! net.http.modelReadLine)) (Val #b))
    {{ (line : GoString) (err : GoInterface), RET (PairV #line #err);
        ∃ l : List w8, ⌜W8 10 ∉ l⌝ ∗
        ((⌜err = interface.nil ∧ line = dropCR l⌝ ∗
            EtcdGrove.bufio.ownReader b ri S E (r ++ l ++ [W8 10])) ∨
         (∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗ EtcdGrove.io.errAt E (r ++ l) e ∗
           EtcdGrove.bufio.ownReader b ri S E (r ++ l) ∗
           ⌜(l ≠ [] ∧ err = interface.nil ∧ line = l) ∨ (l = [] ∧ err = e ∧ line = [])⌝)) }}

end spec

end net.http
end Perennial
