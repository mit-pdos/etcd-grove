/-
`badStringError(what, val)` (`fmt.Errorf("%s %q", what, val)`): a non-nil error, a pointer
(`io.ptrTyped`: `readRequestLimit` compares it with `io.EOF`), whose `Error()` returns some string
(`errMsgOk`: `fmt.Errorf`'s error). Proved in
`Net/Proof/net/http/badStringError.lean`.
-/
module

public import Net.Proof.net.http.RequestDefs

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
abbrev badStringError.spec : Prop :=
  ∀ (what val : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt }}
    (App (App (Val (@! net.http.badStringError)) (Val #what)) (Val #val))
  {{ (e : GoInterfaceOk), RET #(interface.ok e);
      ⌜_root_.Perennial.io.ptrTyped (interface.ok e)⌝ ∗ errMsgOk (interface.ok e) }}

end spec

end net.http
end Perennial
