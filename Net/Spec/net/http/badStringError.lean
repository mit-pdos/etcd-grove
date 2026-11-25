/-
`badStringError(what, val)` (`fmt.Errorf("%s %q", what, val)`): a non-nil error, a pointer
(`io.ptrTyped`: `readRequestLimit` compares it with `io.EOF`), an `*errors.errorString` (`errors.New`
of the message) whose message starts with `what` (what tells it from the package's other
`errors.New` errors, `errTooLarge`). Proved in
`Net/Proof/net/http/badStringError.lean`.
-/
module

public import Net.Proof.net.http.Defs

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
  {{ (e : GoInterfaceOk), RET #(interface.ok e); ⌜_root_.Perennial.io.ptrTyped (interface.ok e)⌝ ∗
      ∃ (x : Loc) (s : GoString),
        ⌜e = ⟨go.GoType.PointerType errors.errorString.ty, #x⟩ ∧ what <+: s⌝ ∗
        x.[errors.errorString, go!"s"] ↦□ s }}

end spec

end net.http
end Perennial
