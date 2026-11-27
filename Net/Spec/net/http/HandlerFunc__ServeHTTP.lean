/-
`HandlerFunc(f).ServeHTTP(w, r)`: `f(w, r)`. Its run returns what `f`'s does, when that is `()` or a
panic. Proved in `Net/Proof/net/http/HandlerFunc__ServeHTTP.lean`. Lean-first.
-/
module

public import Net.Proof.net.http.PkgInit

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
abbrev HandlerFunc.ServeHTTP.spec : Prop :=
  ∀ (f : GoFunc) (w : GoInterface) (r : Loc) (Φ : val → IProp GF),
    WP (App (App (Val #f) (Val #w)) (Val #r)) {{ v, ⌜v = #() ∨ v.isPanic = true⌝ ∗ Φ v }} ⊢
    WP (App (App (Val #(methods net.http.HandlerFunc.ty go!"ServeHTTP" #f)) (Val #w)) (Val #r))
      {{ Φ }}

end spec
end net.http
end Perennial
