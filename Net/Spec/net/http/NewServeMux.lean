/-
`http.NewServeMux()`: `&ServeMux{}`, a zero mux, owned. Proved in `Net/Proof/net/http/NewServeMux.lean`.
Lean-first.
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
abbrev NewServeMux.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http }}
    (App (Val (@! net.http.NewServeMux)) (Val #()))
  {{ (m : Loc), RET #m; m ↦ (zero_val net.http.ServeMux) }}

end spec
end net.http
end Perennial
