/-
`hasToken(v, token)` (`header.go`) when `token` is longer than `v`: `false`, without reading the
strings. (Only that case: the rest of the body calls `isTokenBoundary` and `ascii.EqualFold`, which
the translation leaves names only; net/http's server reaches it with `v` the `""` of a request with
no `Connection` header.) Proved in `Net/Proof/net/http/hasToken.lean`.
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
abbrev hasToken.spec : Prop :=
  ∀ (v token : GoString),
  {{ (⌜v.length < token.length⌝ : IProp GF) }}
    (App (App (Val (@! net.http.hasToken)) (Val #v)) (Val #token))
  {{ RET #false; True }}

end spec

end net.http
end Perennial
