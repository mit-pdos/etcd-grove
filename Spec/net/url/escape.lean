/-
`url.escape(s, mode)` (Go 1.27.3, `url.go`), for one of the seven modes: `s` with each byte
`mode` escapes as `%AB` (a space as `+` in a query component): `escapeF s mode`. `s` at most a third of the `int` range (Go's
`len(s) + 2*hexCount`, the result's length, may not overflow). Proved in `Proof/net/url/escape.lean`.
-/
module

public import Proof.net.url.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.url

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : net.url.Assumptions]

/-- See the file header. -/
abbrev escape.spec : Prop :=
  ∀ (s : GoString) (mode : w8), mode ∈ encModes → 3 * s.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.url }}
    (App (App (Val (@! net.url.escape)) (Val #s)) (Val #mode))
  {{ RET #(escapeF s mode); True }}

end spec

end net.url
end Perennial
