/-
`url.unhex(c)` (Go 1.27.3, `url.go`): `9*(c>>6) + (c&15)` (`unhexF`; a hex digit's value). Proved in `Proof/net/url/unhex.lean`.
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
abbrev unhex.spec : Prop :=
  ∀ (c : w8),
  {{ (True : IProp GF) }}
    (App (Val (@! net.url.unhex)) (Val #c))
  {{ RET #(unhexF c); True }}

end spec

end net.url
end Perennial
