/-
`url.ishex(c)` (Go 1.27.3, `url.go`): `table[c]&hexChar != 0`, whether `c` is a hex digit
(`ishexRef`, by net/url's fact `urlInit` and `encTable_hex`). Proved in `Proof/net/url/ishex.lean`.
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
abbrev ishex.spec : Prop :=
  ∀ (c : w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.url }}
    (App (Val (@! net.url.ishex)) (Val #c))
  {{ RET #(ishexRef c); True }}

end spec

end net.url
end Perennial
