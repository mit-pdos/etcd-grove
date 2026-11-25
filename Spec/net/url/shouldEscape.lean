/-
`url.shouldEscape(c, mode)` (Go 1.27.3, `url.go`): `table[c]&mode == 0`, the table being net/url's
fact (`urlInit`); for one of the seven modes, that is `gen_encoding_table.go`'s reference
`shouldEscapeRef c mode` (`encTable_mode`). Proved in `Proof/net/url/shouldEscape.lean`.
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
abbrev shouldEscape.spec : Prop :=
  ∀ (c mode : w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.url }}
    (App (App (Val (@! net.url.shouldEscape)) (Val #c)) (Val #mode))
  {{ RET #(encTable c &&& mode == W8 0); True }}

end spec

end net.url
end Perennial
