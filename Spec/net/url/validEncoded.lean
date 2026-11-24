/-
`url.validEncoded(s, mode)` (Go 1.27.3, `url.go`), for one of the seven modes: whether every byte
of `s` is a sub-delim, `:`, `@`, `[`, `]`, `%`, or one `mode` does not escape (`validEncodedF`). Proved in `Proof/net/url/validEncoded.lean`.
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
abbrev validEncoded.spec : Prop :=
  ∀ (s : GoString) (mode : w8), mode ∈ encModes →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.url }}
    (App (App (Val (@! net.url.validEncoded)) (Val #s)) (Val #mode))
  {{ RET #(validEncodedF s mode); True }}

end spec

end net.url
end Perennial
