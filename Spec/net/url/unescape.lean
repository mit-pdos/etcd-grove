/-
`url.unescape(s, mode)` (Go 1.27.3, `url.go`), for one of the seven modes: the decoded bytes and
`nil`, or `""` and the error its check finds first (`unescRes s mode`, over `unescapeF`). (`i+2` does
not overflow: a string is no longer than the address space, `wp_string_len_maxAddr`.) Proved in `Proof/net/url/unescape.lean`.
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
abbrev unescape.spec : Prop :=
  ∀ (s : GoString) (mode : w8), mode ∈ encModes →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.url }}
    (App (App (Val (@! net.url.unescape)) (Val #s)) (Val #mode))
  {{ RET (PairV #(unescRes s mode).1 #(unescRes s mode).2); True }}

end spec

end net.url
end Perennial
