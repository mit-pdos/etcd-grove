/-
`url.PathUnescape(s)` (Go 1.27.3, `url.go`): `unescape(s, encodePathSegment)` (`unescRes`), under `unescape`'s premise. Proved in `Proof/net/url/PathUnescape.lean`.
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
abbrev PathUnescape.spec : Prop :=
  ∀ (s : GoString), s.length + 1 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.url }}
    (App (Val (@! net.url.PathUnescape)) (Val #s))
  {{ RET (PairV #(unescRes s mPathSegment).1 #(unescRes s mPathSegment).2); True }}

end spec

end net.url
end Perennial
