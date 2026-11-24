/-
`u.EscapedPath()` (Go 1.27.3, `url.go`; pointer receiver): `u.RawPath` when it is a valid
encoding of `u.Path`, else `u.Path` escaped (`escapedPathF`); the URL is only read. `u.Path` at
most a third of the `int` range (`escape`'s premise: its result's length may not overflow), and
`len(u.RawPath) + 1` within it (`unescape`'s). Proved in `Proof/net/url/URL__EscapedPath.lean`.
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
abbrev URL.EscapedPath.spec : Prop :=
  ∀ (u : Loc) (dq : DFrac) (v : net.url.URL), 3 * v.Path'.length < 2 ^ 63 →
    v.RawPath'.length + 1 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.url ∗ u ↦{dq} v }}
    (App (Val (u @!! go.GoType.PointerType net.url.URL.ty @!! go!"EscapedPath")) (Val #()))
  {{ RET #(escapedPathF v.RawPath' v.Path'); u ↦{dq} v }}

end spec

end net.url
end Perennial
