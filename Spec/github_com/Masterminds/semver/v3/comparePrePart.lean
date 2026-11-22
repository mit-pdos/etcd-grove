/-
`semver.comparePrePart` (`version.go:680-730`), proved over the real code (prove-ps2-semver,
2026-11-22), over `strconv.ParseUint`'s spec. Lean-first.
-/
module

public import Proof.github_com.Masterminds.semver.v3.CompareModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `comparePrePart(s, o)` returns the comparison of two prerelease parts (`semver.cmpPrePart`:
numbers by value, below non-numbers, which compare by their bytes). -/
abbrev semver.comparePrePart.spec : Prop :=
  ∀ (s o : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
    (App (App (Val (@! github_com.Masterminds.semver.v3.comparePrePart)) (Val #s)) (Val #o))
  {{ RET #(semver.cmpPrePart s o); True }}

end spec

end EtcdGrove
end Perennial
