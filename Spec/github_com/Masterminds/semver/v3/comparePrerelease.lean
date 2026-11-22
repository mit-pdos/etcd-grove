/-
`semver.comparePrerelease` (`version.go:638-678`), proved over the real code (prove-ps2-semver,
2026-11-22), over `strings.Split`'s spec and `comparePrePart`'s. Lean-first.
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

/-- `comparePrerelease(v, o)` returns the comparison of two prereleases, part by part
(`semver.cmpPre`). -/
abbrev semver.comparePrerelease.spec : Prop :=
  ∀ (v o : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
    (App (App (Val (@! github_com.Masterminds.semver.v3.comparePrerelease)) (Val #v)) (Val #o))
  {{ RET #(semver.cmpPre v o); True }}

end spec

end EtcdGrove
end Perennial
