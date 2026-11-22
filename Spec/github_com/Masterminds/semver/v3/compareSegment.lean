/-
`semver.compareSegment` (`version.go:627-636`), proved over the real code (prove-ps2-semver,
2026-11-22). Lean-first.
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

/-- `compareSegment(v, o)` returns `-1`, `1` or `0` as `v` is below, above or equal to `o`
(`semver.cmpSeg`). -/
abbrev semver.compareSegment.spec : Prop :=
  ∀ (v o : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
    (App (App (Val (@! github_com.Masterminds.semver.v3.compareSegment)) (Val #v)) (Val #o))
  {{ RET #(semver.cmpSeg v o); True }}

end spec

end EtcdGrove
end Perennial
