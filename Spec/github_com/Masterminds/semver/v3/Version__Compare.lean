/-
`semver.Version.Compare` (`version.go:525-553`), proved over the real code (prove-ps2-semver,
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

/-- `v.Compare(o)` of the versions `v` and `o` point to, at any fractions, kept, returns their
comparison (`semver.compare`: `-1`, `0` or `1`). -/
abbrev semver.Version.Compare.spec : Prop :=
  ∀ (v o : Loc) (dv dw : DFrac) (x y : github_com.Masterminds.semver.v3.Version),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 ∗ v ↦{dv} x ∗ o ↦{dw} y }}
    (App (Val (v @!! go.GoType.PointerType github_com.Masterminds.semver.v3.Version.ty @!! go!"Compare")) (Val #o))
  {{ RET #(semver.compare x y); v ↦{dv} x ∗ o ↦{dw} y }}

end spec

end EtcdGrove
end Perennial
