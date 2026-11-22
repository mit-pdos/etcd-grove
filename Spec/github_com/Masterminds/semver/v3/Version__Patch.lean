/-
`semver.Version.Patch` (`version.go`), proved over the real code (prove-ps2-semver, 2026-11-22).
Lean-first.
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

/-- `v.Patch()` of a version `v` points to, at any fraction, kept, returns its `patch` field. -/
abbrev semver.Version.Patch.spec : Prop :=
  ∀ (v : Loc) (dq : DFrac) (x : github_com.Masterminds.semver.v3.Version),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 ∗ v ↦{dq} x }}
    (App (Val (v @!! go.GoType.PointerType github_com.Masterminds.semver.v3.Version.ty @!! go!"Patch")) (Val #()))
  {{ RET #x.patch'; v ↦{dq} x }}

end spec

end EtcdGrove
end Perennial
