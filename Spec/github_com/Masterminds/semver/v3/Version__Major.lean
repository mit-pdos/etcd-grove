/-
`semver.Version.Major`: the trust boundary (`github.com/Masterminds/semver/v3` is names-only;
rafthttp stage 5e-3). Lean-first.
-/
module

public import Spec.github_com.Masterminds.semver.v3.Version__LessThan

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
variable [package_sem : github_com.Masterminds.semver.v3.Assumptions]

/-- `v.Major()` of a version `v` points to, at any fraction, kept (2026-11-20, prove-smalllibs: until then of
any `v` not nil, which a concurrent writer races; and some number) returns its major number. -/
abbrev semver.Version.Major.spec : Prop :=
  ∀ (v : Loc) (dq : DFrac) (x : github_com.Masterminds.semver.v3.Version),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 ∗ v ↦{dq} x }}
    (App (Val (v @!! go.GoType.PointerType github_com.Masterminds.semver.v3.Version.ty @!! go!"Major")) (Val #()))
  {{ RET #x.major'; v ↦{dq} x }}

end spec

end EtcdGrove
end Perennial
