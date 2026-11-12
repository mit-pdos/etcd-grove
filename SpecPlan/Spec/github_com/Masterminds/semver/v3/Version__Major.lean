/-
## `Version.Major()`: assumed

**Users.** rafthttp (`util.go:135`, `stream.go:712`), downgrade checks. Snippet: `examples/specreq/pkgleaves/leaves.go` (`ReqMajorMinor`). **Assumed** (`version.go:360-368`): a
field read. **Changes.** From `specs-ref`'s `Version__Major.lean`. **Margin.** None.
-/
module

public import SpecPlan.Spec.github_com.Masterminds.semver.v3.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Semver

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.Masterminds.semver.v3.Assumptions]

/-- The version's major number. -/
def Version.Major.spec : Prop :=
  ∀ (v : Loc) (a : SemVer),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 ∗ verAt v a }}
    (App (Val (v @!! go.GoType.PointerType github_com.Masterminds.semver.v3.Version.ty @!! go!"Major")) (Val #()))
  {{ RET #(a.major); True }}

end spec
end Semver
end EtcdGrove
end Perennial
