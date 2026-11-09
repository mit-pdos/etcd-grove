/-
## `Version.String()`: assumed

**Users.** The membership (`cluster.go:586`: `MustParse(c.version.String())`, a copy), the schema
(`schema/membership.go:156`: the stored cluster version), logs. Snippet: `semver.go`
(`ReqRoundTrip`). **Assumed** (`version.go:340-352`): `fmt.Fprintf` of the fields.
**Changes.** From `specs-ref`'s `Version__String.lean`: the rendering. **Margin.** None.
-/
module

public import Spec.github_com.Masterminds.semver.v3.Api

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

/-- **The version's rendering** (`render`). -/
def Version.String.spec : Prop :=
  ∀ (v : Loc) (a : SemVer),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 ∗ verAt v a }}
    (App (Val (v @!! go.GoType.PointerType github_com.Masterminds.semver.v3.Version.ty @!! go!"String")) (Val #()))
  {{ RET #(render a); True }}

end spec
end Semver
end EtcdGrove
end Perennial
