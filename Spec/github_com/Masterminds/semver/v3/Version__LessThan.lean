/-
## `(*Version).LessThan(o)`: assumed

**Users.** rafthttp (`util.go:138,140`), the applier (`apply/backend.go:275`), the downgrade checks,
`api/version.LessThan` (3h, used by the lessor's `greaterOrEqual`). Snippet: `examples/specreq/pkgleaves/leaves.go`
(`ReqParseCompare`).

**Assumed** (`version.go:486,525-560`): `Compare(o) < 0`; it reads both (neither nil: `verAt`).
**Changes.** From `specs-ref`'s `Version__LessThan.lean` (some boolean): the comparison.
**Margin.** None.
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

/-- **`a < b`** in semver's precedence. -/
def Version.LessThan.spec : Prop :=
  ∀ (v o : Loc) (a b : SemVer),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 ∗ verAt v a ∗ verAt o b }}
    (App (Val (v @!! go.GoType.PointerType github_com.Masterminds.semver.v3.Version.ty @!! go!"LessThan")) (Val #o))
  {{ RET #(SemVer.ltb a b); True }}

end spec
end Semver
end EtcdGrove
end Perennial
