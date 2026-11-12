/-
## `semver.New(major, minor, patch, pre, metadata)`: assumed

**Users.** rafthttp (`util.go:135-136`, `stream.go:712`: `major.minor.0`), the downgrade checks
(`version/downgrade.go:44,59,69-70`), `api/version`'s constants (3h). Snippet: `examples/specreq/pkgleaves/leaves.go`
(`ReqMajorMinor`).

**Assumed** (`version.go:310-324`): a struct literal (no validation), `original` its `String()`.
**Changes.** From `specs-ref`'s `New.lean` (not nil): the fields. **Margin.** None.
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

/-- **A version of these fields.** -/
def New.spec : Prop :=
  ∀ (ma mi pa : w64) (pre md : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
    (App (App (App (App (App (Val (@! github_com.Masterminds.semver.v3.New)) (Val #ma)) (Val #mi))
      (Val #pa)) (Val #pre)) (Val #md))
  {{ (v : Loc), RET #v; verAt v ⟨ma, mi, pa, pre, md⟩ }}

end spec
end Semver
end EtcdGrove
end Perennial
