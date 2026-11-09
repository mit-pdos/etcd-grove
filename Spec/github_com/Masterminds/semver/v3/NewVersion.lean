/-
## `semver.NewVersion(s)`: assumed

**Users.** The schema (`schema/membership.go:233`: a stored downgrade target), `api/version`
(`Cluster`, `init`: 3h's). **Assumed** (`version.go:176-250`): the parse, or an error.
**Changes.** New. **Margin.** The error is not described.
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

/-- **The version `s` parses to, or an error.** -/
def NewVersion.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
    (App (Val (@! github_com.Masterminds.semver.v3.NewVersion)) (Val #s))
  {{ (v : Loc) (err : GoInterface), RET (PairV #v #err);
      match parse s with
      | some sv => iprop(⌜err = GoInterface.nil⌝ ∗ verAt v sv)
      | none => iprop(⌜err ≠ GoInterface.nil⌝) }}

end spec
end Semver
end EtcdGrove
end Perennial
