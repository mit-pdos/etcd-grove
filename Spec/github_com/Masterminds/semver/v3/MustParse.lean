/-
## `semver.MustParse(s)`: assumed

**Users.** rafthttp (`util.go:154,164,174,175`, `stream.go:613`: a peer's version header, etcd's
constants), the applier (`apply/backend.go:272`: a committed `ClusterVersionSet`'s `Ver`), the
membership (`cluster.go:270,586,610`), the schema (`schema/membership.go:205`: the stored cluster
version). Snippets: `examples/specreq/pkgleaves/leaves.go` (`ReqParseCompare`, `ReqRoundTrip`).

**Assumed** (`version.go:327-333`): `NewVersion(s)`, a panic on its error. The premise is the
callers': a header the protocol says parses, a constant (`parse_version`, `parse_plain`), a stored
or committed `String()` of a version (`parse_render`).

**Changes.** From `specs-ref`'s `MustParse.lean` (a disjunction with a panic result, over the
applier's `semverValid`): the parse is the premise, the result a model.

**Margin.** None (a fresh version; `verAt` gives it read-only).
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

/-- **The version `s` parses to** (it must parse: else a panic). -/
def MustParse.spec : Prop :=
  ∀ (s : GoString) (sv : SemVer),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 ∗ ⌜parse s = some sv⌝ }}
    (App (Val (@! github_com.Masterminds.semver.v3.MustParse)) (Val #s))
  {{ (v : Loc), RET #v; verAt v sv }}

end spec
end Semver
end EtcdGrove
end Perennial
