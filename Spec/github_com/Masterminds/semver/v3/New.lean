/-
`semver.New`: the trust boundary (`github.com/Masterminds/semver/v3` is names-only; rafthttp
stage 5e-3, `compareMajorMinorVersion` and `checkStreamSupport`). Lean-first.
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

/-- `semver.New(major, minor, patch, pre, metadata)` returns a new version, not nil, of these
fields (and its `String()` as `original`), read-only (2026-11-20, prove-smalllibs: until then only
not nil). -/
abbrev semver.New.spec : Prop :=
  ∀ (ma mi pa : w64) (pre md : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
    (App (App (App (App (App (Val (@! github_com.Masterminds.semver.v3.New)) (Val #ma)) (Val #mi)) (Val #pa)) (Val #pre))
      (Val #md))
  {{ (v : Loc), RET #v; ⌜v ≠ null⌝ ∗
      ∃ orig : GoString, v ↦□ (github_com.Masterminds.semver.v3.Version.mk ma mi pa pre md orig) }}

end spec

end EtcdGrove
end Perennial
