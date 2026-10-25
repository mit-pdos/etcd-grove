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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `semver.New(major, minor, patch, pre, metadata)` returns a new version, not nil. -/
abbrev semver.New.spec : Prop :=
  ∀ (ma mi pa : w64) (pre md : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
    (App (App (App (App (App (Val (@! github_com.Masterminds.semver.v3.New)) (Val #ma)) (Val #mi)) (Val #pa)) (Val #pre))
      (Val #md))
  {{ (v : Loc), RET #v; ⌜v ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
