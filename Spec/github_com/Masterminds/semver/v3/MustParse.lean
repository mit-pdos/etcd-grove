/-
`semver.MustParse`: the trust boundary (`github.com/Masterminds/semver/v3` is names-only). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvRequest

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

/-- `semver.MustParse(s)` for an `s` that parses (`semverValid`): a new version, not nil, never
written afterwards (a `Version` has no mutating method the verified code calls), so its
points-to is returned persistent (`Version.String` is a value method: its callers load `*v`).
(On an error of `NewVersion`, `MustParse` panics, which no deferred function recovers: the call
is stuck there, so the spec requires `s` to parse.) -/
abbrev semver.MustParse.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 ∗
      ⌜apply.semverValid s⌝ }}
    (App (Val (@! github_com.Masterminds.semver.v3.MustParse)) (Val #s))
  {{ (v : Loc), RET #v; ⌜v ≠ null⌝ ∗
      ∃ ver : github_com.Masterminds.semver.v3.Version, v ↦□ ver }}

end spec

end EtcdGrove
end Perennial
