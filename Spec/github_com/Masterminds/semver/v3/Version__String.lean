/-
`semver.Version.String` (`version.go:340-352`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.github_com.Masterminds.semver.v3.Str

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

/-- `v.String()` of a version `v` points to, at any fraction, kept, returns its rendering
(`semver.render`: `major.minor.patch` in decimal, then `-pre` and `+metadata` if not empty), which
starts with the major and minor versions in decimal, each followed by a dot
(`semver.semverStr_render`). (2026-11-23, prove-ps2-semstr, proved over the real code: until then
a trust-boundary axiom of any `v` not nil, which a concurrent writer races, returning some string
with `semverStr`; D19l (iii), 2026-10-18: until then some string.) -/
abbrev semver.Version.String.spec : Prop :=
  ∀ (v : Loc) (dq : DFrac) (x : github_com.Masterminds.semver.v3.Version),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 ∗ v ↦{dq} x }}
    (App (Val (v @!! go.GoType.PointerType github_com.Masterminds.semver.v3.Version.ty @!! go!"String")) (Val #()))
  {{ RET #(semver.render x); v ↦{dq} x }}

end spec

end EtcdGrove
end Perennial
