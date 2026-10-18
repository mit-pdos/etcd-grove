/-
`semver.Version.String`: the trust boundary (`github.com/Masterminds/semver/v3` is names-only). Lean-first (no Rocq counterpart).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `v.String()` (`v` not nil) returns a string that starts with the major and minor versions in
decimal, each followed by a dot (`semverStr`: `"%d.%d.%d"`, then `-pre` and `+metadata`,
`version.go`; D19l (iii), 2026-10-18: until then some string). -/
abbrev semver.Version.String.spec : Prop :=
  ∀ (v : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 ∗ ⌜v ≠ null⌝ }}
    (App (Val (v @!! go.GoType.PointerType github_com.Masterminds.semver.v3.Version.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; ⌜semverStr s⌝ }}

end spec

end EtcdGrove
end Perennial
