/-
`semver.Version.Major`: the trust boundary (`github.com/Masterminds/semver/v3` is names-only; pr-verify etcd#22589). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

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

/-- `v.Major()` (`v` not nil: `Major` has a value receiver, so a call through a nil pointer panics) returns some number. -/
abbrev semver.Version.Major.spec : Prop :=
  ∀ (v : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 ∗ ⌜v ≠ null⌝ }}
    (App (Val (v @!! go.GoType.PointerType github_com.Masterminds.semver.v3.Version.ty @!! go!"Major")) (Val #()))
  {{ (n : w64), RET #n; True }}

end spec

end EtcdGrove
end Perennial
