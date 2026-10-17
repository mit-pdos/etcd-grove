/-
`semver.Version.Equal`: the trust boundary (`github.com/Masterminds/semver/v3` is names-only; pr-verify etcd#22589). Lean-first (no Rocq counterpart).
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

/-- `v.Equal(o)` returns some boolean, for any `v` and `o`: semver v3.5.0's `Equal` is nil-safe (`v == o` is true, one nil is false, else `Compare`). -/
abbrev semver.Version.Equal.spec : Prop :=
  ∀ (v o : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
    (App (Val (v @!! go.GoType.PointerType github_com.Masterminds.semver.v3.Version.ty @!! go!"Equal")) (Val #o))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
