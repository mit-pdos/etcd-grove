/-
`version.LessThan(a, b)` (`api/v3/version`, names only: the trust boundary). Lean-first (no Rocq
counterpart); the lessor's `greaterOrEqual` (2026-10-13, unit 9).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.Base

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
variable [package_sem : go_etcd_io.etcd.api.v3.version.Assumptions]

/-- `LessThan(a, b)` compares two `semver.Version` values (by value: their major and minor
numbers); it returns some boolean. -/
abbrev version.LessThan.spec : Prop :=
  ∀ (a b : github_com.Masterminds.semver.v3.Version),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version }}
    (App (App (Val (@! go_etcd_io.etcd.api.v3.version.LessThan)) (Val #a)) (Val #b))
  {{ (r : Bool), RET #r; True }}

end spec

end EtcdGrove
end Perennial
