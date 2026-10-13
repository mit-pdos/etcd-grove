/-
`greaterOrEqual` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `greaterOrEqual(a, b)`: some boolean (`!version.LessThan(a, b)`). -/
abbrev lease.greaterOrEqual.spec : Prop :=
  ∀ (a b : github_com.Masterminds.semver.v3.Version),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.lease.greaterOrEqual)) (Val #a)) (Val #b))
  {{ (r : Bool), RET #r; True }}

end spec

end EtcdGrove
end Perennial
