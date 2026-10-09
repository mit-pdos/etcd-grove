/-
`EtcdServer.stopWithDelay`: the trust boundary (names-only: it stops the server after a delay). Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Server.InvApplier

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3 go_etcd_io.etcd.pkg.v3 go_uber_org

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.stopWithDelay(d, err)` returns. -/
abbrev EtcdServer.stopWithDelay.spec : Prop :=
  ∀ (s : Loc) (d : w64) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"stopWithDelay")) (Val #d)) (Val #err))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
