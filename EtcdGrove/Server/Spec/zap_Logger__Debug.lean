/-
`zap.Logger.Debug`: the trust boundary (`go.uber.org/zap` is names-only). Lean-first (no Rocq counterpart).
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

/-- `l.Debug(msg, fields...)` (a non-nil logger) returns: logging has no effect here. -/
abbrev zap.Logger.Debug.spec : Prop :=
  ∀ (l : Loc) (msg : GoString) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ ⌜l ≠ null⌝ }}
    (App (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"Debug")) (Val #msg)) (Val #fields))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
