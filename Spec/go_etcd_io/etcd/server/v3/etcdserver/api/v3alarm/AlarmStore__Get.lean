/-
`v3alarm.AlarmStore.Get`: the trust boundary (`api/v3alarm` is names-only: `Get` reads the alarms under a mutex). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

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

/-- `a.Get(aty)` returns some slice of the alarms of type `aty`. -/
abbrev v3alarm.AlarmStore.Get.spec : Prop :=
  ∀ (a : Loc) (aty : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm }}
    (App (Val (a @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore.ty @!! go!"Get")) (Val aty))
  {{ (sl : GoSlice), RET #sl; True }}

end spec

end EtcdGrove
end Perennial
