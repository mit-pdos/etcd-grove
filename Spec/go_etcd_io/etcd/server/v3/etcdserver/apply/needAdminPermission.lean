/-
`needAdminPermission(r)` (`auth.go:244-275`): the auth administration requests.

**Users.** `authApplierV3.Apply`.

**Proof sketch.** Field reads of the message (`irrMsgAt`).

**Changes** from `specs-ref`'s file of the same name: over `Irr`.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Apply

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **Whether the request needs an administrator.** -/
def needAdminPermission.spec : Prop :=
  ∀ (p : Loc) (ir : Irr),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ irrMsgAt p ir }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.needAdminPermission)) (Val #p))
  {{ (b : Bool), RET #b; ⌜b = ir.op.needAdmin⌝ }}

end spec

end Apply
end EtcdGrove
end Perennial
