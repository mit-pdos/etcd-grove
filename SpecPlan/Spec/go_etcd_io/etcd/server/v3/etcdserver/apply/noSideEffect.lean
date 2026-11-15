/-
`noSideEffect(r)` (`apply.go:51-53`): a range, a user or role read, the auth status.

**Users.** `Apply`.

**Proof sketch.** Field reads of the message (`irrMsgAt`).

**Changes** from `specs-ref`'s file of the same name: over `Irr`.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult

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

/-- **Whether the request has no side effect.** -/
def noSideEffect.spec : Prop :=
  ∀ (p : Loc) (ir : Irr),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ irrMsgAt p ir }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.noSideEffect)) (Val #p))
  {{ (b : Bool), RET #b; ⌜b = ir.op.noSideEffect⌝ }}

end spec

end Apply
end EtcdGrove
end Perennial
