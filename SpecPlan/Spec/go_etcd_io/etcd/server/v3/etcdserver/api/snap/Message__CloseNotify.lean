/-
## `(*Message).CloseNotify()` (`message.go:53-55`): trusted (names only)

**Users.** 2d's `sendMergedSnap` (waits for the transport's verdict). **Why it is true.** The field.
**Changes**: from `specs-ref`. **Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Api
public import SpecPlan.Spec.go_uber_org.zap.Api
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Snap

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.snap.Assumptions]

/-- **The close-notification channel.** -/
def Message.CloseNotify.spec : Prop :=
  ∀ (p : Loc) (to tot : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗ isMessage p to tot }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message.ty @!! go!"CloseNotify")) (Val #()))
  {{ (ch : Loc), RET #ch; msgCloseCh p ch }}

end spec

end Snap
end EtcdGrove
end Perennial
