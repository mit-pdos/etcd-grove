/-
## `(*Message).GetTo()` (promoted from the embedded raft message): translated

**Users.** rafthttp's `Transport.SendSnapshot` (2f). **Proof sketch.** The embedded message's
`To` (read-only, `isMessage`). **Changes**: from `specs-ref`. **Margin.** Exact.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Api
public import Spec.go_uber_org.zap.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.Api

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

/-- **The recipient.** -/
def Message.GetTo.spec : Prop :=
  ∀ (p : Loc) (to tot : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗ isMessage p to tot }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message.ty @!! go!"GetTo")) (Val #()))
  {{ RET #to; True }}

end spec

end Snap
end EtcdGrove
end Perennial
