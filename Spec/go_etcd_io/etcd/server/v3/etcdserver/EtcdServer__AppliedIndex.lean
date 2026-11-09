/-
## `(*EtcdServer).AppliedIndex()` (`server.go:1766`)

**Users.** `restart.stop` (waits until the bootstrap entries are applied: not needed for the restart's safety, `memberDisk` holds any durable state).

**Proof sketch.** A read of a read-only field or an atomic load (`srvMember`'s realization).

**Changes** (from `specs-ref`'s `EtcdServer__AppliedIndex.lean` where it existed): over `srvMember`.

**Margin.** The value is not tied to the model: a member's view may be stale.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`AppliedIndex()`**: the applied index (any). -/
def EtcdServer.AppliedIndex.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvMember s γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"AppliedIndex")) (Val #()))
  {{ (i : w64), RET #i; True }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
