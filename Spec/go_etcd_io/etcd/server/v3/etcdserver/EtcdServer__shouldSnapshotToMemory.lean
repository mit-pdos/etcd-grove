/-
`(*EtcdServer).shouldSnapshotToMemory(ep)` (`server.go:1255-1257`): past the last memory snapshot by
more than `memorySnapshotCount` (100; the sum wraps as Go's `uint64`). Internal (`snapshotIfNeededAndCompactRaftLog`).

**Proof sketch**: reads `ep`'s indices (the constant needs no field). **Changes**: over
`applyThread`. **Margin**: none (the result's formula is stated).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

def EtcdServer.shouldSnapshotToMemory.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : w64) (ep : Loc) (p : Progress),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ applyThread s γ ep p }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"shouldSnapshotToMemory")) (Val #ep))
  {{ (b : Bool), RET #b; applyThread s γ ep p ∗
      ⌜b = decide (uint.Z (p.memSnap + W64 100) < uint.Z p.appliedi)⌝ }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
