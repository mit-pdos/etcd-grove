/-
`(*raftNode).getLatestTickTs()` (`raft.go:163-167`): the last tick's time, under `tickMu`'s read
lock. **Users**: `isActive`/`ensureLeadership` (2c). The time carries no fact (time is not modelled).
**Changes**: over `isRaftNode`. **Margin**: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

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

def raftNode.getLatestTickTs.spec : Prop :=
  ∀ (r : Loc) (γ : Names) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode r γ id n }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.raftNode.ty @!!
      go!"getLatestTickTs")) (Val #()))
  {{ (t : time.Time), RET #t; True }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
