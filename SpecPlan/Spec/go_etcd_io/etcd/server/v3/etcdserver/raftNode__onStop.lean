/-
`(*raftNode).onStop()` (`raft.go:432-440`): stop the raft node, the ticker and the transport, close
the WAL storage, close `done`. Internal (the loop's deferred exit).

**Proof sketch**: `r.Stop()` (R1's `node.Stop.spec`, with the loop's `nodeRunning` half and the
other half the loop holds from the start: the node's vacancy comes back once its goroutine exits),
`ticker.Stop()`, `transport.Stop()` (2f's), `storage.Close()` (2e's: no error under the disk premise,
`lg.Panic` unreachable; the WAL's durable half returned), `close(done)` with `rnStopped`.
**Changes**: over `rnLoop`/`rnStopped`. **Margin**: none.
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

def raftNode.onStop.spec : Prop :=
  ∀ (r : Loc) (γ : Names) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isRaftNode r γ id n ∗ rnLoop r }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.raftNode.ty @!!
      go!"onStop")) (Val #()))
  {{ RET #(); True }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
