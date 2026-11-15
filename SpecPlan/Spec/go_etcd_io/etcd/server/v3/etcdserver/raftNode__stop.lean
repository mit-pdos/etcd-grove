/-
`(*raftNode).stop()` (`raft.go:420-430`): signal `stopped` (unless already done) and wait for `done`.

**Users**: `run`'s deferred shutdown (`server.go:807`... `s.r.stop()`). Snippet `restart.go`
(`ReqRestartContinues`).

**Proof sketch**: the stopper's send on `stopped` is received by the loop (or the loop has already
exited: `done` closed); `<-r.done` gives what `onStop` deposited: `rnStopped`.

**Changes** from `specs-ref`'s spec (the WAL's claim, `rnDoneTok`): over `rnStopper`/`rnStopped`.
**Margin**: none.
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

def raftNode.stop.spec : Prop :=
  ∀ (r : Loc) (γ : Names) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isRaftNode r γ id n ∗ rnStopper r }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.raftNode.ty @!!
      go!"stop")) (Val #()))
  {{ RET #(); rnStopped r γ id }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
