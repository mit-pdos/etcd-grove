/-
`(*EtcdServer).stopWithDelay(d, err)` (`server.go:1366-1375`): wait `d` or until `s.done` closes,
then try to send `err` on `s.errorc` (without blocking).

**Users**: `applyEntries` (`go s.stopWithDelay(10*s.Cfg.TickMs*time.Millisecond,
ErrStopped)` once the member applied its own removal: `run` then stops on `errorc`).

**Proof sketch**: `time.After` (Perennial's), `s.done` (`srvStarted`: 2e's `doneCh`, a receive gives
nothing); `s.errorc` (`srvNode_errorc`: 2f's `errChanOk`, a non-blocking send of any error).

**Changes**: verify round (A7-provability F7): new (cited by `applyEntries`' sketch).

**Margin**: none. The self-stop it triggers is A8-provability F3's case (`run`'s `errorc` arm closes
the backend while request-path calls may be in flight): `run.spec`'s scope, recorded in the repair
report.
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

/-- **`stopWithDelay(d, err)`**: after a delay, ask `run` to stop (if it still runs). -/
def EtcdServer.stopWithDelay.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (d : w64) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"stopWithDelay")) (Val #d)) (Val #err))
  {{ RET #(); True }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
