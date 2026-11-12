/-
`(*EtcdServer).ApplyWait(deadline)` (`interface.go:22-24`): `s.applyWait.Wait(deadline)`.

**Users**: the read loop (`readEnv`'s `ApplyWait` row: a read round waits until the member applied
its read index).

**Proof sketch**: the read-only field `s.applyWait` (`srvStarted`: the time list
`Wait.timeListAt tl (fun d => srvApplied s γ (uint.nat d))`, which `applyAll` triggers at each applied
index with `applyThread_applied`); `timeList.Wait.spec`.

**Changes**: verify round (A7-provability F4): new here (the old tree's
`EtcdServer__ApplyWait.lean`).

**Margin**: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply
public import SpecPlan.Spec.go_etcd_io.etcd.pkg.v3.wait.Api

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

/-- **`ApplyWait(d)`**: a channel closed once the member has applied the committed log through
`d`. -/
def EtcdServer.ApplyWait.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ srvStarted s γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"ApplyWait")) (Val #d))
  {{ (ch : Loc), RET #ch; Wait.timeChan ch (fun d' => srvApplied s γ (uint.nat d')) d }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
