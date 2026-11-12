/-
## `(*EtcdServer).Alarms()` (`server.go:2455-2457`): translated

**Users.** 2a's maintenance `Status` (its `Errors`). **Proof sketch.** `alarmStore.Get(NONE)`
(`V3alarm.AlarmStore.Get.spec`, its update fired by the server's invariant). **Changes**: new.
**Margin.** The alarms are the member's view at some point (not tied to `State.alarms` here).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Api

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

/-- **The member's raised alarms** (read-only). -/
def EtcdServer.Alarms.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Alarms")) (Val #()))
  {{ (sl : GoSlice), RET #sl; threadTok ∗ ∃ (ps : List Loc) (l : List Alarm), sl ↦* ps ∗
      ([∗list] pa ∈ ps.zip l, V3alarm.alarmMemberRO pa.1 pa.2) ∗ ⌜ps.length = l.length⌝ }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
