/-
**The alarm store's `Get` with no alarm** (2026-11-01, J8a-5): `apply.alarmGetIs` at the user's
half at no alarm (`alarmEmpty a be`, which `NewAlarmStore` and `Recover` give), from
`v3alarm.AlarmStore.Get.spec`: `Get` returns an empty slice. The uber-applier's construction
takes it (`NewUberApplier`'s `alarmGetIs a T z ∗ T`, `z = true`), at boot and after a snapshot.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore__Get
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Assumptions]

theorem alarmGetIs_empty (hAG : v3alarm.AlarmStore.Get.spec (GF := GF) (hG := hG)) (a be : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm ∗
      isAlarmStore a ⊢ apply.alarmGetIs a (alarmEmpty a be) true := by
  iintro ⟨#Hpkg, #Ha⟩
  iunfold apply.alarmGetIs
  iintro !> %at' %Φ !> HT HΦ
  iapply hAG a at' (some be) $$ [HT] [HΦ]
  · iframe #; iexact HT
  inext
  iintro %sl ⟨HT, %Hz⟩
  iapply HΦ
  iframe HT
  ipureintro; intro _; exact Hz rfl

end proof

end EtcdGrove
end Perennial
