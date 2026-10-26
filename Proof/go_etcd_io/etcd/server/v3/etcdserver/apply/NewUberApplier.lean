/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.NewUberApplier
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__restoreAlarms

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.NewUberApplier.wp_proof
    (hN : apply.newApplierV3.spec (GF := GF) (hG := hG))
    (hR : apply.uberApplier.restoreAlarms.spec (GF := GF) (hG := hG)) :
    apply.NewUberApplier.spec (GF := GF) (hG := hG) := by
  intro opts RD T z Hbuq
  wp_start as ⟨Hard, #HGet, HT⟩
  wp_auto
  wp_apply (hN opts RD Hbuq) $$ [Hard] as %base ⟨#Hshape, #Hbase, #HbAuth⟩
  · iframe
  ihave ⟨Hu, %Hun⟩ := typedPointsto_not_null_dup _ _ _ $$ «$r0»
  iStructNamed Hu
  ipersist lg
  ipersist alarmStore
  ipersist warningApplyDuration
  ipersist applyV3base
  wp_apply (hR «$r0_ptr» opts.AlarmStore' base _ T z) $$ [applyV3 HT]
    as ⟨HT, %ns, %cr, %a', %Hz, Ha', #Hchain, #Hsh⟩
  · iframe #
    iframe applyV3 HT
  iapply HΦ
  iframe HT
  iexists «$r0_ptr»
  isplitr
  · ipureintro; rfl
  iintro %E %hRD #Hopts
  ihave #Hb := Hbase $$ %E %hRD Hopts
  ihave #HbA := HbAuth $$ %E %hRD Hopts
  isplitr
  · iunfold apply.uberIs
    iframe #
    ipureintro; exact Hun
  iexists ns, cr
  isplitr
  · ipureintro; exact Hz
  iunfold apply.uberOwn
  iexists a'
  iframe Ha'
  isplitr
  · iapply Hchain $$ %E Hb
  isplitr
  · ipureintro
    cases ns <;> cases cr <;> simp [apply.alarmChain, apply.baseChain, apply.Chain.authOn]
  iunfold apply.uberShape
  iexists base, ns, cr
  iframe applyV3base Hsh
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
