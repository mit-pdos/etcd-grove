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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.NewUberApplier.wp_proof
    (hN : apply.newApplierV3.spec (GF := GF) (hG := hG))
    (hR : apply.uberApplier.restoreAlarms.spec (GF := GF) (hG := hG)) :
    apply.NewUberApplier.spec (GF := GF) (hG := hG) := by
  intro E opts
  wp_start as #Hopts
  wp_auto
  wp_apply (hN E opts) $$ [] as %base #Hbase
  · iframe #
  ihave ⟨Hu, %Hun⟩ := typedPointsto_not_null_dup _ _ _ $$ «$r0»
  iStructNamed Hu
  ipersist lg
  ipersist alarmStore
  ipersist warningApplyDuration
  ipersist applyV3base
  ihave #Hui : iprop(apply.uberIs E «$r0_ptr» opts) $$ []
  · iunfold apply.uberIs
    iframe #
    ipureintro; exact Hun
  wp_apply (hR E «$r0_ptr» opts base) $$ [applyV3] as ⟨%ns, %cr, Hown⟩
  · iframe #
    iframe applyV3
  iapply HΦ
  iexists «$r0_ptr»
  iframe Hui
  isplitr
  · ipureintro; rfl
  iexists ns, cr
  iexact Hown

end proof

end EtcdGrove
end Perennial
