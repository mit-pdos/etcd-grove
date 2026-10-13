/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__newHeader
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Rev
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.FrozenSpecs

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

theorem apply.applierV3backend.newHeader.wp_proof
    (hRev : mvcc.store.Rev.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG) := by
  have hRev := mvcc.store.Rev.spec_frozen hRev
  intro E p log
  wp_start as ⟨#Hb, Hrd, Hsw⟩
  iunfold apply.backendIs at Hb
  icases Hb with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨%Hlg, #Hkv, -, -, -, -, #Hcl, #Hrs, -⟩
  iStructNamed Hopts
  iunfold apply.isCluster at Hcl
  icases Hcl with ⟨%Hcn, -, #HID, -⟩
  iunfold apply.isRaftStatus at Hrs
  icases Hrs with ⟨%ri, %Hri, #HMem, #HLead, #HTerm⟩
  iunfold apply.isApplyKV at Hkv
  icases Hkv with ⟨#HisKV, %rv, #HRV, #Hrv⟩
  iunfold txn.isKV at HisKV
  icases HisKV with ⟨%Hkveq, #Hst⟩
  wp_auto
  wp_apply HID as %cid -
  rw [Hri]
  wp_auto
  wp_apply HMem as %mid -
  rw [Hkveq]
  wp_auto
  iunfold txn.soleWriter at Hsw
  icases Hsw with ⟨#Hcert, Htoks, %Hl2⟩
  wp_apply (hRev E.s rv E.γ (txn.soleBudget log) log) $$ [$Hrd $Htoks]
    as %v ⟨Hrd, Htoks, -⟩
  · iframe #
  wp_apply HTerm as %tm -
  wp_apply HLead as %ld -
  wp_alloc h as Hh
  wp_auto
  iapply HΦ
  iframe Hrd
  isplitl [Htoks]
  · iunfold txn.soleWriter
    iframe Htoks
    iframe #
    ipureintro; exact Hl2
  iapply typedPointsto_not_null $$ Hh

end proof

end EtcdGrove
end Perennial
