/-
Proof of `Spec/go_etcd_io/etcd/client/v3/ordering/txnOrdering__Else.lean`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ordering.txnOrdering__Else

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ordering

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.ordering

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.ordering.Assumptions]

theorem txnOrdering.Else.wp_proof : txnOrdering.Else.spec (GF := GF) (hG := hG) := by
  intro txnp kvp innerTxn ctx st esl' es' P Q
  wp_start as ⟨Htxn, #Hes', HP, Hinner⟩
  iunfold ownTxnOrdering at Htxn
  icases Htxn with ⟨%Htxnp, #HTxn_fld, #Hkvp_fld, #Hctx_fld, #Hmu, Hcmps_fld, #Hcmps, Hthen_fld, #Hts, Helse_fld, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, -⟩
  (try wp_auto)
  wp_apply Hinner $$ [$HP] as %_ HQ
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked]
  · inext; itrivial
  (try wp_auto)
  iapply HΦ
  iframe HQ
  unfold ownTxnOrdering
  iframe Hcmps_fld Hthen_fld Helse_fld
  iframe #
  ipureintro; exact Htxnp

end proof

end ordering
end EtcdGrove
end Perennial
