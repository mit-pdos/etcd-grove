/-
Proof of `Spec/go_etcd_io/etcd/client/v3/ordering/kvOrdering__Txn.lean`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ordering.kvOrdering__Txn

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
variable [MutexCompositeLiteral]

theorem kvOrdering.Txn.wp_proof : kvOrdering.Txn.spec (GF := GF) (hG := hG) := by
  intro kvp kv vf ctx P Q
  wp_start as ⟨#Hkv, HP, Htxn_mk⟩
  iunfold isKvOrdering at Hkv
  icases Hkv with ⟨%Hkvp, #HKV, #Hvf_fld⟩
  iapply wp_fupd
  wp_auto
  wp_apply Htxn_mk $$ [$HP] as %innerTxn HQ
  (try wp_auto)
  wp_apply wp_slice_literal (l := ([] : List go_etcd_io.etcd.client.v3.Cmp))
  isplitr; · ipureintro; rfl
  iintro %csl ⟨Hcsl, -⟩
  ipersist Hcsl
  (try wp_auto)
  wp_apply wp_slice_literal (l := ([] : List go_etcd_io.etcd.client.v3.Op))
  isplitr; · ipureintro; rfl
  iintro %tsl ⟨Htsl, -⟩
  ipersist Htsl
  (try wp_auto)
  wp_apply wp_slice_literal (l := ([] : List go_etcd_io.etcd.client.v3.Op))
  isplitr; · ipureintro; rfl
  iintro %esl ⟨Hesl, -⟩
  ipersist Hesl
  (try wp_auto)
  wp_alloc txnp as Htxnp
  (try wp_auto)
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Htxnp
  iStructNamed Htxnp
  ipersist Txn
  ipersist kvOrdering
  ipersist ctx
  imod sync.init_Mutex iprop(True) ⊤
    (structFieldRef go_etcd_io.etcd.client.v3.ordering.txnOrdering go!"mu" txnp)
    $$ mu [] with #Hmu
  · inext; itrivial
  imodintro
  iapply HΦ $$ %txnp
  iexists innerTxn, _, _, _
  iframe HQ
  unfold ownTxnOrdering
  iframe Txn kvOrdering ctx Hmu cmps thenOps elseOps
  isplitr
  · ipureintro; exact Hnn
  isplitr
  · unfold cmpsAt
    iexists []
    iframe Hcsl
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %c %m %h
    simp at h
  isplitr
  · unfold opsTAt
    iexists []
    iframe Htsl
    unfold opListAtC; itrivial
  · unfold opsTAt
    iexists []
    iframe Hesl
    unfold opListAtC; itrivial

end proof

end ordering
end EtcdGrove
end Perennial
