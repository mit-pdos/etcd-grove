/-
Top-level linked theorems for `go.etcd.io/etcd/client/v3/ordering` (`etcd-io/etcd#22122`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ordering.NewKV
public import Proof.go_etcd_io.etcd.client.v3.ordering.kvOrdering__getPrevRev
public import Proof.go_etcd_io.etcd.client.v3.ordering.kvOrdering__setPrevRev
public import Proof.go_etcd_io.etcd.client.v3.ordering.kvOrdering__GetStream
public import Proof.go_etcd_io.etcd.client.v3.ordering.kvOrdering__Get
public import Proof.go_etcd_io.etcd.client.v3.ordering.kvOrdering__Txn
public import Proof.go_etcd_io.etcd.client.v3.ordering.txnOrdering__If
public import Proof.go_etcd_io.etcd.client.v3.ordering.txnOrdering__Then
public import Proof.go_etcd_io.etcd.client.v3.ordering.txnOrdering__Else
public import Proof.go_etcd_io.etcd.client.v3.ordering.txnOrdering__Commit
public import Proof.go_etcd_io.etcd.client.v3.ordering.isReadOnly
public import Proof.go_etcd_io.etcd.client.v3.Op__IsGet
public import Proof.go_etcd_io.etcd.client.v3.Op__IsTxn
public import Proof.go_etcd_io.etcd.client.v3.Op__Txn
public import Proof.go_etcd_io.etcd.client.v3.OpTxn
public import Proof.go_etcd_io.etcd.client.v3.OpResponse__Get
public import Proof.go_etcd_io.etcd.client.v3.OpResponse__Txn
public import Proof.go_etcd_io.etcd.client.v3.Link
public import Proof.google_golang_org.grpc.status.Error

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ordering

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.ordering go_etcd_io.etcd.api.v3

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.ordering.Assumptions]
variable [go_etcd_io.etcd.client.v3.OpResponseTxnBody]
variable [MutexCompositeLiteral]

/-- Linked proof of `ordering.NewKV`. -/
theorem wp_NewKV : NewKV.spec (GF := GF) (hG := hG) :=
  NewKV.wp_proof

/-- Linked proof of `(*kvOrdering).getPrevRev`. -/
theorem wp_kvOrdering_getPrevRev : kvOrdering.getPrevRev.spec (GF := GF) (hG := hG) :=
  kvOrdering.getPrevRev.wp_proof

/-- Linked proof of `(*kvOrdering).setPrevRev`. -/
theorem wp_kvOrdering_setPrevRev : kvOrdering.setPrevRev.spec (GF := GF) (hG := hG) :=
  kvOrdering.setPrevRev.wp_proof

/-- Linked proof of `(*kvOrdering).GetStream`. -/
theorem wp_kvOrdering_GetStream : kvOrdering.GetStream.spec (GF := GF) (hG := hG) :=
  kvOrdering.GetStream.wp_proof EtcdGrove.status.Error.wp_proof

/-- Linked proof of `ordering.isReadOnly`. -/
theorem wp_isReadOnly : isReadOnly.spec (GF := GF) (hG := hG) :=
  isReadOnly.wp_proof
    EtcdGrove.Op.IsGet.wp_proof
    EtcdGrove.Op.IsTxn.wp_proof
    EtcdGrove.Op.Txn.wp_proof

/-- Linked proof of `(*kvOrdering).Get`. -/
theorem wp_kvOrdering_Get : kvOrdering.Get.spec (GF := GF) (hG := hG) :=
  kvOrdering.Get.wp_proof
    wp_kvOrdering_getPrevRev
    wp_kvOrdering_setPrevRev
    EtcdGrove.client.v3.wp_OpGet
    EtcdGrove.OpResponse.Get.wp_proof

/-- Linked proof of `(*kvOrdering).Txn`. -/
theorem wp_kvOrdering_Txn : kvOrdering.Txn.spec (GF := GF) (hG := hG) :=
  kvOrdering.Txn.wp_proof

/-- Linked proof of `(*txnOrdering).If`. -/
theorem wp_txnOrdering_If : txnOrdering.If.spec (GF := GF) (hG := hG) :=
  txnOrdering.If.wp_proof

/-- Linked proof of `(*txnOrdering).Then`. -/
theorem wp_txnOrdering_Then : txnOrdering.Then.spec (GF := GF) (hG := hG) :=
  txnOrdering.Then.wp_proof

/-- Linked proof of `(*txnOrdering).Else`. -/
theorem wp_txnOrdering_Else : txnOrdering.Else.spec (GF := GF) (hG := hG) :=
  txnOrdering.Else.wp_proof

/-- Linked proof of `(*txnOrdering).Commit`. -/
theorem wp_txnOrdering_Commit : txnOrdering.Commit.spec (GF := GF) (hG := hG) :=
  txnOrdering.Commit.wp_proof
    wp_kvOrdering_getPrevRev
    wp_kvOrdering_setPrevRev
    (EtcdGrove.OpTxn.wp_proof EtcdGrove.client.v3.Cmp.wp_Clone)
    wp_isReadOnly
    EtcdGrove.OpResponse.Txn.wp_proof

/-- **Corollary 1 (PR #22122 — Mutable Transactions Executed At Most Once)**:
When `isReadOnlyM (.txn OpFull.txnInit st.ms st.ts st.es) = false` (i.e., `∃ o ∈ leaves, o.t ≠ W64 1`),
`txn.Commit()` requires only a **single linear** execution token `P : IProp GF` consumed by
`kvDoTxnSpec` — proving in separation logic that `txn.KV.Do` is never re-executed even if
`txnResp.Header.Revision < prevRev` and `orderViolationFunc` returns `nil`. -/
theorem wp_txnOrdering_Commit_mutable_at_most_once
    (txnp kvp : Loc) (innerTxn : go_etcd_io.etcd.client.v3.Txn)
    (kv : go_etcd_io.etcd.client.v3.KV) (vf : OrderViolationFunc)
    (ctx : context.Context) (st : TxnOrderingState)
    (hmut : isReadOnlyM (.txn OpFull.txnInit st.ms st.ts st.es) = false)
    (R : w64 → IProp GF) (P : IProp GF)
    (PostOk : Loc → w64 → IProp GF) (PostErr : GoInterface → IProp GF) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.ordering ∗
      isKvOrdering kvp kv vf ∗
      ownTxnOrdering txnp kvp innerTxn ctx st ∗
      kvOrderingHandle kvp R ∗
      P ∗
      kvDoTxnSpec kv ctx st.ms st.ts st.es R P PostOk PostErr ∗
      orderViolationSpec vf R PostErr }}
    (App (Val (txnp @!! go.GoType.PointerType txnOrdering.ty @!! go!"Commit")) (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      ownTxnOrdering txnp kvp innerTxn ctx st ∗
      kvOrderingHandle kvp R ∗
      if decide (err = GoInterface.nil) then
        ∃ (prevRev rev : w64) (hdr : Loc),
          ⌜resp ≠ null ∧ hdr ≠ null⌝ ∗
          structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ hdr ∗
          structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdr ↦□ rev ∗
          □ R prevRev ∗ □ R rev ∗ PostOk resp rev
      else
        ⌜resp = null⌝ ∗ PostErr err }} := by
  wp_start_folded as ⟨#Hkv, Htxn, Hrw, HP, #Hdo, #Hvf⟩
  wp_apply (wp_txnOrdering_Commit txnp kvp innerTxn kv vf ctx st R P PostOk PostErr)
    $$ [$Hkv $Htxn $Hrw HP $Hdo $Hvf] as %resp %err ⟨Htxn, Hrw, Hres⟩
  · simp only [hmut, Bool.false_eq_true, ↓reduceIte]; iexact HP
  iapply HΦ
  iframe Htxn Hrw
  by_cases herr : err = GoInterface.nil
  · subst herr
    simp only [_root_.decide_true, ↓reduceIte]
    icases Hres with ⟨%prevRev, %rev, %hdr, ⟨%Hresp, %Hhdr, -⟩, #Hhdr_fld, #Hrev_fld, #HRprev, #HRrev, Hok⟩
    iexists prevRev, rev, hdr
    iframe #
    iframe Hok
    ipureintro; exact ⟨Hresp, Hhdr⟩
  · simp only [decide_eq_false herr, Bool.false_eq_true, ↓reduceIte]
    iexact Hres

/-- **Corollary 2 (Read-Only Transactions Guarantee Revision Monotonicity)**:
When `isReadOnlyM (.txn OpFull.txnInit st.ms st.ts st.es) = true` (i.e., `∀ o ∈ leaves, o.t = W64 1`),
`txn.Commit()` retries on ordering violations (requiring persistent `□ P`) and guarantees
`sint.Z prevRev ≤ sint.Z rev` on any `nil`-error return. -/
theorem wp_txnOrdering_Commit_readOnly_monotonic
    (txnp kvp : Loc) (innerTxn : go_etcd_io.etcd.client.v3.Txn)
    (kv : go_etcd_io.etcd.client.v3.KV) (vf : OrderViolationFunc)
    (ctx : context.Context) (st : TxnOrderingState)
    (hro : isReadOnlyM (.txn OpFull.txnInit st.ms st.ts st.es) = true)
    (R : w64 → IProp GF) (P : IProp GF)
    (PostOk : Loc → w64 → IProp GF) (PostErr : GoInterface → IProp GF) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.ordering ∗
      isKvOrdering kvp kv vf ∗
      ownTxnOrdering txnp kvp innerTxn ctx st ∗
      kvOrderingHandle kvp R ∗
      □ P ∗
      kvDoTxnSpec kv ctx st.ms st.ts st.es R P PostOk PostErr ∗
      orderViolationSpec vf R PostErr }}
    (App (Val (txnp @!! go.GoType.PointerType txnOrdering.ty @!! go!"Commit")) (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      ownTxnOrdering txnp kvp innerTxn ctx st ∗
      kvOrderingHandle kvp R ∗
      if decide (err = GoInterface.nil) then
        ∃ (prevRev rev : w64) (hdr : Loc),
          ⌜resp ≠ null ∧ hdr ≠ null ∧ sint.Z prevRev ≤ sint.Z rev⌝ ∗
          structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ hdr ∗
          structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdr ↦□ rev ∗
          □ R prevRev ∗ □ R rev ∗ PostOk resp rev
      else
        ⌜resp = null⌝ ∗ PostErr err }} := by
  wp_start_folded as ⟨#Hkv, Htxn, Hrw, #HP, #Hdo, #Hvf⟩
  wp_apply (wp_txnOrdering_Commit txnp kvp innerTxn kv vf ctx st R P PostOk PostErr)
    $$ [$Hkv $Htxn $Hrw $Hdo $Hvf] as %resp %err ⟨Htxn, Hrw, Hres⟩
  · simp only [hro, ↓reduceIte]; iexact HP
  iapply HΦ
  iframe Htxn Hrw
  by_cases herr : err = GoInterface.nil
  · subst herr
    simp only [_root_.decide_true, ↓reduceIte]
    icases Hres with ⟨%prevRev, %rev, %hdr, ⟨%Hresp, %Hhdr, %Hle⟩, #Hhdr_fld, #Hrev_fld, #HRprev, #HRrev, Hok⟩
    iexists prevRev, rev, hdr
    iframe #
    iframe Hok
    ipureintro; exact ⟨Hresp, Hhdr, Hle hro⟩
  · simp only [decide_eq_false herr, Bool.false_eq_true, ↓reduceIte]
    iexact Hres

#print axioms isReadOnlyM_iff_leaves
#print axioms isReadOnlyM_false_iff_exists_non_get
#print axioms wp_NewKV
#print axioms wp_kvOrdering_getPrevRev
#print axioms wp_kvOrdering_setPrevRev
#print axioms wp_kvOrdering_GetStream
#print axioms wp_isReadOnly
#print axioms wp_kvOrdering_Get
#print axioms wp_kvOrdering_Txn
#print axioms wp_txnOrdering_If
#print axioms wp_txnOrdering_Then
#print axioms wp_txnOrdering_Else
#print axioms wp_txnOrdering_Commit
#print axioms wp_txnOrdering_Commit_mutable_at_most_once
#print axioms wp_txnOrdering_Commit_readOnly_monotonic

end results

end ordering
end EtcdGrove
end Perennial
