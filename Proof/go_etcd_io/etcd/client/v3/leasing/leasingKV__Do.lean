/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__Do.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__Do
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__get
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__put
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__delete
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__Txn
public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__If
public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__Then
public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__Else
public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__Commit
public import Spec.go_etcd_io.etcd.client.v3.Op__IsGet
public import Spec.go_etcd_io.etcd.client.v3.Op__IsPut
public import Spec.go_etcd_io.etcd.client.v3.Op__IsDelete
public import Spec.go_etcd_io.etcd.client.v3.Op__IsTxn
public import Spec.go_etcd_io.etcd.client.v3.Op__Txn
public import Spec.go_etcd_io.etcd.client.v3.GetResponse__OpResponse
public import Spec.go_etcd_io.etcd.client.v3.PutResponse__OpResponse
public import Spec.go_etcd_io.etcd.client.v3.DeleteResponse__OpResponse
public import Spec.go_etcd_io.etcd.client.v3.TxnResponse__OpResponse

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

private theorem ownTxnLeasing_conv (txn lkv : Loc) (γ : LeasingNames) (pfx : GoString)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (b b' : LTxnBuild) (h : b = b') :
    ownTxnLeasing (GF := GF) txn lkv γ pfx ctx cs b ⊢ ownTxnLeasing txn lkv γ pfx ctx cs b' :=
  h ▸ .rfl

theorem leasingKV.Do.wp_proof
    (hIsGet : EtcdGrove.Op.IsGet.spec (GF := GF) (hG := hG))
    (hget : leasingKV.get.spec (GF := GF) (hG := hG))
    (hGOR : EtcdGrove.GetResponse.OpResponse.spec (GF := GF) (hG := hG))
    (hIsPut : EtcdGrove.Op.IsPut.spec (GF := GF) (hG := hG))
    (hput : leasingKV.put.spec (GF := GF) (hG := hG))
    (hPOR : EtcdGrove.PutResponse.OpResponse.spec (GF := GF) (hG := hG))
    (hIsDel : EtcdGrove.Op.IsDelete.spec (GF := GF) (hG := hG))
    (hdel : leasingKV.delete.spec (GF := GF) (hG := hG))
    (hDOR : EtcdGrove.DeleteResponse.OpResponse.spec (GF := GF) (hG := hG))
    (hIsTxn : EtcdGrove.Op.IsTxn.spec (GF := GF) (hG := hG))
    (hOpTxn : EtcdGrove.Op.Txn.spec (GF := GF) (hG := hG))
    (hTxn : leasingKV.Txn.spec (GF := GF) (hG := hG))
    (hIf : txnLeasing.If.spec (GF := GF) (hG := hG))
    (hThen : txnLeasing.Then.spec (GF := GF) (hG := hG))
    (hElse : txnLeasing.Else.spec (GF := GF) (hG := hG))
    (hCommit : txnLeasing.Commit.spec (GF := GF) (hG := hG))
    (hTOR : EtcdGrove.TxnResponse.OpResponse.spec (GF := GF) (hG := hG)) :
    leasingKV.Do.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs opv o lo q
  wp_start as ⟨#Hlkv, Hrd, Hslot, #Hctx, #Hcc, #Hop, #Hlo, Hopen, Htok, %Hput, Htxn⟩
  wp_auto
  ipersist lkv
  ipersist op
  ipersist ctx
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_apply hIsGet $$ [$Hcv $op $Hop] as op
  by_cases h1 : o.t = W64 1
  · simp only [decide_eq_true h1, decide_eq_self_any]
    wp_auto
    wp_apply hget lkv γ pfx ctx cs opv o lo q $$ [$Hpkg $Hlkv $Hrd $Hslot $Hctx $Hop $Hlo $Hopen $Htok]
      as %ret %err ⟨Hrd, Hopen, Htok, Hout⟩
    · ipureintro; exact h1
    try wp_auto
    wp_apply hGOR $$ [$Hcv]
    try wp_auto
    iapply HΦ
    rw [if_pos h1]
    iframe
  simp only [decide_eq_false h1, Bool.true_eq_false, decide_False_any]
  wp_auto
  wp_apply hIsPut $$ [$Hcv $op $Hop] as op
  by_cases h2 : o.t = W64 2
  · simp only [decide_eq_true h2, decide_eq_self_any]
    obtain ⟨top, htop⟩ := Option.ne_none_iff_exists'.1 (Hput h2)
    wp_auto
    wp_apply hput lkv γ pfx ctx cs opv o top lo $$ [$Hpkg $Hlkv $Hrd $Hctx $Hcc $Hop $Hlo]
      as %pr %err ⟨Hrd, Hout⟩
    · ipureintro; exact ⟨h2, htop⟩
    try wp_auto
    wp_apply hPOR $$ [$Hcv]
    try wp_auto
    iapply HΦ
    rw [if_neg h1, if_pos h2]
    iframe
    icases Hout with (%Hne | ⟨%Heq, Hc⟩)
    · ileft; ipureintro; exact Hne
    · iright
      iframe
      isplitr
      · ipureintro; exact Heq
      ipureintro; exact htop
  simp only [decide_eq_false h2, Bool.true_eq_false, decide_False_any]
  wp_auto
  wp_apply hIsDel $$ [$Hcv $op $Hop] as op
  by_cases h3 : o.t = W64 3
  · simp only [decide_eq_true h3, decide_eq_self_any]
    wp_auto
    wp_apply hdel lkv γ pfx ctx cs opv o lo $$ [$Hpkg $Hlkv $Hrd $Hctx $Hcc $Hop $Hlo]
      as %dr %err ⟨Hrd, Hout⟩
    · ipureintro; exact h3
    try wp_auto
    wp_apply hDOR $$ [$Hcv]
    try wp_auto
    iapply HΦ
    rw [if_neg h1, if_neg h2, if_pos h3]
    iframe
  simp only [decide_eq_false h3, Bool.true_eq_false, decide_False_any]
  wp_auto
  wp_apply hIsTxn $$ [$Hcv $op $Hop] as op
  by_cases h4 : o.t = W64 4
  · simp only [decide_eq_true h4, decide_eq_self_any]
    ihave Htxn := Htxn $$ [] 
    · ipureintro; exact h4
    iunfold doTxnPre at Htxn
    icases Htxn with ⟨%ms, %tos, %eos, %tops, %eops, #Hcmps, #Htos, #Heos, %Hops⟩
    try wp_auto
    wp_apply hOpTxn $$ [$Hcv $op] as op
    try wp_auto
    wp_apply hTxn lkv γ pfx ctx cs $$ [$Hpkg $Hlkv $Hctx] as %txn Ht
    try wp_auto
    wp_apply hIf txn lkv γ pfx ctx cs LTxnBuild.empty opv.cmps' ms $$ [$Hpkg $Ht $Hcmps] as Ht
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    try wp_auto
    wp_apply hThen txn lkv γ pfx ctx cs _ opv.thenOps' tos tops $$ [$Hpkg $Ht $Htos] as Ht
    · ipureintro; exact ⟨Hops.1, rfl, rfl⟩
    try wp_auto
    wp_apply hElse txn lkv γ pfx ctx cs _ opv.elseOps' eos eops $$ [$Hpkg $Ht $Heos] as Ht
    · ipureintro; exact ⟨Hops.2.1, rfl⟩
    try wp_auto
    ihave Ht := ownTxnLeasing_conv txn lkv γ pfx ctx cs
      (LTxnBuild.mk ([] ++ ms) ([] ++ tos) ([] ++ eos) true true true)
      (LTxnBuild.mk ms tos eos true true true) rfl $$ Ht
    wp_apply hCommit txn lkv γ pfx ctx cs (LTxnBuild.mk ms tos eos true true true) lo
      $$ [$Hpkg $Ht $Hrd $Hcc $Hlo] as %resp %err ⟨Hrd, Hout⟩
    · ipureintro; exact Hops.2.2
    try wp_auto
    wp_apply hTOR $$ [$Hcv]
    try wp_auto
    iapply HΦ
    rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    iframe
    iframe #
  simp only [decide_eq_false h4, Bool.true_eq_false, decide_False_any]
  wp_auto
  iapply HΦ
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  iframe
  ipureintro; exact ⟨rfl, rfl⟩

end proof

end leasing
end EtcdGrove
end Perennial
