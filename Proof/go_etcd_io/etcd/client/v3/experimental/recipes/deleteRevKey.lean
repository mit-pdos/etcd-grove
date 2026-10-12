/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/deleteRevKey.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.deleteRevKey
public import Spec.go_etcd_io.etcd.client.v3.ModRevision
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.OpDelete
public import Spec.context.TODO
public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

private theorem B_conv {PROP : Type _} [BI PROP] (B : TxnBuild → PROP) (b b' : TxnBuild)
    (h : b = b') : B b ⊢ B b' := h ▸ .rfl

theorem deleteRevKey.wp_proof (hMR : EtcdGrove.ModRevision.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG))
    (hDel : EtcdGrove.OpDelete.spec (GF := GF) (hG := hG))
    (hTODO : EtcdGrove.context.TODO.spec (GF := GF) (hG := hG)) :
    deleteRevKey.spec (GF := GF) (hG := hG) := by
  intro kv pfx key rev lo
  wp_start as ⟨#Hkv, #Hlo, %Hk⟩
  iunfold isRecipesKV at Hkv
  icases Hkv with ⟨-, #HTxn, -, -⟩
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  have hrev0 : rev ≠ W64 0 := by intro h; rw [h] at Hk; exact absurd Hk.2 (by decide)
  wp_auto
  wp_apply hMR key $$ [$Hcv] as %c0 #Hc0
  (try wp_auto)
  wp_apply hCmp c0 _ go!"=" .eq _ (.num rev) $$ [$Hcv $Hc0] as %c1 #Hc1
  · ipureintro
    refine ⟨by simp [cmpOpOf], ?_⟩
    simp [cmpKeyM, cmpArgOf]
  (try wp_auto)
  ihave #Hnil := concurrency.optsAt_nil (GF := GF)
  wp_apply hDel key slice.nil [] $$ [$Hcv $Hnil] as %opDel #HopDel
  · ipureintro; exact concurrency.deleteOp_not_panics key
  (try wp_auto)
  wp_apply wp_slice_literal (l := [opDel])
  isplitr
  · ipureintro; rfl
  iintro %slT ⟨HslT, -⟩
  ipersist HslT
  (try wp_auto)
  wp_apply wp_slice_literal (l := [c1])
  isplitr
  · ipureintro; rfl
  iintro %slC ⟨HslC, -⟩
  ipersist HslC
  (try wp_auto)
  wp_apply hTODO
  (try wp_auto)
  iunfold isEtcdTxnKVTodo at HTxn
  wp_apply HTxn as %t ⟨%B, HB, #HBs, -⟩
  iunfold txnBuilderSpec at HBs
  icases HBs with ⟨#HIf, #HThen, -, #HCommit, -⟩
  wp_apply_raw HIf $$ %TxnBuild.empty %_ %([compareM (cmpKeyM .mod key) .eq (.num rev)] : List CmpModel) [$HB]
  · isplitl
    · unfold cmpsAt
      iexists [c1]
      iframe HslC
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %c %mm %Hc %Hmm
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hc Hmm; subst Hc Hmm; iexact Hc1
      · simp at Hc
    · ipureintro; simp [TxnBuild.empty]
  inext
  iintro HB
  (try wp_auto)
  wp_apply_raw HThen $$ %_ %_ %([opDeleteModel key []] : List OpFull) %([.delete (opDeleteModel key [])] : List TxnOp) [$HB]
  · isplitl
    · unfold opsAt
      iexists [opDel]
      iframe HslT
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %v %o %Hv %Ho
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho; subst Hv Ho; iexact HopDel
      · simp at Hv
    · ipureintro
      refine ⟨?_, rfl, rfl⟩
      simp [txnOpOf, opDeleteModel, opFold, OpFull.deleteInit, OpFull.newOp]
  inext
  iintro HB
  (try wp_auto)
  ihave HB := B_conv B _ ({ model := deleteRevTxn key rev, cif := true, cthen := true, celse := false } : TxnBuild) (by rfl) $$ HB
  wp_apply HCommit $$ %({ model := deleteRevTxn key rev, cif := true, cthen := true, celse := false } : TxnBuild) %lo [$HB $Hlo] as %resp %err Hres
  · ipureintro; exact deleteRevTxn_under pfx key rev Hk.1
  iunfold txnCommitResultTok at Hres
  icases Hres with (%Hne | ⟨%Heq, %r, %s0, #Hresp, #Hr, %Hrr, #Hts, Htok⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    (try wp_auto)
    iapply HΦ
    iright
    ipureintro; exact ⟨Hne, rfl⟩
  subst Heq
  have hm : ({ model := deleteRevTxn key rev, cif := true, cthen := true, celse := false } :
      TxnBuild).model = deleteRevTxn key rev := rfl
  rw [hm]
  obtain ⟨Hlo_r0, Hr0, Hrmax, Hwf0⟩ := Hrr
  have Hlo_r := Hlo_r0 rfl
  iunfold txnRespAt at Hresp
  icases Hresp with ⟨%hdr, %rsl, %ps, #HH, %Hhdr, #HRev, #HSucc, -, -, -, -⟩
  (try wp_auto)
  cases hok : (runTxn r s0 (deleteRevTxn key rev)).1
  · -- the key does not have mod revision `rev`
    obtain ⟨h1, h2⟩ := deleteRevTxn_else key rev r s0 hok
    have hgone := deleteRevTxn_else_gone pfx key rev r s0 Hwf0 hok
    ihave #Hs0 := txnStates_noWrite pfx r s0 _ _ h2 $$ Hts
    have hok' : (deleteRevTxn key rev).cmps.all (cmpHolds s0) = false := hok
    simp only [deleteRevTxn] at hok'
    rw [hok']
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists r
    iframe Hr
    isplitr
    · ipureintro; exact ⟨Hlo_r, Hrmax⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold revKeyGone
    iexists s0
    iframe Hs0
    ipureintro; exact hgone
  · -- claimed: present with mod revision `rev` at `r - 1`, absent at `r`
    obtain ⟨hpres, h2, habs⟩ := deleteRevTxn_then key rev r s0 hrev0 hok
    ihave ⟨#Hs0, #Hs1⟩ := txnStates_wrote pfx r s0 _ _ _ h2 rfl $$ Hts
    ihave Htok := tokIf_true h2 _ $$ Htok
    have hok' : (deleteRevTxn key rev).cmps.all (cmpHolds s0) = true := hok
    simp only [deleteRevTxn] at hok'
    rw [hok']
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists r
    iframe Hr
    isplitr
    · ipureintro; exact ⟨Hlo_r, Hrmax⟩
    simp only [↓reduceIte]
    iframe Htok
    unfold revKeyDeleted
    iexists s0, _
    iframe Hs0 Hs1
    ipureintro; exact ⟨Hr0, hpres, habs⟩

end proof

end recipes
end EtcdGrove
end Perennial
