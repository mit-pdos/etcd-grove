/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__rescind.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__rescind
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Evict
public import Spec.go_etcd_io.etcd.client.v3.CreateRevision
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.OpDelete
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKVLemmas
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingPutLemmas
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

private theorem B_conv {PROP : Type _} [BI PROP] (B : TxnBuild → PROP) (b b' : TxnBuild)
    (h : b = b') : B b ⊢ B b' := h ▸ .rfl

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.rescind.wp_proof
    (hEvict : leaseCache.Evict.spec (GF := GF) (hG := hG))
    (hCR : EtcdGrove.CreateRevision.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG))
    (hDel : EtcdGrove.OpDelete.spec (GF := GF) (hG := hG)) :
    leasingKV.rescind.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs key rev
  wp_start as ⟨#Hlkv, #Hctx⟩
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %lctx, %lcs, %cancel, %osl, %Hpfx, #Hcl, #Hkvf, #Hpfxf, #Hctxf,
    #Hcan, #Hosl, #HKV, #HDo, #HTxn, #HLC, #Hlctx, #Hlcc, #Hcache, #Hwg, #Hwginv, %Hbound⟩
  ihave #Hpeek := leasingX_peek (GF := GF) lkv γ
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hstep : □ (∀ (st' : LeaseCacheSt) (tt : time.Time), leasingX lkv γ st' 1 ={⊤}=∗
      leasingX lkv γ (st'.evict key tt) 1 ∗ (fun _ => iprop(True)) st') $$ []
  · iintro !> %st' %tt HX
    imod leasingX_step (GF := GF) lkv γ st' (st'.evict key tt) $$ HX with ⟨HX, -⟩
    imodintro
    iframe
  (try wp_auto)
  wp_apply (hEvict (lkvLeases lkv) γ.lc pfx (leasingX lkv γ) (leasingSeen γ) key
    (fun _ => iprop(True))) $$ [$Hcache $Hpeek $Hstep] as %r0 -
  (try wp_auto)
  wp_if_destruct
  · iapply HΦ; itrivial
  wp_apply hCR (pfx ++ key) $$ [$Hcv] as %c0 #Hc0
  (try wp_auto)
  wp_apply hCmp c0 _ go!"<" .lt _ (.num rev) $$ [$Hcv $Hc0] as %c1 #Hc1
  · ipureintro
    refine ⟨by simp [cmpOpOf], ?_⟩
    simp [cmpKeyM, cmpArgOf]
  (try wp_auto)
  ihave #Hopt0 : optsAt (GF := GF) slice.nil ([] : List (OpFull → OpFull)) $$ []
  · iapply concurrency.optsAt_nil
  wp_apply hDel (pfx ++ key) slice.nil [] $$ [$Hcv $Hopt0] as %opD #HopD
  · ipureintro
    simp [opDeletePanics, opGetPanics, opFold, OpFull.newOp, opDeleteModel, OpFull.deleteInit,
      OpFull.deletePanics, OpModel.zero]
  (try wp_auto)
  ihave #Hlo := etcdReached_zero (GF := GF)
  have Hd : txnOpOf (opDeleteModel (pfx ++ key) []) =
      some (.delete (opDeleteModel (pfx ++ key) [])) := by
    simp [txnOpOf, opDeleteModel, opFold, OpFull.deleteInit, OpFull.newOp]
  iunfold isEtcdTxnKVO at HTxn
  ihave #Hctx2 := Hctx
  iNamed Hctx2
  ihave #HErrU := HErr $$ %Broadcast.Unknown
  wp_for
  wp_apply HErrU as %cerr -
  cases cerr with
  | ok e =>
    (try wp_auto)
    simp only [goose_wp_simp_extra, Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    iapply HΦ; itrivial
  | nil =>
    (try wp_auto)
    simp only [goose_wp_simp_extra, ↓reduceIte]
    (try wp_auto)
    wp_apply wp_slice_literal (l := [opD])
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
    wp_apply HTxn $$ %ctx %cs [$Hctx] as %t ⟨%B, HB, #HBs⟩
    iunfold txnBuilderSpecO at HBs
    icases HBs with ⟨#HIf, #HThen, -, #HCommit⟩
    wp_apply_raw HIf $$ %TxnBuild.empty %_
        %([compareM (cmpKeyM .create (pfx ++ key)) .lt (.num rev)] : List CmpModel) [$HB]
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
    have Hmap : [opDeleteModel (pfx ++ key) []].map txnOpOf =
        [TxnOp.delete (opDeleteModel (pfx ++ key) [])].map some := by simp [Hd]
    ihave #HopsT := opsAt_leaves (GF := GF) _ _ _ Hmap $$ []
    · unfold opsAt
      iexists [opD]
      iframe HslT
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %v %o %Hv %Ho
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho; subst Hv Ho; iexact HopD
      · simp at Hv
    wp_apply_raw HThen $$ %_ %_ %_ %([TxnOp.delete (opDeleteModel (pfx ++ key) [])]) [$HB]
    · isplitl
      · iexact HopsT
      · ipureintro
        refine ⟨txnOps_leaves _ _ Hmap, rfl, rfl⟩
    inext
    iintro HB
    (try wp_auto)
    wp_apply HCommit $$ %_ %(W64 0) [$HB $Hlo] as %resp %err Hres
    · ipureintro; exact TxnModel.under_nil _
    (try wp_auto)
    cases err with
    | nil =>
      (try wp_auto)
      wp_for_post
      iapply HΦ; itrivial
    | ok e =>
      (try wp_auto)
      wp_for_post
      iframe

end proof

end leasing
end EtcdGrove
end Perennial
