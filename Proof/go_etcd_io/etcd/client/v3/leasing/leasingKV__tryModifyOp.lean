/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__tryModifyOp.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__tryModifyOp
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Lock
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Evict
public import Spec.go_etcd_io.etcd.client.v3.Op__KeyBytes
public import Spec.go_etcd_io.etcd.client.v3.CreateRevision
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKVLemmas
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingPutLemmas

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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.tryModifyOp.wp_proof
    (hKey : EtcdGrove.Op.KeyBytes.spec (GF := GF) (hG := hG))
    (hLock : leaseCache.Lock.spec (GF := GF) (hG := hG))
    (hCR : EtcdGrove.CreateRevision.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG))
    (hEvict : leaseCache.Evict.spec (GF := GF) (hG := hG)) :
    leasingKV.tryModifyOp.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs opv o top lo
  wp_start as ⟨#Hlkv, #Hctx, #Hop, #Hlo, %Hpre⟩
  obtain ⟨Htop, Hot⟩ := Hpre
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %lctx, %lcs, %cancel, %osl, %Hpfx, #Hcl, #Hkvf, #Hpfxf, #Hctxf,
    #Hcan, #Hosl, #HKV, #HDo, #HTxn, #HLC, #Hlctx, #Hlcc, #Hcache, #Hwg, #Hwginv, %Hbound⟩
  ihave #Hpeek := leasingX_peek (GF := GF) lkv γ
  ihave #Hwaitc := leasingX_waitc (GF := GF) lkv γ
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply hKey $$ [$Hcv $op $Hop] as %ksl ⟨op, #Hk⟩
  wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
  (try wp_auto)
  wp_apply (hLock (lkvLeases lkv) γ.lc pfx (leasingX lkv γ) (leasingSeen γ) o.key)
    $$ [$Hcache $Hpeek $Hwaitc] as %wc %rv ⟨%st, %Hrv, -, -, Hwcres⟩
  (try wp_auto)
  wp_apply hCR (pfx ++ o.key) $$ [$Hcv] as %c0 #Hc0
  (try wp_auto)
  wp_apply hCmp c0 _ go!"<" .lt _ (.num (rv + W64 1)) $$ [$Hcv $Hc0] as %c1 #Hc1
  · ipureintro
    refine ⟨by simp [cmpOpOf], ?_⟩
    simp [cmpKeyM, cmpArgOf]
  (try wp_auto)
  wp_apply wp_slice_literal (l := [opv])
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
  iunfold isEtcdTxnKVO at HTxn
  wp_apply HTxn $$ %ctx %cs [$Hctx] as %t ⟨%B, HB, #HBs⟩
  iunfold txnBuilderSpecO at HBs
  icases HBs with ⟨#HIf, #HThen, #HElse, #HCommit⟩
  wp_apply_raw HIf $$ %TxnBuild.empty %_ %([compareM (cmpKeyM .create (pfx ++ o.key)) .lt (.num (rv + W64 1))] : List CmpModel) [$HB]
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
  ihave #HopsT : opsAt (GF := GF) _ [o] $$ []
  · unfold opsAt
    iexists [opv]
    iframe HslT
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %v %oo %Hv %Ho
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho; subst Hv Ho; iexact Hop
    · simp at Hv
  have Hmap : [o].map txnOpOf = [top].map some := by simp [Htop]
  ihave #HopsTT := opsAt_leaves _ [o] [top] Hmap $$ HopsT
  wp_apply_raw HThen $$ %_ %_ %([o].map OpT.leaf) %([top]) [$HB]
  · isplitl
    · iexact HopsTT
    · ipureintro
      refine ⟨txnOps_leaves [o] [top] Hmap, rfl, rfl⟩
  inext
  iintro HB
  (try wp_auto)
  ihave HB := B_conv B _ ({ model := ⟨[compareM (cmpKeyM .create (pfx ++ o.key)) .lt (.num (rv + W64 1))], [top], []⟩, cif := true, cthen := true, celse := false } : TxnBuild) (by rfl) $$ HB
  wp_apply HCommit $$ %_ %lo [$HB $Hlo] as %resp %err Hres
  · ipureintro; exact TxnModel.under_nil _
  ihave #Hstep : □ (∀ (st' : LeaseCacheSt) (tt : time.Time), leasingX lkv γ st' 1 ={⊤}=∗
      leasingX lkv γ (st'.evict o.key tt) 1 ∗ (fun _ => iprop(True)) st') $$ []
  · iintro !> %st' %tt HX
    imod leasingX_step (GF := GF) lkv γ st' (st'.evict o.key tt) $$ HX with ⟨HX, -⟩
    imodintro
    iframe
  iunfold txnCommitResultO at Hres
  icases Hres with (⟨%Hne, -⟩ | ⟨%Heq, Hok⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    (try wp_auto)
    wp_apply (hEvict (lkvLeases lkv) γ.lc pfx (leasingX lkv γ) (leasingSeen γ) o.key
      (fun _ => iprop(True))) $$ [$Hcache $Hpeek $Hstep] as %_ -
    icases Hwcres with (⟨%Hn, %Hwc⟩ | ⟨%Hs, Hwc⟩)
    · subst Hwc
      (try wp_auto)
      iapply HΦ
      ileft; ipureintro; exact ⟨rfl, rfl⟩
    · (try wp_auto)
      wp_if_destruct
      · iapply HΦ
        ileft; ipureintro; exact ⟨rfl, rfl⟩
      · unfold waitcClose
        icases Hwc with ⟨%γch, Hwc⟩
        wp_apply wp_broadcast_chan_close $$ [$Hwc] as -
        · unfold waitQ; imodintro; itrivial
        (try wp_auto)
        iapply HΦ
        ileft; ipureintro; exact ⟨rfl, rfl⟩
  subst Heq
  have Hlin : (TxnModel.linearizable ⟨[compareM (cmpKeyM .create (pfx ++ o.key)) .lt (.num (rv + W64 1))], [top], []⟩) = true := by
    simp [TxnModel.linearizable, txnOpOf_write_lin Htop Hot]
  icases txnCommitOk_guarded lo _ top [] resp Hlin $$ Hok with ⟨%ok, %hdr, %hm, -, -, HS, Hok⟩
  (try wp_auto)
  cases ok
  · (try wp_auto)
    icases Hwcres with (⟨%Hn, %Hwc⟩ | ⟨%Hs, Hwc⟩)
    · subst Hwc
      (try wp_auto)
      iapply HΦ
      ileft; ipureintro; exact ⟨rfl, rfl⟩
    · (try wp_auto)
      wp_if_destruct
      · iapply HΦ
        ileft; ipureintro; exact ⟨rfl, rfl⟩
      · unfold waitcClose
        icases Hwc with ⟨%γch, Hwc⟩
        wp_apply wp_broadcast_chan_close $$ [$Hwc] as -
        · unfold waitQ; imodintro; itrivial
        (try wp_auto)
        iapply HΦ
        ileft; ipureintro; exact ⟨rfl, rfl⟩
  · simp only [↓reduceIte]
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    isplitl [Hok HS]
    · iapply Hok $$ HS
    icases Hwcres with (⟨%Hn, %Hwc⟩ | ⟨%Hs, Hwc⟩)
    · ileft; ipureintro; exact Hwc
    · iright; iexact Hwc

end proof

end leasing
end EtcdGrove
end Perennial
