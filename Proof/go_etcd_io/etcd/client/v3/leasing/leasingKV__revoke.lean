/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__revoke.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__revoke
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__waitRescind
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Rev
public import Spec.go_etcd_io.etcd.client.v3.CreateRevision
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.WithIgnoreLease
public import Spec.go_etcd_io.etcd.client.v3.OpPut
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.revoke.wp_proof
    (hRev : leaseCache.Rev.spec (GF := GF) (hG := hG))
    (hCR : EtcdGrove.CreateRevision.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG))
    (hWIL : EtcdGrove.WithIgnoreLease.spec (GF := GF) (hG := hG))
    (hPut : EtcdGrove.OpPut.spec (GF := GF) (hG := hG))
    (hWR : leasingKV.waitRescind.spec (GF := GF) (hG := hG)) :
    leasingKV.revoke.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs key opv o top lo
  wp_start as ⟨#Hlkv, Hrd, #Hctx, #Hcc, #Hop, #Hlo, %Htop⟩
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %lctx, %lcs, %cancel, %osl, %Hpfx, #Hcl, #Hkvf, #Hpfxf, #Hctxf,
    #Hcan, #Hosl, #HKV, #HDo, #HTxn, #HLC, #Hlctx, #Hlcc, #Hcache, #Hwg, #Hwginv, %Hbound⟩
  ihave #Hpeek := leasingX_peek (GF := GF) lkv γ
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (hRev (lkvLeases lkv) γ.lc pfx (leasingX lkv γ) (leasingSeen γ) key)
    $$ [$Hcache $Hrd $Hpeek] as %rv ⟨Hrd, %st, %Hrv, -, -⟩
  (try wp_auto)
  wp_apply wp_slice_literal (l := [opv])
  isplitr
  · ipureintro; rfl
  iintro %slT ⟨HslT, -⟩
  ipersist HslT
  (try wp_auto)
  wp_apply hCR (pfx ++ key) $$ [$Hcv] as %c0 #Hc0
  (try wp_auto)
  wp_apply hCmp c0 _ go!"<" .lt _ (.num (rv + W64 1)) $$ [$Hcv $Hc0] as %c1 #Hc1
  · ipureintro
    refine ⟨by simp [cmpOpOf], ?_⟩
    simp [cmpKeyM, cmpArgOf]
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
  wp_apply_raw HIf $$ %TxnBuild.empty %_ %([compareM (cmpKeyM .create (pfx ++ key)) .lt (.num (rv + W64 1))] : List CmpModel) [$HB]
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
  wp_apply hWIL $$ [$Hcv] as %f0 #Hf0
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f0])
  isplitr
  · ipureintro; rfl
  iintro %slo ⟨Hslo, -⟩
  ipersist Hslo
  (try wp_auto)
  ihave #Hopts : optsAt (GF := GF) _ [withIgnoreLeaseM] $$ []
  · unfold optsAt
    iexists [f0]
    iframe Hslo
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf Hg; subst Hf Hg; iexact Hf0
    · simp at Hf
  wp_apply hPut (pfx ++ key) go!"REVOKE" _ [withIgnoreLeaseM] $$ [$Hcv $Hopts] as %opR #HopR
  · ipureintro; exact revokeOp_not_panics (pfx ++ key)
  (try wp_auto)
  wp_apply wp_slice_literal (l := [opR])
  isplitr
  · ipureintro; rfl
  iintro %slE ⟨HslE, -⟩
  ipersist HslE
  (try wp_auto)
  ihave #HopsE : opsAt (GF := GF) _ [opPutModel (pfx ++ key) go!"REVOKE" [withIgnoreLeaseM]] $$ []
  · unfold opsAt
    iexists [opR]
    iframe HslE
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %v %oo %Hv %Ho
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho; subst Hv Ho; iexact HopR
    · simp at Hv
  have HmapE : [opPutModel (pfx ++ key) go!"REVOKE" [withIgnoreLeaseM]].map txnOpOf =
      [TxnOp.putKeep (pfx ++ key) go!"REVOKE"].map some := by simp [revokeOp_txnOpOf]
  ihave #HopsEE := opsAt_leaves _ _ _ HmapE $$ HopsE
  wp_apply_raw HElse $$ %_ %_ %([opPutModel (pfx ++ key) go!"REVOKE" [withIgnoreLeaseM]].map OpT.leaf) %([TxnOp.putKeep (pfx ++ key) go!"REVOKE"]) [$HB]
  · isplitl
    · iexact HopsEE
    · ipureintro
      refine ⟨txnOps_leaves _ _ HmapE, rfl⟩
  inext
  iintro HB
  (try wp_auto)
  ihave HB := B_conv B _ ({ model := ⟨[compareM (cmpKeyM .create (pfx ++ key)) .lt (.num (rv + W64 1))], [top], [TxnOp.putKeep (pfx ++ key) go!"REVOKE"]⟩, cif := true, cthen := true, celse := true } : TxnBuild) (by rfl) $$ HB
  wp_apply HCommit $$ %_ %lo [$HB $Hlo] as %resp %err Hres
  · ipureintro; exact TxnModel.under_nil _
  iunfold txnCommitResultO at Hres
  icases Hres with (⟨%Hne, -⟩ | ⟨%Heq, Hok⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    (try wp_auto)
    iapply HΦ
    iframe
    ileft; ipureintro; exact Hne
  subst Heq
  have Hlin : (TxnModel.linearizable ⟨[compareM (cmpKeyM .create (pfx ++ key)) .lt (.num (rv + W64 1))], [top], [TxnOp.putKeep (pfx ++ key) go!"REVOKE"]⟩) = true := by
    simp [TxnModel.linearizable, TxnOp.linearizable]
  icases txnCommitOk_guarded lo _ top _ resp Hlin $$ Hok with ⟨%ok, %hdr, %hm, #HH, #Hhf, %Hrb, HS, Hok⟩
  (try wp_auto)
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold hdrFull
    icases Hhf with ⟨%Hhn, -, -, #Hrev, -, -⟩
    (try wp_auto)
    wp_apply (hWR lkv γ pfx ctx cs key hm.revision) $$ [$Hlkv $Hctx $Hcc] as %err2 -
    · ipureintro; constructor <;> omega
    (try wp_auto)
    iapply HΦ
    iframe
    cases err2 with
    | ok e2 => ileft; ipureintro; simp
    | nil =>
      iright
      isplitr
      · ipureintro; rfl
      iright
      unfold notCommitted
      iexact HS
  · simp only [↓reduceIte]
    (try wp_auto)
    iapply HΦ
    iframe
    iright
    isplitr
    · ipureintro; rfl
    ileft
    iapply Hok $$ HS

end proof

end leasing
end EtcdGrove
end Perennial
