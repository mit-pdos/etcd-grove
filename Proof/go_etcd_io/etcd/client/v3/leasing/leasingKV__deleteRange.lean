/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__deleteRange.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__deleteRange
public import Spec.go_etcd_io.etcd.client.v3.Op__KeyBytes
public import Spec.go_etcd_io.etcd.client.v3.Op__RangeBytes
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__revokeRange
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__LockRange
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__deleteRangeRPC
public import Spec.go_etcd_io.etcd.client.v3.leasing.closeAll
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKVLemmas
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingDeleteLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.deleteRange.wp_proof
    (hKey : EtcdGrove.Op.KeyBytes.spec (GF := GF) (hG := hG))
    (hRange : EtcdGrove.Op.RangeBytes.spec (GF := GF) (hG := hG))
    (hRR : leasingKV.revokeRange.spec (GF := GF) (hG := hG))
    (hLR : leaseCache.LockRange.spec (GF := GF) (hG := hG))
    (hRPC : leasingKV.deleteRangeRPC.spec (GF := GF) (hG := hG))
    (hCA : closeAll.spec (GF := GF) (hG := hG)) :
    leasingKV.deleteRange.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs opv o lo
  wp_start as ⟨#Hlkv, Hrd, #Hsr, #Hctx, #Hcc, #Hop, #Hlo⟩
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %lctx, %lcs, %cancel, %osl, %Hpfx, -, -, -, -, -, -, -, -,
    -, -, -, -, #Hlc, -⟩
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hctx2 := Hctx
  iNamed Hctx2
  ihave #Hop' := Hop
  iunfold opFullAt at Hop'
  icases Hop' with ⟨#HopAt, -⟩
  (try wp_auto)
  wp_apply hKey $$ [$Hcv $op $Hop] as %ksl ⟨op, #Hk⟩
  wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
  wp_apply hRange $$ [$Hcv $op $HopAt] as %esl ⟨op, #He⟩
  wp_apply wp_bytes_to_string esl o.base.rangeEnd DFrac.discard $$ [$He] as -
  (try wp_auto)
  ihave #Hpeek := leasingX_peek (GF := GF) lkv γ
  ihave #Hwst := leasingX_waitc (GF := GF) lkv γ
  ihave IH : iprop("Hrd" ∷ lkvReader lkv γ pfx ∗ "ctx" ∷ ctx_ptr ↦ GoInterface.ok ctx ∗
      "lkv" ∷ lkv_ptr ↦ lkv ∗ "key" ∷ key_ptr ↦ o.key ∗ "Hend" ∷ end_ptr ↦ o.base.rangeEnd)
      $$ [Hrd ctx lkv key «end»]
  · simp only [named]; iframe
  wp_for IH
  ihave #HErrU := HErr $$ %Broadcast.Unknown
  wp_apply HErrU as %cerr Hcerr
  cases cerr with
  | ok e =>
    rw [if_neg (show GoInterface.ok e ≠ GoInterface.nil from fun h => by cases h)]
    icases Hcerr with ⟨#HPD, #HCC⟩
    (try wp_auto)
    simp only [goose_wp_simp_extra, Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    ihave #HErrD := HErr $$ %Broadcast.Done
    wp_apply HErrD $$ [$HCC] as %cerr2 %Hcerr2
    iapply HΦ
    iframe
    ileft; ipureintro; exact ⟨Hcerr2, rfl⟩
  | nil =>
  (try wp_auto)
  simp only [goose_wp_simp_extra, ↓reduceIte]
  (try wp_auto)
  wp_apply (hRR lkv γ pfx ctx cs o.key o.base.rangeEnd) $$ [$Hlkv $Hrd $Hsr $Hctx $Hcc]
    as %maxRev %err1 Hrd
  (try wp_auto)
  rcases err1 with e1 | _
  · (try wp_auto)
    wp_for_post
    iapply HΦ
    isplitl [Hrd]
    · iexact Hrd
    ileft; ipureintro; exact ⟨by simp, rfl⟩
  (try wp_auto)
  wp_apply (hLR (lkvLeases lkv) γ.lc pfx (leasingX lkv γ) (leasingSeen γ) o.key o.base.rangeEnd)
    $$ [$Hlc $Hpeek $Hwst] as %wsl ⟨%st, %ks, %wcs, Hwsl, -, Hwcs, -, -⟩
  (try wp_auto)
  wp_apply (hRPC lkv γ pfx ctx cs maxRev o.key o.base.rangeEnd lo) $$ [$Hlkv $Hctx $Hlo]
    as %dr %err2 Hres
  (try wp_auto)
  wp_apply hCA $$ [$Hwsl $Hwcs] as -
  (try wp_auto)
  icases Hres with (%Hdr | ⟨%Heq, Hdc⟩)
  · subst Hdr
    rcases err2 with e2 | _
    · (try wp_auto)
      wp_for_post
      iapply HΦ
      isplitl [Hrd]
      · iexact Hrd
      ileft; ipureintro; exact ⟨by simp, rfl⟩
    · (try wp_auto)
      wp_for_post
      simp only [named]
      iframe
  · subst Heq
    ihave Hdc := deleteCommitted_congr lo _ o dr (rangeDeleteOp_key _ _) (rangeDeleteOp_end _ _) $$ Hdc
    icases deleteCommitted_ne_null $$ Hdc with ⟨%Hdrn, Hdc⟩
    (try wp_auto)
    rw [show decide (dr = null) = false by simpa using Hdrn]
    (try wp_auto)
    wp_for_post
    iapply HΦ
    iframe
    iright; iframe; ipureintro; rfl

end proof

end leasing
end EtcdGrove
end Perennial
