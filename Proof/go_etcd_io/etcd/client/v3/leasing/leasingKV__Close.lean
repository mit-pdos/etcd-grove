/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__Close.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__Close
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingNewLemmas

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

theorem leasingKV.Close.wp_proof : leasingKV.Close.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx
  wp_start as ⟨#Hlkv, #Hcan, Hopen⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %lctx, %lcs, %cancel0, %osl, %Hpfx, #Hclf, #Hkvf, #Hpfxf, #Hctxf,
    #Hcancelf, #Hoslf, #HKV, #HDo, #HTxn, #HLC, #Hlctx, #Hlcc, #Hcache, #HisWg, #HwgInv, %Hbound⟩
  iunfold isLeasingCancel at Hcan
  icases Hcan with ⟨%cancel, #Hcf, #Hcs⟩
  iunfold concurrency.cancelSpec at Hcs
  wp_auto
  -- `lkv.cancel()`
  wp_apply Hcs $$ []
  · imodintro; itrivial
  -- register as the wait group's waiter, depositing the "open" token
  iapply fupd_wp
  iinv HwgInv with >Hi Hclose
  iunfold leasingWgInv at Hi
  icases Hi with ⟨%ctr, %wn, %k, %d, Hwgo, Hwt, Hrun, Hk, Hoauth, Hcap, Hcauth,
    %Hctr, %Hkd, Hwn⟩
  icases Hwn with (%Hw0 | ⟨-, Hop1⟩)
  rotate_left
  · iexfalso
    iapply leasingOpen_excl γ 1 $$ [$Hopen $Hop1]
  subst Hw0
  imod fupd_mask_subseteq leasingWg_mask with Hmask
  imod sync.alloc_wait_token (lkvWg lkv) γ.wg leasingWgWGN 0 (by decide) $$ HisWg Hwt
    with ⟨Hwt, Htok⟩
  imod Hmask with -
  imod Hclose $$ [Hwgo Hwt Hrun Hk Hoauth Hcap Hcauth Hopen] with -
  · inext
    unfold leasingWgInv
    iexists ctr, 1, k, d
    iframe
    isplitr
    · ipureintro; exact Hctr
    isplitr
    · ipureintro; exact Hkd
    iright
    iframe
    ipureintro; rfl
  imodintro
  -- `lkv.wg.Wait()`
  wp_apply +noauto wp_leasingWg_Wait lkv γ $$ [$Hsync $HisWg $HwgInv $Htok] as -
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end leasing
end EtcdGrove
end Perennial
