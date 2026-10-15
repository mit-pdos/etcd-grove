/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__readySession.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__readySession
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Done
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKVLemmas

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
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.readySession.wp_proof
    (hDone : EtcdGrove.concurrency.Session.Done.spec (GF := GF) (hG := hG)) :
    leasingKV.readySession.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx
  wp_start as ⟨#Hlkv, Hrd⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold lkvReader leaseCacheReader
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  icases leaseCacheInv_open $$ HP with ⟨%st, Hown, HX, Hinst, #Hfacts, %Hwf, Hclose⟩
  icases leasingX_session lkv γ st _ $$ HX with ⟨%s, Hs, #Hso, #Hrdy, HXback⟩
  wp_auto
  by_cases hs : s = null
  · subst hs
    wp_auto
    ihave HX := HXback $$ Hs
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hclose Hown HX Hinst] as Hrd
    · inext
      iapply Hclose $$ Hown HX Hinst
    iapply HΦ
    iframe
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  · rw [decide_eq_false hs]
    unfold sessionOk
    simp only [hs, ↓reduceIte] at *
    icases Hso with ⟨%γs, %cl, %id, #Hsess, -⟩
    wp_auto
    ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency $$ []
    · iPkgInit
    wp_apply hDone s γs cl id $$ [$Hcpkg $Hsess] as %dch #Hdch
    ihave HX := HXback $$ Hs
    ihave HR : iprop(sync.ownRWMutexRLocked (lkvLeases lkv).[leaseCache, go!"mu"]
          (leaseCacheInv (lkvLeases lkv) γ.lc pfx (leasingX lkv γ)) ∗
        leaseCacheInv (lkvLeases lkv) γ.lc pfx (leasingX lkv γ) sync.rfrac) $$ [Hrl Hclose Hown HX Hinst]
    · iframe Hrl
      iapply Hclose $$ Hown HX Hinst
    ipersist defer
    wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)]
        iprop((sync.ownRWMutexRLocked (lkvLeases lkv).[leaseCache, go!"mu"]
          (leaseCacheInv (lkvLeases lkv) γ.lc pfx (leasingX lkv γ)) ∗
          leaseCacheInv (lkvLeases lkv) γ.lc pfx (leasingX lkv γ) sync.rfrac) ∗
          (∀ b : Bool, (sync.ownRWMutex (lkvLeases lkv).[leaseCache, go!"mu"]
            (leaseCacheInv (lkvLeases lkv) γ.lc pfx (leasingX lkv γ)) ∗
            (if b = true then sessionReady γ else iprop(True))) -∗ Φ #b))
        $$ [] [HR HΦ] []
    · iapply BigSepL2.bigSepL2_singleton.2
      iintro ⟨⟨Hrl, HP⟩, HΦ⟩
      simp only [chan.nonblockingAltClausePre]
      iunfold concurrency.sessionDoneChan at Hdch
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γs.done
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownBroadcastChan_is_chan $$ Hdch
      iapply ownBroadcastChan_nonblocking_receive _ _ _ _ _ _ $$ Hdch
      isplit
      · iintro -
        wp_auto
        wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl $HP] as Hrd
        iapply HΦ
        iframe
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
      · iintro -
        iframe
    · iframe
    · iintro ⟨⟨Hrl, HP⟩, HΦ⟩ -
      wp_auto
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl $HP] as Hrd
      iapply HΦ
      iframe
      simp only [↓reduceIte]
      iexact Hrdy

end proof

end leasing
end EtcdGrove
end Perennial
