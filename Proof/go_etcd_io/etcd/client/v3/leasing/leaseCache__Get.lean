/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__Get.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Get
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__notify
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseKey__get
public import Spec.go_etcd_io.etcd.client.v3.leasing.isBadOp
public import Spec.go_etcd_io.etcd.client.v3.Op__KeyBytes

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

theorem leaseCache.Get.wp_proof
    (hBad : isBadOp.spec (GF := GF) (hG := hG))
    (hKey : Op.KeyBytes.spec (GF := GF) (hG := hG))
    (hnotify : leaseCache.notify.spec (GF := GF) (hG := hG))
    (hget : leaseKey.get.spec (GF := GF) (hG := hG)) :
    leaseCache.Get.spec (GF := GF) (hG := hG) := by
  intro lc γ pfx X Qr ctx cs opv o
  wp_start as ⟨#Hlc, Hrd, #Hpeek, #Hctx, #Hat⟩
  wp_auto
  wp_apply hBad $$ [$Hat]
  cases hbad : isBadOpM o
  · wp_auto
    wp_apply hKey $$ [$op $Hat] as %ksl ⟨op, #Hk⟩
    wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
    wp_apply (hnotify lc γ pfx X Qr o.key) $$ [$Hrd $Hlc $Hpeek] as %li %wc ⟨Hrd, %st1, -, Hres⟩
    icases Hres with (⟨%Hnone, %Hli, %Hwc⟩ | ⟨%e1, %He1, #Hw, #Hinst1, -⟩)
    · subst Hli
      wp_auto
      iapply HΦ
      iframe
      iright; ileft
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨-, -, Hwc1, Hlinn⟩ := He1
      rw [decide_eq_false Hlinn]
      wp_auto
      unfold context.isContext context.isContextDef
      iNamed Hctx
      wp_apply HDone as %ch1 %γ1 #Hdone
      unfold waitcOk
      icases Hw with ⟨%γw, #Hbw⟩
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, wc, γw
        isplit
        · ipureintro; rfl
        isplit
        · iapply ownBroadcastChan_is_chan $$ Hbw
        iapply broadcast_chan_receive _ _ _ _ _ $$ Hbw
        iintro ⟨-, -⟩
        wp_auto
        ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
        · iPkgInit
        unfold leaseCacheReader
        wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
        icases leaseCacheInv_open $$ HP with ⟨%st, Hown, HX, Hinst, #Hfacts, %Hwf, Hclose⟩
        unfold lcPeek
        icases Hpeek $$ %st %_ HX with ⟨HX, #HQr⟩
        unfold leaseKeyInstalled
        icases Hinst1 with ⟨%i, #Hidx⟩
        ihave %Hi := mono_list_auth_idx_lookup $$ Hinst Hidx
        unfold lcOwn
        icases Hown with ⟨Hentries, Hemap, Hrv, Hrmap, Hhdr, #HhdrOk, Hents, #Hfrozen⟩
        unfold lcFacts
        icases Hfacts with ⟨#Hf, #Hff⟩
        rcases Hwf.installed o.key li (List.mem_of_getElem? Hi) with ⟨e2, hk2, hli2⟩ | ⟨e2, hfr, hli2⟩
        · -- still the key's entry
          subst hli2
          icases (BigSepM.bigSepM_lookup_acc hk2).1 $$ Hents with ⟨He, Hents⟩
          unfold entryOwn
          icases He with ⟨%Hnn, Hr, Hrev, Hwc, Hresp, #Hw2⟩
          ihave Hlk := (leaseKey_struct e2.li e2.lk _ Hnn).1 $$ [Hr Hrev Hwc]
          · simp only [LeaseEntry.lk]; iframe
          wp_auto
          wp_apply hget $$ [$lk $Hresp $Hat] as %ret ⟨lk, Hresp, Hret⟩
          icases (leaseKey_struct e2.li e2.lk _ Hnn).2 $$ Hlk with ⟨Hr, Hrev, Hwc⟩
          simp only [LeaseEntry.lk]
          wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hclose Hentries Hemap Hrv Hrmap Hhdr Hents Hr Hrev Hwc Hresp HX Hinst]
            as Hrd
          · inext
            iapply Hclose $$ [Hentries Hemap Hrv Hrmap Hhdr Hents Hr Hrev Hwc Hresp] HX Hinst
            iframe
            iframe #
            iapply Hents
            iframe
            iframe #
            ipureintro; exact Hnn
          iapply HΦ
          iframe
          iright; iright
          isplitr
          · ipureintro; exact ⟨trivial, rfl⟩
          iexists st, e2
          iframe #
          isplitr
          · ipureintro; left; exact hk2
          isplitr [Hret]
          · iapply (BigSepM.bigSepM_lookup hk2) $$ Hf
          iexact Hret
        · -- evicted since: frozen
          subst hli2
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hfr
          ihave He := (BigSepL.bigSepL_lookup (Φ := fun _ f => entryOwn f.2 DFrac.discard) hj) $$ Hfrozen
          ihave #Hfe := (BigSepL.bigSepL_lookup (Φ := fun _ f => entryFacts pfx f.1 f.2) hj) $$ Hff
          unfold entryOwn
          icases He with ⟨%Hnn, #Hr, #Hrev, #Hwc, #Hresp, #Hw2⟩
          ihave #Hlk := (leaseKey_struct e2.li e2.lk DFrac.discard Hnn).1 $$ [Hr Hrev Hwc]
          · simp only [LeaseEntry.lk]; iframe #
          wp_auto
          wp_apply hget $$ [$lk $Hresp $Hat] as %ret ⟨lk, -, Hret⟩
          wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hclose Hentries Hemap Hrv Hrmap Hhdr Hents HX Hinst]
            as Hrd
          · inext
            iapply Hclose $$ [Hentries Hemap Hrv Hrmap Hhdr Hents] HX Hinst
            iframe
            iframe #
          iapply HΦ
          iframe
          iright; iright
          isplitr
          · ipureintro; exact ⟨trivial, rfl⟩
          iexists st, e2
          iframe #
          isplitr
          · ipureintro; right; exact hfr
          iexact Hret
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
        isplit
        · ipureintro; rfl
        isplit
        · iapply context.isContextDone_is_chan $$ Hdone
        iapply context.isContextDone_receive _ _ _ _ $$ Hdone
        iintro -
        wp_auto
        iapply HΦ
        iframe
        iright; ileft
        ipureintro; exact ⟨trivial, rfl, rfl⟩
      iapply BigAndL.bigAndL_nil.2
      itrivial
  · wp_auto
    iapply HΦ
    iframe
    ileft
    ipureintro
    exact ⟨rfl, rfl, rfl⟩

end proof

end leasing
end EtcdGrove
end Perennial
