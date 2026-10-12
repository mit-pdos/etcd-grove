/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__notify.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__notify

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

theorem leaseCache.notify.wp_proof : leaseCache.notify.spec (GF := GF) (hG := hG) := by
  intro lc γ pfx X Qr key
  wp_start as ⟨#Hlc, Hrd, #Hpeek⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold leaseCacheReader
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  icases leaseCacheInv_open $$ HP with ⟨%st, Hown, HX, Hinst, #Hfacts, %Hwf, Hclose⟩
  unfold lcPeek
  icases Hpeek $$ %st %_ HX with ⟨HX, #HQr⟩
  unfold lcOwn
  icases Hown with ⟨Hentries, Hemap, Hrv, Hrmap, Hhdr, #HhdrOk, Hents, #Hfrozen⟩
  by_cases hnil : st.emap = map.nil
  · have hemp := Hwf.empty_if_nil hnil
    simp only [emapOwn, hnil, ↓reduceIte]
    wp_auto
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hclose Hentries Hemap Hrv Hrmap Hhdr Hents HX Hinst]
      as Hrd
    · inext
      iapply Hclose $$ [Hentries Hemap Hrv Hrmap Hhdr Hents] HX Hinst
      iframe
      iframe #
    iapply HΦ
    iframe
    iexists st
    iframe #
    ileft
    ipureintro
    exact ⟨by simp [hemp], rfl, rfl⟩
  · simp only [emapOwn, hnil, ↓reduceIte]
    wp_auto
    wp_apply wp_map_lookup1 $$ [$Hemap] as Hemap
    cases hk : st.entries !! key with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      wp_auto
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hclose Hentries Hemap Hrv Hrmap Hhdr Hents HX Hinst]
        as Hrd
      · inext
        iapply Hclose $$ [Hentries Hemap Hrv Hrmap Hhdr Hents] HX Hinst
        iframe
        iframe #
      iapply HΦ
      iframe
      iexists st
      iframe #
      ileft
      ipureintro
      exact ⟨hk, rfl, rfl⟩
    | some e =>
      have hli : e.li ≠ null := Hwf.li_ne key e hk
      simp only [Option.map_some, Option.getD_some]
      icases (BigSepM.bigSepM_lookup_acc hk).1 $$ Hents with ⟨He, Hents⟩
      unfold entryOwn
      icases He with ⟨%-, Hr, Hrev, Hwc, Hresp, #Hw⟩
      rw [decide_eq_false hli]
      wp_auto
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (Hwf.entries_installed key e hk)
      ihave #Hlb := monoListLbOwn_get $$ Hinst
      ihave #Hidx := monoListIdxOwn_get i (key, e.li) hi $$ Hlb
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hclose Hentries Hemap Hrv Hrmap Hhdr Hents Hr Hrev Hwc Hresp HX Hinst]
        as Hrd
      · inext
        iapply Hclose $$ [Hentries Hemap Hrv Hrmap Hhdr Hents Hr Hrev Hwc Hresp] HX Hinst
        iframe
        iframe #
        iapply Hents
        iframe
        iframe #
        ipureintro; exact hli
      iapply HΦ
      iframe
      iexists st
      iframe #
      iright
      iexists e
      iframe #
      isplitr
      · ipureintro; exact ⟨hk, rfl, rfl, hli⟩
      isplitr
      · unfold leaseKeyInstalled; iexists i; iexact Hidx
      · unfold lcFacts
        icases Hfacts with ⟨#Hf, -⟩
        iapply (BigSepM.bigSepM_lookup hk) $$ Hf

end proof

end leasing
end EtcdGrove
end Perennial
