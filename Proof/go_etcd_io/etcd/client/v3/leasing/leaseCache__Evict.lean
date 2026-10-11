/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__Evict.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Evict
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCacheWrite

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

theorem leaseCache.Evict.wp_proof : leaseCache.Evict.spec (GF := GF) (hG := hG) := by
  intro lc γ pfx X Qr key Q
  wp_start as ⟨#Hlc, #Hpeek, Hstep⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold isLeaseCache
  icases Hlc with ⟨#Hguard, #Hcl⟩
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hwl, HP⟩
  icases leaseCacheInv_open_w $$ HP with ⟨%st, Hown, HX, Hinst, Hready, #Hfacts, %Hwf, Hclose⟩
  unfold lcPeek
  icases Hpeek $$ %st %_ HX with ⟨HX, #HQr⟩
  icases lcOwn_emap_acc $$ Hown with ⟨Hentries, Hemap, Hown⟩
  wp_auto
  wp_apply wp_emap_lookup st key _ Hwf $$ [$Hemap] as Hemap
  cases hk : st.entries !! key with
  | none =>
    ihave Hown := Hown $$ Hentries Hemap
    simp only [Option.map_none, Option.getD_none]
    wp_auto
    imod Hstep $$ %st %(zero_val time.Time) HX with ⟨HX, HQ⟩
    rw [evict_none st key _ hk]
    imod Hclose $$ %st %Hwf [] Hinst Hready Hown HX with HP
    · iexact Hfacts
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $HP]
    iapply HΦ
    iexists st
    simp only [entryFactsAt, LeaseCacheSt.revOf, hk]
    iframe
    iframe #
    ipureintro; rfl
  | some e =>
    have hli := Hwf.li_ne key e hk
    have hnil : st.emap ≠ map.nil := fun h => by rw [Hwf.empty_if_nil h] at hk; simp at hk
    simp only [Option.map_some, Option.getD_some]
    rw [decide_eq_false hli]
    ihave Hown := Hown $$ Hentries Hemap
    icases lcOwn_entry_acc' lc st _ key e hk $$ Hown with ⟨He, Hown⟩
    unfold entryOwn
    icases He with ⟨%hnn, Hr, Hrev, Hwc, Hresp, #Hw⟩
    wp_auto
    ihave Hown := Hown $$ [Hr Hrev Hwc Hresp]
    · iframe; iframe #; ipureintro; exact hnn
    icases lcOwn_freeze lc st key e hk $$ Hown with ⟨Hentries, Hemap, Hrv, Hrmap, Hfr⟩
    ihave Hemap : st.emap ↦$ st.lis $$ [Hemap]
    · unfold emapOwn; simp only [hnil, ↓reduceIte]; iexact Hemap
    wp_auto
    wp_apply wp_mapDelete $$ [$Hemap] as Hemap
    wp_apply time.wp_Now as %t -
    wp_apply wp_mapInsert $$ [$Hrmap] as Hrmap
    imod Hfr $$ %(GMap.insert key t st.revokes) [Hemap] Hrmap Hentries Hrv with Hown
    · unfold emapOwn
      simp only [show (lcFreeze st key e (GMap.insert key t st.revokes)).emap = st.emap from rfl,
        hnil, ↓reduceIte, freeze_lis]
      iexact Hemap
    imod Hstep $$ %st %t HX with ⟨HX, HQ⟩
    rw [evict_eq st key e t hk]
    have hwf' := wf_freeze Hwf hk (GMap.insert key t st.revokes)
    ihave #Hfacts' := lcFacts_same pfx st _ (sameFacts_freeze st key e hk
      (GMap.insert key t st.revokes)) $$ Hfacts
    ihave Hready : monoNatAuthOwn γ.ready 1 (lcFreeze st key e (GMap.insert key t st.revokes)).readyN
      $$ [Hready]
    · rw [show (lcFreeze st key e (GMap.insert key t st.revokes)).readyN = st.readyN from rfl]
      iexact Hready
    ihave Hinst : monoListAuthOwn γ.inst 1
        (lcFreeze st key e (GMap.insert key t st.revokes)).installed $$ [Hinst]
    · rw [show (lcFreeze st key e (GMap.insert key t st.revokes)).installed = st.installed from rfl]
      iexact Hinst
    imod Hclose $$ %_ %hwf' Hfacts' Hinst Hready Hown HX with HP
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $HP]
    iapply HΦ
    iexists st
    simp only [entryFactsAt, LeaseCacheSt.revOf, hk]
    iframe
    iframe #
    isplitr
    · ipureintro; rfl
    unfold lcFacts
    icases Hfacts with ⟨#Hf, -⟩
    iapply (BigSepM.bigSepM_lookup hk) $$ Hf

end proof

end leasing
end EtcdGrove
end Perennial
