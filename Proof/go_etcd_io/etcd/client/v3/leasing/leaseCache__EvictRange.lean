/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__EvictRange.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__EvictRange
public import Spec.go_etcd_io.etcd.client.v3.leasing.inRange
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
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leaseCache.EvictRange.wp_proof (hinRange : inRange.spec (GF := GF) (hG := hG)) :
    leaseCache.EvictRange.spec (GF := GF) (hG := hG) := by
  intro lc γ pfx X Qr key e Q
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
  by_cases hnil : st.emap = map.nil
  · have hemp := Hwf.empty_if_nil hnil
    icases lcOwn_emap_acc $$ Hown with ⟨Hentries, Hemap, Hown⟩
    wp_auto
    ihave Hown := Hown $$ Hentries Hemap
    rw [hnil]
    wp_func_lits
    wp_auto
    imod Hstep $$ %st %(zero_val time.Time) HX with ⟨HX, HQ⟩
    rw [evictRange_none st key e _ (by simp [hemp])]
    imod Hclose $$ %st %Hwf [] Hinst Hready Hown HX with HP
    · iexact Hfacts
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $HP]
    iapply HΦ
    iexists st
    iframe
    iframe #
  · icases lcOwn_evictKey_acc lc st key hnil $$ Hown with ⟨Hentries, Hemap, Hrv, Hrmap, Hcl⟩
    wp_auto
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range_gen (fun (keys : List GoString) (i : Nat) (m' : GMap GoString Loc) =>
        iprop(∃ (found : Bool) (t : time.Time) (kv : GoString),
        "Hrmap" ∷ st.rmap ↦$ (if found then GMap.insert key t st.revokes else st.revokes) ∗
        "Hentries" ∷ structFieldRef leaseCache go!"entries" lc ↦ st.emap ∗
        "Hrv" ∷ structFieldRef leaseCache go!"revokes" lc ↦ st.rmap ∗
        "k" ∷ k_ptr ↦ kv ∗ "Hkey" ∷ key_ptr ↦ key ∗ "Hend" ∷ end_ptr ↦ e ∗ "Hlc" ∷ lc_ptr ↦ lc ∗
        "%Hm" ∷ ⌜m' = if found then GMap.delete key st.lis else st.lis⌝ ∗
        "%Hf" ∷ ⌜found = true → ∃ k ent, st.entries !! k = some ent ∧ leaseInRange k key e = true⌝ ∗
        "%Hnf" ∷ ⌜found = false → ∀ j k, j < i → keys[j]? = some k → leaseInRange k key e = false⌝))
      _ _ _ st.emap st.lis (DFrac.own 1) $$ Hemap
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [Hrmap Hentries Hrv k key «end» lc]
    · iexists false, zero_val time.Time, _
      simp only [named]
      iframe
      ipureintro
      refine ⟨rfl, fun h => by simp at h, fun _ j k hj _ => by omega⟩
    isplitr
    · imodintro
      iintro %i %k %v %m' ⟨%Hki, %Hmv⟩ HP Hm
      iNamed HP
      wp_auto
      wp_apply hinRange
      have hlis : st.lis !! k = some v := by
        cases found <;> simp only [Bool.false_eq_true, ↓reduceIte] at Hm <;> subst Hm
        · exact Hmv
        · rw [ldel] at Hmv; exact Hmv.2
      have hent : ∃ ent, st.entries !! k = some ent := by
        simp only [LeaseCacheSt.lis, GMap.lookup_fmap, Option.map_eq_some_iff] at hlis
        obtain ⟨ent, h, -⟩ := hlis; exact ⟨ent, h⟩
      cases hr : leaseInRange k key e
      · wp_auto
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists m'
        iframe Hm
        iexists found, t, k
        simp only [named]
        iframe
        ipureintro
        refine ⟨Hm, Hf, fun hfalse j k' hj hkj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact Hnf hfalse j k' hj hkj
        · rw [Hki] at hkj; cases hkj; exact hr
      · wp_auto
        wp_apply wp_mapDelete $$ [$Hm] as Hm
        wp_apply time.wp_Now as %t' -
        wp_apply wp_mapInsert $$ [$Hrmap] as Hrmap
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _
        iframe Hm
        iexists true, t', k
        simp only [named, ↓reduceIte]
        have hrv : GMap.insert key t' (if found = true then GMap.insert key t st.revokes else st.revokes)
            = GMap.insert key t' st.revokes := by
          cases found <;> simp [GMap.insert_insert]
        rw [hrv]
        iframe
        ipureintro
        refine ⟨?_, fun _ => ⟨k, hent.choose, hent.choose_spec, hr⟩, fun h => by simp at h⟩
        cases found <;> simp only [Bool.false_eq_true, ↓reduceIte] at Hm <;> subst Hm
        · rfl
        · exact GMap.delete_idemp _ _
    isplitr
    · imodintro
      iintro %i %k %m' ⟨%Hki, %Hnone⟩ HP
      iNamed HP
      cases found
      · exfalso
        simp only [Bool.false_eq_true, ↓reduceIte] at Hm
        subst Hm
        have := (Hkset k).1 (List.mem_of_getElem? Hki)
        rw [Hnone] at this; simp at this
      · iexists true, t, kv
        simp only [named]
        iframe
        ipureintro
        exact ⟨Hm, fun _ => Hf rfl, fun h => by simp at h⟩
    iintro %m' HP Hm
    iNamed HP
    wp_auto
    cases found
    · simp only [Bool.false_eq_true, ↓reduceIte] at Hm
      subst Hm
      have hno : ¬ ∃ k ent, st.entries !! k = some ent ∧ leaseInRange k key e = true := by
        rintro ⟨k, ent, hk, hr⟩
        have hmem : k ∈ keys := (Hkset k).2 (by simp [LeaseCacheSt.lis, hk])
        obtain ⟨j, hj⟩ := List.getElem?_of_mem hmem
        have hjl : j < keys.length := (List.getElem?_eq_some_iff.1 hj).1
        rw [Hnf rfl j k hjl hj] at hr; exact Bool.false_ne_true hr
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hcl with ⟨Hcl, -⟩
      ihave Hown := Hcl $$ Hentries Hm Hrv Hrmap
      imod Hstep $$ %st %t HX with ⟨HX, HQ⟩
      rw [evictRange_none st key e t hno]
      imod Hclose $$ %st %Hwf [] Hinst Hready Hown HX with HP
      · iexact Hfacts
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $HP]
      iapply HΦ
      iexists st
      iframe
      iframe #
    · simp only [↓reduceIte] at Hm
      subst Hm
      simp only [↓reduceIte]
      icases Hcl with ⟨-, Hcl⟩
      imod Hcl $$ %t Hentries Hm Hrv Hrmap with Hown
      imod Hstep $$ %st %t HX with ⟨HX, HQ⟩
      rw [evictRange_found st key e t (Hf rfl)]
      have hwf' := wf_evictKeySt Hwf key t
      ihave #Hfacts' := lcFacts_same pfx st _ (sameFacts_evictKeySt st key t) $$ Hfacts
      ihave Hready : monoNatAuthOwn γ.ready 1 (evictKeySt st key t).readyN $$ [Hready]
      · rw [show (evictKeySt st key t).readyN = st.readyN by
          unfold evictKeySt; cases st.entries !! key <;> rfl]
        iexact Hready
      ihave Hinst : monoListAuthOwn γ.inst 1 (evictKeySt st key t).installed $$ [Hinst]
      · rw [show (evictKeySt st key t).installed = st.installed by
          unfold evictKeySt; cases st.entries !! key <;> rfl]
        iexact Hinst
      imod Hclose $$ %_ %hwf' Hfacts' Hinst Hready Hown HX with HP
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $HP]
      iapply HΦ
      iexists st
      iframe
      iframe #
  
end proof

end leasing
end EtcdGrove
end Perennial
