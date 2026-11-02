module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__reindex
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__pendingPageIds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem shared.reindex.wp_proof (hPP : shared.pendingPageIds.spec (GF := GF) (hG := hG)) :
    shared.reindex.spec (GF := GF) (hG := hG) := by
  intro I s sv σ c hFPI
  wp_start as ⟨#Hhdl, Hs, Hown⟩
  unfold ownSharedC
  iNamed Hs
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hpds
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  rw [Hiface]
  unfold FLImpl.iface
  wp_auto
  wp_bind (App (Val #(methods I.ity go!"freePageIds" I.iv)) (Val #()))
  iapply (hFPI s σ.free) $$ Hown
  inext
  iintro %r ⟨Hr, Hback⟩
  wp_auto
  wp_bind (App (Val #(methods (go.GoType.PointerType shared.ty) go!"pendingPageIds" #s)) (Val #()))
  iapply (hPP s sv (DFrac.own 1)) $$ [Hs]
  · iframe Hs; iexact Hpkg
  inext
  iintro Hs
  try wp_auto
  wp_apply (wp_map_make2 (K := w64) (V := Unit)) as %mc Hmc
  ihave %Hrl := ownSlice_len _ _ _ $$ Hr
  ihave IH : iprop(∃ (n idv : w64) (cm : GMap w64 Unit),
      "i" ∷ i_ptr ↦ n ∗ "id" ∷ id_ptr ↦ idv ∗ "Hmc" ∷ mc ↦$ cm ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (σ.free.length : Int) ∧
        ∀ x, (cm !! x).isSome ↔ x ∈ σ.free.take (sint.nat n)⌝) $$ [i id Hmc]
  · iexists W64 0, _, ∅
    iframe
    ipureintro
    refine ⟨by word, by word, fun x => ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]
    simp
  wp_for IH
  wp_if_destruct
  · have Hb : sint.nat n < σ.free.length := by word
    list_elem σ.free (sint.nat n) as e
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index r (sint.Z n) σ.free _ e Hn.1 $$ [Hr] with Hr
    · iframe; ipureintro; exact He_lookup
    try wp_auto
    wp_apply wp_mapInsert $$ Hmc as Hmc
    wp_for_post
    iframe
    iexists n + W64 1, e, <[e := ()]> cm
    iframe
    ipureintro
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    refine ⟨by word, by word, fun x => ?_⟩
    rw [hn1, List.take_add_one, He_lookup]
    simp only [Option.toList_some, List.mem_append, List.mem_singleton]
    by_cases hx : x = e
    · subst hx; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hx)]
      simp [hx, Hn.2.2 x]
  -- the free ids are all in the cache; now the pending ones
  have Hall : sint.nat n = σ.free.length := by word
  rw [Hall, List.take_length] at Hn
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (tp : Loc) (cm : GMap w64 Unit),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "Hpds" ∷ ([∗map] _t ↦ p;pd ∈ pp;σ.pending, ownPending p pd) ∗
      "Hmc" ∷ mc ↦$ cm ∗ "txp" ∷ txp_ptr ↦ tp ∗ "t" ∷ t_ptr ↦ s ∗
      "Hs" ∷ s ↦ ({ sv with cache' := mc } : shared) ∗
      "%Hcm" ∷ ⌜∀ x, (cm !! x).isSome ↔
        x ∈ σ.free ∨ x ∈ (keys.take i.toNat).flatMap (fun t => (σ.pendingOf t).ids)⌝)) $$ Hpending
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hpds Hmc txp t Hs]
  · iexists _, cm
    simp only [Int.toNat_zero, List.take_zero, List.flatMap_nil, List.not_mem_nil, or_false]
    iframe
    ipureintro; exact ⟨Int.le_refl _, Hn.2.2⟩
  isplitr
  · imodintro
    iintro %i %key %p ⟨%Hkey, %Hp⟩ HP
    iNamed HP
    obtain ⟨pd, Hpd⟩ := Option.isSome_iff_exists.1
      ((Hdom key).1 (by simp only [show Std.get? pp key = some p from Hp, Option.isSome_some]))
    icases BigSepM2.bigSepM2_lookup_acc Hp Hpd $$ Hpds with ⟨Hpo, Hback2⟩
    iNamed Hpo
    ihave %Hl := ownSlice_len _ _ _ $$ Hids
    wp_auto
    ihave IH2 : iprop(∃ (j pid : w64) (cm' : GMap w64 Unit),
        "i" ∷ i_ptr ↦ j ∗ "pendingID" ∷ pendingID_ptr ↦ pid ∗ "Hmc" ∷ mc ↦$ cm' ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (pd.ids.length : Int) ∧
          ∀ x, (cm' !! x).isSome ↔ (x ∈ σ.free ∨
            x ∈ (keys.take i.toNat).flatMap (fun t => (σ.pendingOf t).ids)) ∨
            x ∈ pd.ids.take (sint.nat j)⌝) $$ [i pendingID Hmc]
    · iexists W64 0, _, cm
      iframe
      ipureintro
      refine ⟨by word, by word, fun x => ?_⟩
      rw [show sint.nat (W64 0) = 0 from rfl]
      simp [Hcm x]
    wp_for IH2
    wp_if_destruct
    · have Hb : sint.nat j < pd.ids.length := by word
      list_elem pd.ids (sint.nat j) as e
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
      wp_apply wp_load_slice_index tv.ids' (sint.Z j) pd.ids _ e Hj.1 $$ [Hids] with Hids
      · iframe; ipureintro; exact He_lookup
      try wp_auto
      wp_apply wp_mapInsert $$ Hmc as Hmc
      wp_for_post
      iframe
      iexists j + W64 1, e, <[e := ()]> cm'
      iframe
      ipureintro
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      refine ⟨by word, by word, fun x => ?_⟩
      rw [hj1, List.take_add_one, He_lookup]
      simp only [Option.toList_some, List.mem_append, List.mem_singleton]
      by_cases hx : x = e
      · subst hx; simp
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hx)]
        simp [hx, Hj.2.2 x]
    have Hjall : sint.nat j = pd.ids.length := by word
    rw [Hjall, List.take_length] at Hj
    ihave Hpds := Hback2 $$ [Hp Hids Hids_cap Hatx Hatx_cap]
    · unfold ownPending; iexists tv; iframe; ipureintro; exact Hlrb
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists p, cm'
    iframe
    ipureintro
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    have Hpo : σ.pendingOf key = pd := by
      simp [FLState.pendingOf, show σ.pending !! key = some pd from Hpd]
    refine ⟨by omega, fun x => ?_⟩
    rw [Htake, List.flatMap_append, Hj.2.2 x]
    simp [Hpo, or_assoc]
  iintro HP Hpending
  iNamed HP
  rw [show (GMap.size pp : Int).toNat = keys.length by omega, List.take_length] at Hcm
  have Hperm := pendingIds_perm_keys σ keys (fun k => (Hkset k).trans (Hdom k)) Hknodup
  wp_auto
  ihave Hown := Hback $$ Hr
  ispecialize HΦ $$ %({ sv with cache' := mc } : shared) %cm
  iapply HΦ
  iframe Hown
  isplitl
  · iexists pp
    simp only [named]
    iframe
    ipureintro; simpa [FLImpl.iface] using Hiface
  · ipureintro
    intro x
    rw [Hcm x]
    simp only [FLState.cached, FLState.allIds, List.mem_append, Hperm.mem_iff]

end proof

end bbolt
end EtcdGrove
end Perennial
