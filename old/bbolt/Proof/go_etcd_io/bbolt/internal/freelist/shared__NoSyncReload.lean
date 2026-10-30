module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__NoSyncReload
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas

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

theorem shared.NoSyncReload.wp_proof : shared.NoSyncReload.spec (GF := GF) (hG := hG) := by
  intro I s σ pg xs dq Q hInit Hinc Hge Hlen Hemp
  wp_start as ⟨#Hhdl, Hsh, Hpg, Hback⟩
  unfold ownSharedW ownSharedC
  icases Hsh with ⟨%sv, %c, Hsh, %Hok⟩
  iNamed Hsh
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hpds
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Unit)) as %mc Hmc
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (tp : Loc) (cm : GMap w64 Unit),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "Hpds" ∷ ([∗map] _t ↦ p;pd ∈ pp;σ.pending, ownPending p pd) ∗
      "Hmc" ∷ mc ↦$ cm ∗ "txp" ∷ txp_ptr ↦ tp ∗ "pcache" ∷ pcache_ptr ↦ mc ∗
      "%Hcm" ∷ ⌜∀ x, (cm !! x).isSome ↔
        x ∈ (keys.take i.toNat).flatMap (fun t => (σ.pendingOf t).ids)⌝)) $$ Hpending
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hpds Hmc txp pcache]
  · iexists _, ∅
    simp only [Int.toNat_zero, List.take_zero, List.flatMap_nil, List.not_mem_nil]
    iframe
    ipureintro; exact ⟨Int.le_refl _, fun x => by simp⟩
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
          ∀ x, (cm' !! x).isSome ↔
            x ∈ (keys.take i.toNat).flatMap (fun t => (σ.pendingOf t).ids) ∨
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
    simp [Hpo]
  iintro HP Hpending
  iNamed HP
  rw [show (GMap.size pp : Int).toNat = keys.length by omega, List.take_length] at Hcm
  have Hperm := pendingIds_perm_keys σ keys (fun k => (Hkset k).trans (Hdom k)) Hknodup
  have Hpc : ∀ x, (cm !! x).isSome ↔ x ∈ σ.pendingIds := fun x => (Hcm x).trans Hperm.mem_iff
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, Hacap⟩
  try wp_auto
  ihave %Hxl := ownSlice_len _ _ _ $$ Hpg
  ihave IH : iprop(∃ (k idv : w64) (al : GoSlice),
      "i" ∷ i_ptr ↦ k ∗ "id" ∷ id_ptr ↦ idv ∗ "a" ∷ a_ptr ↦ al ∗
      "Ha" ∷ al ↦* (xs.take (sint.nat k)).filter (fun x => decide (x ∉ σ.pendingIds)) ∗
      "Hacap" ∷ ownSliceCap w64 al (DFrac.own 1) ∗ "Hpg" ∷ pg ↦*{dq} xs ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (xs.length : Int)⌝) $$ [i id a Hasl Hacap Hpg]
  · iexists W64 0, _, _
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil]
    iframe
    isplitl
    · iExactEq Hasl; rfl
    ipureintro; exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hb : sint.nat k < xs.length := by word
    list_elem xs (sint.nat k) as e
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index pg (sint.Z k) xs _ e Hk.1 $$ [Hpg] with Hpg
    · iframe; ipureintro; exact He_lookup
    try wp_auto
    wp_apply wp_map_lookup2 $$ [Hmc] as Hmc
    · iexact Hmc
    try wp_auto
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    have Htk : xs.take (sint.nat k + 1) = xs.take (sint.nat k) ++ [e] := by
      rw [List.take_add_one, He_lookup]; rfl
    wp_if_destruct
    · try wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, e, al
      rw [hk1, Htk, List.filter_append]
      iframe
      isplitl
      · iExactEq Ha
        simp only [List.filter_cons, List.filter_nil]
        rw [if_neg (by simpa using (Hpc e).1 Hif)]
        simp
      ipureintro; exact ⟨by word, by word⟩
    · try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append $$ [Ha Hacap Hsl] as %al2 ⟨Ha, Hacap, -⟩
      · iframe
      try wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, e, al2
      rw [hk1, Htk, List.filter_append]
      iframe
      isplitl
      · iExactEq Ha
        congr 1
        simp only [List.filter_cons, List.filter_nil]
        rw [if_pos (by simpa using fun h => Hif ((Hpc e).2 h))]
      ipureintro; exact ⟨by word, by word⟩
  have Hall : sint.nat k = xs.length := by word
  rw [Hall, List.take_length]
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  rw [Hiface]
  unfold FLImpl.iface
  try wp_auto
  icases Hback $$ Hpg with ⟨Hown, HQ⟩
  ihave Hsh : ownSharedW s I.iface σ $$ [Hs Hro Hro_cap Hallocs Hcache Hpending Hpds]
  · unfold ownSharedW ownSharedC
    iexists sv, c
    iframe
    ipureintro; exact ⟨Hiface, Hok⟩
  have Hwf' := reload_WF_w Hok.2 Hinc Hge Hlen
  wp_bind (App (Val #(methods I.ity go!"Init" I.iv)) (Val #al))
  iapply (hInit s σ al _ Hwf'.wfw Hemp) $$ [Hsh Hown Ha Hacap]
  · iframe
    isplitl []
    · iexact Hpkg
    iexact Hhdl
  inext
  iintro ⟨Hsh, Hown⟩
  try wp_auto
  iapply HΦ
  iframe
  ihave Hsh := (ownSharedW_wf _ _ _ Hwf') $$ Hsh
  iExactEq Hsh; rfl

end proof

end bbolt
end EtcdGrove
end Perennial
