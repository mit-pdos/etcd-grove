module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Rollback

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

theorem shared.Rollback.wp_proof : shared.Rollback.spec (GF := GF) (hG := hG) := by
  intro s iface σ txid Hcan
  wp_start as Hsh
  unfold ownShared ownSharedC
  icases Hsh with ⟨%sv, %c, Hsh, %Hok⟩
  iNamed Hsh
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hpds
  wp_auto
  wp_apply wp_map_lookup1 $$ [Hpending] as Hpending
  · iexact Hpending
  try wp_auto
  rcases hpt : pp !! txid with _ | p0
  · have hpd : σ.pending !! txid = none := by
      have := Hdom txid
      simp only [show Std.get? pp txid = pp !! txid from rfl, hpt, Option.isSome_none] at this
      cases h : σ.pending !! txid
      · rfl
      · simp [show Std.get? σ.pending txid = σ.pending !! txid from rfl, h] at this
    rw [decide_eq_true (show (none : Option Loc).getD (zero_val Loc) = null from rfl)]
    try wp_auto
    rw [rollback_none hpd]
    iapply HΦ
    iexists sv, c
    simp only [named]
    isplitl
    · iexists pp; iframe; ipureintro; exact Hiface
    · ipureintro; exact Hok
  obtain ⟨pd, hpd⟩ := Option.isSome_iff_exists.1
    ((Hdom txid).1 (by simp only [show Std.get? pp txid = some p0 from hpt, Option.isSome_some]))
  icases (BigSepM2.bigSepM2_delete (show Std.get? pp txid = some p0 from hpt) hpd).1 $$ Hpds
    with ⟨Hpo, Hpds⟩
  iunfold ownPending at Hpo
  iunfold named at Hpo
  icases Hpo with ⟨%tv, Htp, Hids, Hids_cap, Hatx, Hatx_cap, %Hlrb⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Htp
  rw [decide_eq_false (by simpa using Hnn)]
  try wp_auto
  have Hpl : pd.ids.length = pd.alloctx.length := Hok.2.2.2.2.2 txid pd hpd
  ihave %Hil := ownSlice_len _ _ _ $$ Hids
  ihave %Hal := ownSlice_len _ _ _ $$ Hatx
  simp only [Option.getD_some]
  try wp_auto
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => Hgi
  ihave IH : iprop(∃ (k pg gi : w64) (cm : GMap w64 Unit) (am : GMap w64 w64),
      "i" ∷ i_ptr ↦ k ∗ "pgid" ∷ pgid_ptr ↦ pg ∗ "Hgi" ∷ gi_ptr ↦ gi ∗
      "Hcache" ∷ sv.cache' ↦$ cm ∗ "Hallocs" ∷ sv.allocs' ↦$ am ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (pd.ids.length : Int) ∧
        (∀ x, (cm !! x).isSome ↔ (c !! x).isSome ∧ x ∉ pd.ids.take (sint.nat k)) ∧
        am = (pd.pairs.take (sint.nat k)).foldl rbStep σ.allocs⌝)
      $$ [i pgid Hgi Hcache Hallocs]
  · iexists W64 0, _, _, c, σ.allocs
    iframe
    ipureintro
    refine ⟨by word, by word, fun x => ?_, ?_⟩
    · rw [show sint.nat (W64 0) = 0 from rfl]; simp
    · rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for IH
  wp_if_destruct
  · have Hb : sint.nat k < pd.ids.length := by word
    list_elem pd.ids (sint.nat k) as e
    have Hb2 : sint.nat k < pd.alloctx.length := by omega
    list_elem pd.alloctx (sint.nat k) as tx
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index _ (sint.Z k) pd.ids _ e Hk.1 $$ [Hids] with Hids
    · iframe; ipureintro; exact He_lookup
    try wp_auto
    wp_apply wp_mapDelete $$ [Hcache] as Hcache
    · iexact Hcache
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index _ (sint.Z k) pd.alloctx _ tx Hk.1 $$ [Hatx] with Hatx
    · iframe; ipureintro; exact Htx_lookup
    try wp_auto
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    have Hpair : pd.pairs.take (sint.nat k + 1) = pd.pairs.take (sint.nat k) ++ [(e, tx)] := by
      rw [List.take_add_one]
      congr 1
      simp [Pending.pairs, List.getElem?_zip_eq_some, He_lookup, Htx_lookup]
    have Hcm' : ∀ x, ((GMap.delete e cm) !! x).isSome ↔
        (c !! x).isSome ∧ x ∉ pd.ids.take (sint.nat k + 1) := by
      intro x
      rw [List.take_add_one, He_lookup, GMap.lookup_delete_iff]
      simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
      by_cases hx : e = x
      · subst hx; simp
      · simp only [hx, if_false, Hk.2.2.1 x]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, h2, fun h => hx h.symm⟩
        · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    wp_if_destruct
    · wp_for_post
      iframe
      iexists k + W64 1, e, k, GMap.delete e cm, am
      iframe
      ipureintro
      rw [hk1]
      refine ⟨by word, by word, Hcm', ?_⟩
      rw [Hpair, List.foldl_append, ← Hk.2.2.2]
      simp [rbStep]
    · wp_if_destruct
      · exfalso
        exact Hcan pd hpd tx (List.mem_of_getElem? Htx_lookup) (by assumption) (by simpa using Hif)
      · try wp_auto
        wp_apply wp_mapInsert $$ [Hallocs] as Hallocs
        · iexact Hallocs
        try wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, e, k, GMap.delete e cm, <[e := tx]> am
        iframe
        ipureintro
        rw [hk1]
        refine ⟨by word, by word, Hcm', ?_⟩
        rw [Hpair, List.foldl_append, ← Hk.2.2.2]
        simp only [List.foldl_cons, List.foldl_nil, rbStep]
        rw [if_neg (by assumption)]
  have Hall : sint.nat k = pd.ids.length := by word
  have Hpl2 : pd.pairs.length = pd.ids.length := by simp [Pending.pairs, Hpl]
  obtain ⟨-, -, Hcm, Ham⟩ := Hk
  rw [Hall, List.take_length] at Hcm
  rw [Hall, show pd.pairs.take pd.ids.length = pd.pairs by rw [← Hpl2, List.take_length]] at Ham
  subst Ham
  try wp_auto
  wp_apply wp_mapDelete $$ [Hpending] as Hpending
  · iexact Hpending
  try wp_auto
  generalize hA : List.foldl rbStep σ.allocs pd.pairs = A at *
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_mut_keys (fun (keys : List w64) (i : Nat) (m' : GMap w64 w64) =>
      iprop(∃ (tv0 pv0 : w64), "tid" ∷ tid_ptr ↦ tv0 ∗ "pgid" ∷ pgid_ptr ↦ pv0 ∗
        "Hs" ∷ s ↦ sv ∗ "t" ∷ t_ptr ↦ s ∗ "txid" ∷ txid_ptr ↦ txid ∗
        "%Hm" ∷ ⌜∀ k, m' !! k = if k ∈ keys.take i then (A !! k).filter (fun t => decide (t ≠ txid))
          else A !! k⌝)) $$ Hallocs
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [tid pgid Hs t txid]
  · iexists _, _
    iframe
    ipureintro; intro k; simp
  isplitr
  · imodintro
    iintro %i %key %v %m' ⟨%Hkey, %Hv, %Hagree⟩ HP Hm
    iNamed HP
    have Hmk : m' !! key = some v := by
      rw [Hagree i key (Nat.le_refl _) Hkey]; exact Hv
    have Hnot : key ∉ keys.take i := by
      intro hm
      obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 hm
      simp only [List.length_take, List.getElem_take] at hj e
      have := list_nodup_getElem?_inj keys Hknodup j i key
        (by rw [List.getElem?_eq_getElem (by omega), e]) Hkey
      omega
    have Htake : keys.take (i + 1) = keys.take i ++ [key] := by
      rw [List.take_add_one, Hkey]; rfl
    try wp_auto
    wp_if_destruct
    · try wp_auto
      wp_apply wp_mapDelete $$ [Hm] as Hm
      · iexact Hm
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists (GMap.delete key m')
      iframe
      isplitr
      · ipureintro
        intro k
        rw [Htake, GMap.lookup_delete_iff]
        by_cases hk : key = k
        · subst hk; simp [Hv, Hif, Option.filter]
        · simp only [hk, if_false, Hm k, List.mem_append, List.mem_singleton, Ne.symm hk, _root_.or_false]
      ipureintro
      intro k hk
      rw [GMap.lookup_delete_ne _ (Ne.symm hk)]
    · try wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists m'
      iframe
      isplitr
      · ipureintro
        intro k
        rw [Htake]
        by_cases hk : key = k
        · subst hk; simp [Hv, Hmk, Hif, Hnot, Option.filter]
        · simp only [Hm k, List.mem_append, List.mem_singleton, Ne.symm hk, _root_.or_false]
      ipureintro
      intro k _; rfl
  iintro %m' HP Hm
  iNamed HP
  try wp_auto
  have Hmeq : m' = GMap.filter (fun _ t => decide (t ≠ txid)) A := by
    apply GMap.map_eq; intro k
    rw [Hm k, List.take_length]
    split
    · rfl
    · rename_i hk
      have : A !! k = none := by
        cases h : A !! k
        · rfl
        · exact absurd ((Hkset k).2 (by simp [h])) hk
      show A !! k = (A !! k).filter _
      rw [this]; rfl
  subst Hmeq
  obtain ⟨Hc', Hwf'⟩ := rollback_ok (txid := txid) Hok.2 hpd
  rw [rollback_some hpd, hA] at Hc' Hwf'
  rw [rollback_some hpd, hA]
  iapply HΦ
  iexists sv, cm
  simp only [named]
  isplitl
  · iexists (GMap.delete txid pp)
    iframe
    ipureintro; exact Hiface
  · ipureintro
    refine ⟨fun x => ?_, Hwf'⟩
    rw [Hcm x, Hc' x, Hok.1 x]

end proof

end bbolt
end EtcdGrove
end Perennial
