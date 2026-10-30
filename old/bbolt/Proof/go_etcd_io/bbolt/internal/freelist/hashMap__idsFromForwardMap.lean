module
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__idsFromForwardMap
public import Proof.go_etcd_io.bbolt.internal.freelist.HashIdsLemmas

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

theorem hashMap.idsFromForwardMap.wp_proof :
    hashMap.idsFromForwardMap.spec (GF := GF) (hG := hG) := by
  intro h s free
  wp_start as Hown
  unfold ownHashPart
  iNamed Hown
  unfold hmRaw
  iNamed Hraw
  have Hok' := Hok
  obtain ⟨Hsok, Hf, Hmok, Hcnt, Hlen⟩ := Hok'
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Unit)) as %mi Hmi
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (M : GMap w64 Unit) (sv stv : w64),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗ "Hmi" ∷ mi ↦$ M ∗ "ids" ∷ ids_ptr ↦ mi ∗ "size" ∷ size_ptr ↦ sv ∗ "start" ∷ start_ptr ↦ stv ∗
      "%HM" ∷ ⌜∀ x, (M !! x).isSome ↔ idsVis sp (fun k => k ∈ keys.take i.toNat) x⌝)) $$ Hfw
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hmi size start ids]
  · iexists ∅, _, _
    iframe
    ipureintro
    refine ⟨Int.le_refl _, fun x => ?_⟩
    simp [idsVis]
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hkey, %Hv⟩ HP
    iNamed HP
    have Hvlt : uint.nat v ≤ free.length := span_le_len Hsok Hf Hv
    have Hnot : key ∉ keys.take i.toNat := not_mem_take_of_nodup Hknodup Hkey
    wp_auto
    ihave IH2 : iprop(∃ (j : w64) (M' : GMap w64 Unit),
        "i" ∷ i_ptr ↦ j ∗ "Hmi" ∷ mi ↦$ M' ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ uint.Z v ∧
          ∀ x, (M' !! x).isSome ↔
            idsVis sp (fun k => k ∈ keys.take i.toNat) x ∨ x ∈ runIds key (sint.nat j)⌝) $$ [i Hmi]
    · iexists W64 0, M
      iframe
      ipureintro
      refine ⟨by word, by word, fun x => ?_⟩
      rw [show sint.nat (W64 0) = 0 from rfl, HM x]
      simp [runIds]
    wp_for IH2
    wp_if_destruct
    · have Hjv : sint.nat j < uint.nat v := by word
      have Hid : key + j = key + W64 (sint.nat j : Int) := by word
      try wp_auto
      wp_apply wp_map_lookup2 $$ [Hmi] as Hmi
      · iexact Hmi
      have Hnone : (M' !! (key + j)).isSome = false := by
        rw [Bool.eq_false_iff]; intro hs
        rw [Hj.2.2, Hid] at hs
        rcases hs with hs | hs
        · exact ids_fresh Hsok Hv (ids_fwd_in Hsok Hv Hjv) Hnot hs
        · exact ids_fwd_notin Hsok Hv Hjv hs
      rw [Hnone]
      try wp_auto
      wp_apply wp_mapInsert $$ Hmi as Hmi
      wp_for_post
      iframe
      iexists j + W64 1, <[key + j := ()]> M'
      iframe
      ipureintro
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      refine ⟨by word, by word, fun x => ?_⟩
      rw [hj1, runIds_mem_succ, ← Hid]
      by_cases hx : x = key + j
      · subst hx; simp
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hx), Hj.2.2 x]
        simp [hx]
    have Hjall : sint.nat j = uint.nat v := by word
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists M', v, key
    iframe
    ipureintro
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    refine ⟨by omega, fun x => ?_⟩
    rw [Hj.2.2 x, Hjall, mem_runIds (by have := (Hsok.1 key v Hv).2; word), Htake]
    unfold idsVis
    constructor
    · rintro (⟨st, hst, v', hv', hx⟩ | hx)
      · exact ⟨st, List.mem_append_left _ hst, v', hv', hx⟩
      · exact ⟨key, by simp, v, Hv, hx⟩
    · rintro ⟨st, hst, v', hv', hx⟩
      rcases List.mem_append.1 hst with hst | hst
      · exact Or.inl ⟨st, hst, v', hv', hx⟩
      · rw [List.mem_singleton] at hst; subst hst
        rw [Hv] at hv'; cases hv'; exact Or.inr hx
  iintro HP Hfw
  iNamed HP
  rw [show (GMap.size sp : Int).toNat = keys.length by omega, List.take_length] at HM
  try wp_auto
  iapply HΦ
  iframe
  isplitr
  · ipureintro
    intro x
    rw [HM x, Hf.2 x]
    unfold idsVis
    constructor
    · rintro ⟨st, -, v, hv, hx⟩; exact ⟨st, v, hv, hx⟩
    · rintro ⟨st, v, hv, hx⟩; exact ⟨st, (Hkset st).2 (by simp [hv]), v, hv, hx⟩
  iexists cnt, sp, bwm, sets
  simp only [named]
  isplitl
  · iexists fm, fw, bw, FM
    iframe
  · ipureintro; exact Hok

end proof

end bbolt
end EtcdGrove
end Perennial
