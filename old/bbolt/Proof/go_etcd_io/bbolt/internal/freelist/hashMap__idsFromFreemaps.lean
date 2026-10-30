module
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__idsFromFreemaps
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

theorem hashMap.idsFromFreemaps.wp_proof :
    hashMap.idsFromFreemaps.spec (GF := GF) (hG := hG) := by
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
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hsets
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (M : GMap w64 Unit) (szv : w64) (isv : Loc),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗ "Hmi" ∷ mi ↦$ M ∗ "ids" ∷ ids_ptr ↦ mi ∗ "size" ∷ size_ptr ↦ szv ∗
      "idSet" ∷ idSet_ptr ↦ isv ∗ "Hsets" ∷ ([∗map] _sz ↦ l;st ∈ FM;sets, l ↦$ st) ∗
      "%HM" ∷ ⌜∀ x, (M !! x).isSome ↔ idsVis sp (fun st => ∃ k ∈ keys.take i.toNat, ∃ set,
        sets !! k = some set ∧ (set !! st).isSome) x⌝)) $$ Hfm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hmi size idSet ids Hsets]
  · iexists ∅, _, _
    iframe
    ipureintro
    refine ⟨Int.le_refl _, fun x => ?_⟩
    simp [idsVis]
  isplitr
  · imodintro
    iintro %i %sz %l ⟨%Hkey, %Hl⟩ HP
    iNamed HP
    have Hnot : sz ∉ keys.take i.toNat := not_mem_take_of_nodup Hknodup Hkey
    obtain ⟨set, Hset⟩ := Option.isSome_iff_exists.1 ((Hdom sz).1
      (by simp only [show Std.get? FM sz = some l from Hl, Option.isSome_some]))
    have Hset' : sets !! sz = some set := Hset
    icases BigSepM2.bigSepM2_lookup_acc Hl Hset $$ Hsets with ⟨Hls, Hback⟩
    wp_auto
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (ikeys : List w64) (b : Int) => iprop(∃ (M : GMap w64 Unit) (stv : w64),
        "%Hb" ∷ ⌜0 ≤ b⌝ ∗ "Hmi" ∷ mi ↦$ M ∗ "ids" ∷ ids_ptr ↦ mi ∗ "size" ∷ size_ptr ↦ sz ∗
        "start" ∷ start_ptr ↦ stv ∗
        "%HM" ∷ ⌜∀ x, (M !! x).isSome ↔ idsVis sp (fun st => (∃ k ∈ keys.take i.toNat, ∃ set,
          sets !! k = some set ∧ (set !! st).isSome) ∨ st ∈ ikeys.take b.toNat) x⌝)) $$ Hls
    iintro %ikeys ⟨%Hikset, %Hiklen, %Hiknodup⟩
    isplitl [Hmi size start ids]
    · iexists M, _
      iframe
      ipureintro
      refine ⟨Int.le_refl _, fun x => ?_⟩
      rw [HM x]
      simp [idsVis]
    isplitr
    · imodintro
      iintro %b %key %u ⟨%Hikey, %Hu⟩ HP
      iNamed HP
      have Hinot : key ∉ ikeys.take b.toNat := not_mem_take_of_nodup Hiknodup Hikey
      have Hv : sp !! key = some sz := (Hmok.2.1 sz key).1 ⟨set, Hset', by simp [Hu]⟩
      have Hvlt : uint.nat sz ≤ free.length := span_le_len Hsok Hf Hv
      have HV : ¬ ((∃ k ∈ keys.take i.toNat, ∃ set,
          sets !! k = some set ∧ (set !! key).isSome) ∨ key ∈ ikeys.take b.toNat) := by
        rintro (⟨k, hk, set', hs', hk'⟩ | h)
        · have := (Hmok.2.1 k key).1 ⟨set', hs', hk'⟩
          rw [Hv] at this; cases this; exact Hnot hk
        · exact Hinot h
      wp_auto
      ihave IH2 : iprop(∃ (j : w64) (M' : GMap w64 Unit),
          "i" ∷ i_ptr ↦ j ∗ "Hmi" ∷ mi ↦$ M' ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ uint.Z sz ∧
            ∀ x, (M' !! x).isSome ↔
              idsVis sp (fun st => (∃ k ∈ keys.take i.toNat, ∃ set,
                sets !! k = some set ∧ (set !! st).isSome) ∨ st ∈ ikeys.take b.toNat) x ∨
              x ∈ runIds key (sint.nat j)⌝) $$ [i Hmi]
      · iexists W64 0, M
        iframe
        ipureintro
        refine ⟨by word, by word, fun x => ?_⟩
        rw [show sint.nat (W64 0) = 0 from rfl, HM x]
        simp [runIds]
      wp_for IH2
      wp_if_destruct
      · have Hjv : sint.nat j < uint.nat sz := by word
        have Hid : key + j = key + W64 (sint.nat j : Int) := by word
        try wp_auto
        wp_apply wp_map_lookup2 $$ [Hmi] as Hmi
        · iexact Hmi
        have Hnone : (M' !! (key + j)).isSome = false := by
          rw [Bool.eq_false_iff]; intro hs
          rw [Hj.2.2, Hid] at hs
          rcases hs with hs | hs
          · exact ids_fresh Hsok Hv (ids_fwd_in Hsok Hv Hjv) HV hs
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
          exact ⟨fun h => h.elim Or.inl (fun h => Or.inr (Or.inl h)),
            fun h => h.elim Or.inl (fun h => h.elim Or.inr (fun h => absurd h hx))⟩
      have Hjall : sint.nat j = uint.nat sz := by word
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists M', key
      iframe
      ipureintro
      have Htake : ikeys.take (b + 1).toNat = ikeys.take b.toNat ++ [key] := by
        rw [show (b + 1).toNat = b.toNat + 1 by omega, List.take_add_one, Hikey]; rfl
      refine ⟨by omega, fun x => ?_⟩
      rw [Hj.2.2 x, Hjall, mem_runIds (by have := (Hsok.1 key sz Hv).2; word), Htake]
      unfold idsVis
      constructor
      · rintro (⟨st, hst, v', hv', hx⟩ | hx)
        · exact ⟨st, hst.imp id (List.mem_append_left _), v', hv', hx⟩
        · exact ⟨key, Or.inr (by simp), sz, Hv, hx⟩
      · rintro ⟨st, hst, v', hv', hx⟩
        rcases hst with hst | hst
        · exact Or.inl ⟨st, Or.inl hst, v', hv', hx⟩
        · rcases List.mem_append.1 hst with hst | hst
          · exact Or.inl ⟨st, Or.inr hst, v', hv', hx⟩
          · rw [List.mem_singleton] at hst; subst hst
            rw [Hv] at hv'; cases hv'; exact Or.inr hx
    iintro HP Hls
    iNamed HP
    rw [show (GMap.size set : Int).toNat = ikeys.length by omega, List.take_length] at HM
    ihave Hsets := Hback $$ Hls
    try wp_auto
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists M, sz, l
    iframe
    ipureintro
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [sz] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    refine ⟨by omega, fun x => ?_⟩
    rw [HM x, Htake]
    unfold idsVis
    constructor
    · rintro ⟨st, hst, v', hv', hx⟩
      refine ⟨st, ?_, v', hv', hx⟩
      rcases hst with ⟨k, hk, set', hs', hk'⟩ | hst
      · exact ⟨k, List.mem_append_left _ hk, set', hs', hk'⟩
      · exact ⟨sz, by simp, set, Hset', (Hikset st).1 hst⟩
    · rintro ⟨st, ⟨k, hk, set', hs', hk'⟩, v', hv', hx⟩
      refine ⟨st, ?_, v', hv', hx⟩
      rcases List.mem_append.1 hk with hk | hk
      · exact Or.inl ⟨k, hk, set', hs', hk'⟩
      · rw [List.mem_singleton] at hk; subst hk
        rw [Hset'] at hs'; cases hs'
        exact Or.inr ((Hikset st).2 hk')
  iintro HP Hfm
  iNamed HP
  rw [show (GMap.size FM : Int).toNat = keys.length by omega, List.take_length] at HM
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
    · rintro ⟨st, v, hv, hx⟩
      obtain ⟨set, hset, hst⟩ := (Hmok.2.1 v st).2 hv
      refine ⟨st, ⟨v, (Hkset v).2 ((Hdom v).2 ?_), set, hset, hst⟩, v, hv, hx⟩
      simp only [show Std.get? sets v = some set from hset, Option.isSome_some]
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
