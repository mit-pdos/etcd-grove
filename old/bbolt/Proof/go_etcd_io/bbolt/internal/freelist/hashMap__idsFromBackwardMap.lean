module
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__idsFromBackwardMap
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

theorem hashMap.idsFromBackwardMap.wp_proof :
    hashMap.idsFromBackwardMap.spec (GF := GF) (hG := hG) := by
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
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (M : GMap w64 Unit) (sv ev : w64),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗ "Hmi" ∷ mi ↦$ M ∗ "ids" ∷ ids_ptr ↦ mi ∗ "size" ∷ size_ptr ↦ sv ∗
      "Hend" ∷ end_ptr ↦ ev ∗
      "%HM" ∷ ⌜∀ x, (M !! x).isSome ↔ idsVis sp (fun st => ∃ k ∈ keys.take i.toNat, ∃ v,
        sp !! st = some v ∧ k = st + v - W64 1) x⌝)) $$ Hbw
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hmi size «end» ids]
  · iexists ∅, _, _
    iframe
    ipureintro
    refine ⟨Int.le_refl _, fun x => ?_⟩
    simp [idsVis]
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hkey, %Hv⟩ HP
    iNamed HP
    have Hnot : key ∉ keys.take i.toNat := not_mem_take_of_nodup Hknodup Hkey
    obtain ⟨st, Hst, rfl⟩ := (Hmok.1 key v).1 Hv
    have Hvlt : uint.nat v ≤ free.length := span_le_len Hsok Hf Hst
    have Hsz := Hsok.1 st v Hst
    have HV : ¬ ∃ k ∈ keys.take i.toNat, ∃ v', sp !! st = some v' ∧ k = st + v' - W64 1 := by
      rintro ⟨k, hk, v', hv', rfl⟩
      rw [Hst] at hv'; cases hv'; exact Hnot hk
    wp_auto
    ihave IH2 : iprop(∃ (j : w64) (M' : GMap w64 Unit),
        "i" ∷ i_ptr ↦ j ∗ "Hmi" ∷ mi ↦$ M' ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ uint.Z v ∧
          ∀ x, (M' !! x).isSome ↔
            idsVis sp (fun st => ∃ k ∈ keys.take i.toNat, ∃ v,
              sp !! st = some v ∧ k = st + v - W64 1) x ∨
            x ∈ downIds (st + v - W64 1) (sint.nat j)⌝) $$ [i Hmi]
    · iexists W64 0, M
      iframe
      ipureintro
      refine ⟨by word, by word, fun x => ?_⟩
      rw [show sint.nat (W64 0) = 0 from rfl, HM x]
      simp [downIds]
    wp_for IH2
    wp_if_destruct
    · have Hjv : sint.nat j < uint.nat v := by word
      have Hid : st + v - W64 1 - j = st + v - W64 1 - W64 (sint.nat j : Int) := by word
      try wp_auto
      wp_apply wp_map_lookup2 $$ [Hmi] as Hmi
      · iexact Hmi
      have Hnone : (M' !! (st + v - W64 1 - j)).isSome = false := by
        rw [Bool.eq_false_iff]; intro hs
        rw [Hj.2.2, Hid] at hs
        rcases hs with hs | hs
        · exact ids_fresh Hsok Hst (ids_bwd_in Hsok Hst Hjv) HV hs
        · exact ids_bwd_notin Hsok Hst Hjv hs
      rw [Hnone]
      try wp_auto
      wp_apply wp_mapInsert $$ Hmi as Hmi
      wp_for_post
      iframe
      iexists j + W64 1, <[st + v - W64 1 - j := ()]> M'
      iframe
      ipureintro
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      refine ⟨by word, by word, fun x => ?_⟩
      rw [hj1, downIds_mem_succ, ← Hid]
      by_cases hx : x = st + v - W64 1 - j
      · subst hx; simp
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hx), Hj.2.2 x]
        exact ⟨fun h => h.elim Or.inl (fun h => Or.inr (Or.inl h)),
          fun h => h.elim Or.inl (fun h => h.elim Or.inr (fun h => absurd h hx))⟩
    have Hjall : sint.nat j = uint.nat v := by word
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists M', v, st + v - W64 1
    iframe
    ipureintro
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [st + v - W64 1] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    refine ⟨by omega, fun x => ?_⟩
    rw [Hj.2.2 x, Hjall, downIds_all Hsok Hst, Htake]
    unfold idsVis
    constructor
    · rintro (⟨st', ⟨k, hk, v'', hv'', hke⟩, v', hv', hx⟩ | hx)
      · exact ⟨st', ⟨k, List.mem_append_left _ hk, v'', hv'', hke⟩, v', hv', hx⟩
      · exact ⟨st, ⟨st + v - W64 1, by simp, v, Hst, rfl⟩, v, Hst, hx⟩
    · rintro ⟨st', ⟨k, hk, v'', hv'', hke⟩, v', hv', hx⟩
      rcases List.mem_append.1 hk with hk | hk
      · exact Or.inl ⟨st', ⟨k, hk, v'', hv'', hke⟩, v', hv', hx⟩
      · rw [List.mem_singleton] at hk; subst hk
        rw [hv''] at hv'; cases hv'
        have Hsz' := Hsok.1 st' v'' hv''
        have := span_disj Hsok Hst hv'' (inRun_last Hsz.1 Hsz.2)
          (by rw [hke]; exact inRun_last Hsz'.1 Hsz'.2)
        subst this
        rw [Hst] at hv''; cases hv''; exact Or.inr hx
  iintro HP Hbw
  iNamed HP
  rw [show (GMap.size bwm : Int).toNat = keys.length by omega, List.take_length] at HM
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
      refine ⟨st, ⟨st + v - W64 1, (Hkset _).2 ?_, v, hv, rfl⟩, v, hv, hx⟩
      rw [(Hmok.1 (st + v - W64 1) v).2 ⟨st, hv, rfl⟩]; rfl
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
