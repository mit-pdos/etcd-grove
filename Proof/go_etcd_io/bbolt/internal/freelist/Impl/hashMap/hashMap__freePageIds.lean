/-
`hashMap.freePageIds` (U2 internal; ported from the old proof).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.hashMap.hashMap__FreeCount
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.HashLemmas
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Sorters

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- The spans' starts are free ids: there are no more of them than free ids. -/
theorem fpi_size_le {sp : GMap w64 w64} {free : List w64} (hok : spansOK sp)
    (hf : spansFree sp free) : GMap.size sp ≤ free.length := by
  have hsub : sp.domList ⊆ free := by
    intro k hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 ((GMap.mem_dom_list sp k).1 hk)
    exact span_mem hf hv (hm_inRun_self (by have := (hok.1 k v hv).1; word))
  have := List.Nodup.length_le_of_subset (GMap.nodup_dom_list sp) hsub
  rw [GMap.size_eq_dom_list_length]; omega

theorem fpi_runIds_succ (e : w64) (j : w64) (hj : 0 ≤ sint.Z j) (hj2 : sint.Z j < 2 ^ 63 - 1) :
    runIds e (sint.nat (j + W64 1)) = runIds e (sint.nat j) ++ [e + j] := by
  have h1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
  rw [h1, runIds_succ]
  congr 2
  word


/-- `f.freePageIds()`: a new slice of the free ids, increasing. -/
abbrev hashMap.freePageIds.spec : Prop :=
  ∀ (h s : Loc) (free : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      ownHashPart (GF := GF) h s free }}
    (App (Val (h @!! go.GoType.PointerType hashMap.ty @!! go!"freePageIds")) (Val #()))
  {{ (r : GoSlice), RET #r; r ↦* free ∗ ownHashPart h s free }}

theorem hashMap.freePageIds.wp_proof (hFC : hashMap.FreeCount.spec (GF := GF) (hG := hG)) :
    hashMap.freePageIds.spec (GF := GF) (hG := hG) := by
  intro h s free
  wp_start as Hpart
  wp_auto
  wp_apply (hFC h s free) $$ [Hpart] as Hpart
  · iexact Hpart
  unfold ownHashPart
  iNamed Hpart
  unfold hmRaw
  iNamed Hraw
  obtain ⟨hok, hf, hmaps, hc, hlen⟩ := Hok
  try wp_auto
  wp_if_destruct
  · have Hnil : free = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    subst Hnil
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    iapply HΦ
    isplitl [Hsl]
    · iExactEq Hsl; rfl
    iexists cnt, sp, bwm, sets
    simp only [named]
    iframe
    ipureintro; exact ⟨hok, hf, hmaps, hc, hlen⟩
  · have Hsz := fpi_size_le hok hf
    wp_apply (wp_slice_make3 (V := w64) (W64 0) (W64 (free.length : Int)) ⟨by word, by word⟩)
      as %msl ⟨Hm, Hmcap, -⟩
    try wp_auto
    wp_apply (wp_map_len (K := w64) (V := w64)) $$ Hfw as Hfw
    wp_apply (wp_slice_make3 (V := w64) (W64 0) (W64 (GMap.size sp : Int)) ⟨by word, by word⟩)
      as %ssl ⟨Hs, Hscap, -⟩
    try wp_auto
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (sl : GoSlice) (kv : w64),
        "startPageIds" ∷ startPageIds_ptr ↦ sl ∗ "k" ∷ k_ptr ↦ kv ∗
        "Hs" ∷ sl ↦* keys.take i.toNat ∗ "Hscap" ∷ ownSliceCap w64 sl (DFrac.own 1) ∗
        "%Hi" ∷ ⌜0 ≤ i⌝)) $$ Hfw
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [startPageIds k Hs Hscap]
    · iexists ssl, _
      iframe
      ipureintro; exact Int.le_refl _
    isplitr
    · imodintro
      iintro %i %key %v ⟨%Hkey, %Hv⟩ HP
      iNamed HP
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [Hs Hscap Hsl1] as %sl2 ⟨Hs, Hscap, -⟩
      · iframe
      try wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists sl2, key
      have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
      rw [Htake]
      iframe
      ipureintro; omega
    iintro HP Hfw
    iNamed HP
    rw [show (GMap.size sp : Int).toNat = keys.length by omega, List.take_length]
    try wp_auto
    ihave #Hsrt := Pgids_isSorter (GF := GF) sl
    icases ownSlice_w64_len sl keys _ $$ Hs with ⟨Hs, %Hkb⟩
    wp_apply (sort.wp_Sort (E := w64) (interface.mk go_etcd_io.bbolt.internal.common.Pgids.ty #sl)
      (fun l => sl ↦* l) pgLt slices.StrictWeakOrder_unsigned_lt keys) $$ [Hs]
      as %ys ⟨Hs, %Hperm, %Hsorted⟩
    · iframe Hsrt Hs; ipureintro; omega
    have Hyseq : ys = sortPgids keys := sort_post_eq Hperm Hsorted
    have Hysinc : PgidsIncr ys := by rw [Hyseq]; exact sortPgids_incr Hknodup
    have Hys2 : keys.Perm ys := Hperm
    have Hysk : ∀ k, k ∈ ys ↔ (sp !! k).isSome := fun k => (Hys2.mem_iff.symm).trans (Hkset k)
    try wp_auto
    ihave %Hsl := ownSlice_len _ _ _ $$ Hs
    have Hysl : ys.length = keys.length := Hys2.length_eq.symm
    ihave IH : iprop(∃ (k stv : w64) (ml : GoSlice),
        "io" ∷ i_ptr ↦ k ∗ "start" ∷ start_ptr ↦ stv ∗ "m" ∷ m_ptr ↦ ml ∗
        "Hm" ∷ ml ↦* (ys.take (sint.nat k)).flatMap (spanRun sp) ∗
        "Hmcap" ∷ ownSliceCap w64 ml (DFrac.own 1) ∗
        "Hs" ∷ sl ↦* ys ∗ "Hfw" ∷ fw ↦$ sp ∗ "f" ∷ f_ptr ↦ h ∗
        "Hfwf" ∷ structFieldRef hashMap go!"forwardMap" h ↦ fw ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ys.length : Int)⌝) $$ [i start m Hm Hmcap Hs Hfw f Hfwf]
    · iexists W64 0, _, msl
      iframe
      ipureintro
      constructor <;> word
    wp_for IH
    wp_if_destruct
    · have Hif' : sint.Z k < sint.Z sl.len := by simpa using Hif
      have Hb : sint.nat k < ys.length := by word
      list_elem ys (sint.nat k) as e
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
      wp_apply wp_load_slice_index sl (sint.Z k) ys _ e Hk.1 $$ [Hs] with Hs
      · iframe; ipureintro; exact He_lookup
      try wp_auto
      obtain ⟨v, Hv⟩ := Option.isSome_iff_exists.1 ((Hysk e).1 (List.mem_of_getElem? He_lookup))
      wp_apply wp_map_lookup2 $$ [Hfw] as Hfw
      · iexact Hfw
      rw [Hv]
      try wp_auto
      simp only [Option.isSome_some, Option.getD_some, _root_.decide_true]
      try wp_auto
      have Hv63 : v.toNat ≤ free.length := span_le_len hok hf Hv
      have Hvs : sint.Z v = v.toNat := by word
      ihave IH2 : iprop(∃ (j : w64) (ml' : GoSlice),
          "i" ∷ i_ptr ↦ j ∗ "m" ∷ m_ptr ↦ ml' ∗
          "Hm" ∷ ml' ↦* ((ys.take (sint.nat k)).flatMap (spanRun sp) ++ runIds e (sint.nat j)) ∗
          "Hmcap" ∷ ownSliceCap w64 ml' (DFrac.own 1) ∗ "start" ∷ start_ptr ↦ e ∗
          "size" ∷ size_ptr ↦ v ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z v⌝)
          $$ [i m Hm Hmcap start size]
      · iexists W64 0, ml
        iframe
        isplitl
        · iExactEq Hm
          rw [show sint.nat (W64 0) = 0 from rfl]
          simp [runIds]
        ipureintro; constructor <;> word
      wp_for IH2
      wp_if_destruct
      · have Hjv : sint.Z j < sint.Z v := by simpa using Hif
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl1 ⟨Hsl1, -⟩
        wp_apply wp_slice_append $$ [Hm Hmcap Hsl1] as %ml2 ⟨Hm, Hmcap, -⟩
        · iframe
        try wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, ml2
        iframe
        isplitl
        · iExactEq Hm
          rw [fpi_runIds_succ e j Hj.1 (by word), List.append_assoc]
        ipureintro; constructor <;> word
      · have Hjv : sint.Z j = sint.Z v := by
          have : ¬ sint.Z j < sint.Z v := by simpa using Hif
          omega
        try wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, e, ml'
        iframe
        isplitl
        · iExactEq Hm
          have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
          rw [hk1, List.take_add_one, He_lookup]
          simp only [Option.toList_some, List.flatMap_append, List.flatMap_singleton]
          unfold spanRun spanLen
          rw [Hv, Option.getD_some, show sint.nat j = v.toNat by word]
        ipureintro; constructor <;> word
    · have Hkall : sint.nat k = ys.length := by
        have : ¬ sint.Z k < sint.Z sl.len := by simpa using Hif
        word
      rw [Hkall, List.take_length, spans_flat_eq hok hf Hysinc Hysk]
      try wp_auto
      iapply HΦ
      iframe Hm
      iexists cnt, sp, bwm, sets
      simp only [named]
      iframe
      ipureintro; exact ⟨hok, hf, hmaps, hc, hlen⟩

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
