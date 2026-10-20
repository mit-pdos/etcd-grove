/-
Proof of `Spec/go_etcd_io/raft/v3/tracker/ReplicationSet__String.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.ReplicationSet__String
public import Spec.slices.Sort
public import Spec.strconv.FormatUint
public import Spec.fmt.Sprintf
public import Spec.strings.Join

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The ids (the map's keys, then the witness unless it is the excluded voter) sorted, each
formatted, joined and printed; at most `2^62` of them (`RSM.strLen`), as `slices.Sort` needs. -/
theorem tracker.ReplicationSet.String.wp_proof
    (wp_slices_Sort : slices.«Sort».spec (GF := GF) (hG := hG))
    (wp_strconv_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG))
    (wp_strings_Join : strings.Join.spec (GF := GF) (hG := hG))
    (wp_fmt_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG)) :
    tracker.ReplicationSet.String.spec (GF := GF) (hG := hG) := by
  intro l rv m
  wp_start as ⟨#Hl, #Hm, %Hsz⟩
  replace Hsz : (GMap.size m.nwv : Int) + (if m.excl = m.wit then 0 else 1) ≤ 2 ^ 62 := by
    unfold RSM.strLen at Hsz; split at Hsz <;> simp_all <;> omega
  icases ownRS_fields l rv m $$ [Hl Hm] with ⟨#Hw, #He, #Hn⟩
  · iframe Hl Hm
  iunfold ownRS at Hm
  icases Hm with ⟨-, Hm⟩
  iunfold ownScope at Hm
  wp_auto
  wp_apply wp_slice_literal (V := w64) []
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨Hsl0, Hcap0⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  icases Hm with (%Hnil | ⟨%idsm, %Hids, #Hmap⟩)
  obtain ⟨Hn0, Hs0⟩ := Hnil
  rw [Hn0]
  wp_auto
  ihave Hc : iprop(∃ (sl : GoSlice) (xs : List w64), ids_ptr ↦ sl ∗ sl ↦* xs ∗
      ownSliceCap w64 sl (DFrac.own 1) ∗ ⌜xs.length = GMap.size m.nwv⌝) $$ [ids Hsl0 Hcap0]
  · iexists _, []
    iframe ids Hsl0 Hcap0
    ipureintro
    rw [Hs0, GMap.size_empty]; rfl
  rotate_left
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (sl' : GoSlice) (x : w64),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "results" ∷ ids_ptr ↦ sl' ∗
      "Hsl" ∷ sl' ↦* keys.take i.toNat ∗
      "Hsl_cap" ∷ ownSliceCap w64 sl' (DFrac.own 1) ∗
      "v" ∷ id_ptr ↦ x)) $$ Hmap
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [ids id Hsl0 Hcap0]
  · iexists _, zero_val w64
    simp only [Int.toNat_zero, List.take_zero, named]
    iframe ids id Hsl0 Hcap0
    ipureintro; omega
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_slice_literal (V := w64) [key]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_auto
    wp_apply wp_slice_append (V := w64) _ _ _ _ _ $$ [$Hsl $Hsl_cap $Hsl2]
      as %sl3 ⟨Hsl, Hsl_cap, -⟩
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    iexists sl3, key
    rw [Htake]
    simp only [named]
    iframe results Hsl Hsl_cap v
    ipureintro; omega
  iintro HP -
  iNamed HP
  rw [show (GMap.size idsm : Int).toNat = keys.length by omega, List.take_length]
  wp_auto
  ihave Hc : iprop(∃ (sl : GoSlice) (xs : List w64), ids_ptr ↦ sl ∗ sl ↦* xs ∗
      ownSliceCap w64 sl (DFrac.own 1) ∗ ⌜xs.length = GMap.size m.nwv⌝) $$ [results Hsl Hsl_cap]
  · iexists _, keys
    iframe results Hsl Hsl_cap
    ipureintro
    have Hp : keys.Perm (GMap.elements m.nwv) := by
      rw [← Hids]
      refine (List.perm_ext_iff_of_nodup Hknodup (GMap.NoDup_elements _)).2 ?_
      intro k
      rw [GMap.elem_of_elements, GMap.elem_of_dom, Hkset, Option.isSome_iff_exists]
    rw [Hp.length_eq, GMap.length_elements]
  all_goals
    icases Hc with ⟨%sl, %xs, ids, Hsl, Hcap, %Hxs⟩
    wp_if_destruct
    ihave Hc2 : iprop(∃ (xs : List w64), sl ↦* xs ∗ ⌜xs.length ≤ 2 ^ 62⌝) $$ [Hsl]
    · iexists xs
      iframe Hsl
      ipureintro
      simp only [Hif, ↓reduceIte] at Hsz
      word
    rotate_left
    wp_apply wp_slice_literal (V := w64) [m.wit]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_auto
    wp_apply wp_slice_append (V := w64) _ _ _ _ _ $$ [$Hsl $Hcap $Hsl2]
      as %sl ⟨Hsl, Hcap, -⟩
    ihave Hc2 : iprop(∃ (xs : List w64), sl ↦* xs ∗ ⌜xs.length ≤ 2 ^ 62⌝) $$ [Hsl]
    · iexists _
      iframe Hsl
      ipureintro
      simp only [Hif, ↓reduceIte] at Hsz
      simp only [List.length_append, List.length_singleton]
      word
    all_goals
      icases Hc2 with ⟨%ys, Hsl, %Hys⟩
      wp_apply wp_slices_Sort $$ [$Hsl] as %zs ⟨Hsl, %Hzs, -⟩
      · ipureintro; exact Hys
      wp_apply wp_slice_make3 (V := GoString) (W64 0) (W64 2) ⟨by word, by word⟩
        as %rs ⟨Hrs, Hrscap, -⟩
      ihave IH : iprop(∃ (k x : w64) (rs' : GoSlice) (strs : List GoString),
          "i" ∷ i_ptr ↦ k ∗ "id" ∷ id_ptr ↦ x ∗ "replSet" ∷ replSet_ptr ↦ rs' ∗
          "Hrs" ∷ rs' ↦* strs ∗
          "Hrscap" ∷ ownSliceCap GoString rs' (DFrac.own 1) ∗
          "Hsl" ∷ sl ↦* zs ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (zs.length : Int)⌝) $$ [i id replSet Hrs Hrscap Hsl]
      · iexists W64 0, _, _, _
        iframe i id replSet Hrs Hrscap Hsl
        ipureintro; constructor <;> word
      wp_for IH
      wp_if_destruct
      · ihave %Hnl := ownSlice_len $$ Hsl
        have Hlt : (sint.Z k).toNat < zs.length := by word
        list_elem zs (sint.Z k).toNat as e
        rw [ite_eq_left (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len by word)]
        wp_apply wp_load_slice_index sl (sint.Z k) zs (DFrac.own 1) e Hk.1 $$ [Hsl] as Hsl
        · iframe; ipureintro; exact He_lookup
        wp_apply wp_strconv_FormatUint $$ [] as %str -
        · ipureintro; decide
        wp_apply wp_slice_literal
        try (isplitr; (ipureintro; rfl))
        iintro %sl2' ⟨Hsl2, -⟩
        wp_auto
        wp_apply wp_slice_append $$ [$Hrs $Hrscap $Hsl2] as %rs3 ⟨Hrs, Hrscap, -⟩
        wp_for_post
        iframe
        iexists _, _, _, _
        iframe
        ipureintro; constructor <;> word
      wp_apply wp_strings_Join $$ [$Hrs] as %joined Hrs
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %sla ⟨Hargs, -⟩
      wp_auto
      wp_apply wp_fmt_Sprintf $$ [$Hargs] as %res -
      · ipureintro
        exact _root_.Perennial.fmt.ArgsWf.cons_string _ _ _root_.Perennial.fmt.ArgsWf.nil
      iapply HΦ
      itrivial

end proof

end EtcdGrove
end Perennial
