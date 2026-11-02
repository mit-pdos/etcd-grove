module
public import Spec.go_etcd_io.bbolt.internal.freelist.array__mergeSpans
public import Spec.sort.Sort
public import Spec.go_etcd_io.bbolt.internal.common.Verify
public import Spec.go_etcd_io.bbolt.internal.common.Pgids__Merge
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

theorem array.mergeSpans.wp_proof (hSort : sort.Sort.spec (GF := GF) (hG := hG))
    (hVerify : Verify.spec (GF := GF) (hG := hG))
    (hMerge : Pgids.Merge.spec (GF := GF) (hG := hG)) :
    array.mergeSpans.spec (GF := GF) (hG := hG) := by
  intro a s free idsl ys Hnd Hge2 Hlen
  wp_start as ⟨Hown, Hys, Hcap⟩
  unfold ownArrayPart
  iNamed Hown
  ihave #Hc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  wp_apply (hSort _ _ ys (Or.inl rfl)) $$ Hys as %ys' ⟨%Hsrt, Hys⟩
  wp_apply (hVerify _ iprop(f_ptr ↦ a ∗ ids_ptr ↦ idsl ∗ idsl ↦* ys' ∗
      structFieldRef array' go!"ids" a ↦ ids ∗ ids ↦* free)) $$ [f ids Hys Hidsf Hids]
  · isplit
    · wp_auto
      wp_apply (wp_map_make1 (K := w64) (V := Unit)) as %mi Hmi
      have Hfnd : free.Nodup := (List.nodup_append.1 Hnd).1
      ihave %Hfl := ownSlice_len _ _ _ $$ Hids
      ihave IH : iprop(∃ (n idv : w64) (m : GMap w64 Unit),
          "i" ∷ i_ptr ↦ n ∗ "id" ∷ id_ptr ↦ idv ∗ "Hmi" ∷ mi ↦$ m ∗
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (free.length : Int) ∧
            ∀ x, (m !! x).isSome ↔ x ∈ free.take (sint.nat n)⌝) $$ [i id Hmi]
      · iexists W64 0, _, ∅
        iframe
        ipureintro
        refine ⟨by word, by word, fun x => ?_⟩
        rw [show sint.nat (W64 0) = 0 from rfl]
        simp
      wp_for IH
      wp_if_destruct
      · have Hb : sint.nat n < free.length := by word
        list_elem free (sint.nat n) as e
        rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
        wp_apply wp_load_slice_index ids (sint.Z n) free _ e Hn.1 $$ [Hids] with Hids
        · iframe; ipureintro; exact He_lookup
        try wp_auto
        wp_apply wp_map_lookup2 $$ [Hmi] as Hmi
        · iexact Hmi
        try wp_auto
        wp_if_destruct
        · exfalso
          exact not_mem_take_of_nodup Hfnd He_lookup ((Hn.2.2 e).1 (by assumption))
        try wp_auto
        wp_apply wp_mapInsert $$ Hmi as Hmi
        wp_for_post
        iframe
        iexists n + W64 1, e, <[e := ()]> m
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
      have Hall : sint.nat n = free.length := by word
      rw [Hall, List.take_length] at Hn
      try wp_auto
      have Hysnd : ys'.Nodup := Hsrt.2.nodup_iff.2 (List.nodup_append.1 Hnd).2.1
      have Hdisj := (List.nodup_append.1 Hnd).2.2
      ihave %Hyl := ownSlice_len _ _ _ $$ Hys
      ihave IH2 : iprop(∃ (k idv pv : w64),
          "i" ∷ i_ptr ↦ k ∗ "id" ∷ id_ptr ↦ idv ∗ "prev" ∷ prev_ptr ↦ pv ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ys'.length : Int) ∧
            (sint.nat k = 0 ∧ pv = W64 0 ∨ 0 < sint.nat k ∧ ys'[sint.nat k - 1]? = some pv)⌝)
          $$ [i id prev]
      · iexists W64 0, _, W64 0
        iframe
        ipureintro
        exact ⟨by word, by word, Or.inl ⟨rfl, rfl⟩⟩
      wp_for IH2
      wp_if_destruct
      · have Hb : sint.nat k < ys'.length := by word
        list_elem ys' (sint.nat k) as e
        have Hemem : e ∈ ys := Hsrt.2.mem_iff.1 (List.mem_of_getElem? He_lookup)
        rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
        wp_apply wp_load_slice_index idsl (sint.Z k) ys' _ e Hk.1 $$ [Hys] with Hys
        · iframe; ipureintro; exact He_lookup
        try wp_auto
        wp_if_destruct
        · exfalso
          rcases Hk.2.2 with ⟨_, rfl⟩ | ⟨hpos, hp⟩
          · have h2 := Hge2 e Hemem
            subst Hif
            word
          · exact nodup_getElem?_ne Hysnd (by omega) hp He_lookup Hif
        try wp_auto
        wp_apply wp_map_lookup2 $$ [Hmi] as Hmi
        · iexact Hmi
        try wp_auto
        wp_if_destruct
        · exfalso
          exact Hdisj e ((Hn.2.2 e).1 (by assumption)) e Hemem rfl
        try wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, e, e
        iframe
        ipureintro
        have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
        refine ⟨by word, by word, Or.inr ⟨by omega, ?_⟩⟩
        rw [hk1, Nat.add_sub_cancel]; exact He_lookup
      try wp_auto
      iframe
      done
    · iframe
  iintro ⟨f, ids, Hys, Hidsf, Hids⟩
  wp_auto
  have Hyl : ys'.length = ys.length := Hsrt.2.length_eq
  wp_apply (hMerge ids idsl free ys' (DFrac.own 1) (DFrac.own 1) (pgidsSorted_of_incr Hincr)
    Hsrt.1 (by omega)) $$ [Hids Hys] as %r %out ⟨%Hout, Hids, Hys, Hcase⟩
  · iframe
  try wp_auto
  have Hperm : out.Perm (free ++ ys) := Hout.2.trans (List.Perm.append_left free Hsrt.2)
  have Hinc : PgidsIncr out := pgidsIncr_of_sorted_nodup Hout.1 (Hperm.nodup_iff.2 Hnd)
  iapply HΦ
  isplitr
  · ipureintro; exact ⟨Hinc, Hperm⟩
  iexists r
  iframe Hidsf
  isplitr
  · ipureintro; exact Hinc
  icases Hcase with (%Hc1 | %Hc2 | Hr)
  · obtain ⟨_, rfl, rfl⟩ := Hc1
    iexact Hys
  · obtain ⟨_, _, rfl, rfl⟩ := Hc2
    iexact Hids
  · iexact Hr

end proof

end bbolt
end EtcdGrove
end Perennial
