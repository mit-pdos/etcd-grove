/-
`array.mergeSpans(ids)` (U2 internal): the ids sorted (`sort.Sort`), checked (`common.Verify`:
no duplicate among the free ids, none among `ids`, none in both), merged into the free ids
(`Pgids.Merge`).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Own
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Callees
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Sorters
public import Spec.go_etcd_io.bbolt.internal.common.Pgids__Merge

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem arrayImpl_mergeSpans
    (hVerify : _root_.Perennial.EtcdGrove.bbolt.internal.common.Verify.spec (GF := GF) (hG := hG))
    (hMerge : _root_.Perennial.EtcdGrove.bbolt.internal.common.Pgids.Merge.spec (GF := GF) (hG := hG))
    (a : Loc) : (arrayImpl (GF := GF) a).MergeSpansSpec := by
  intro free idsl ys Hinc Hnd _ Hge2 Hlen
  dsimp only [arrayImpl]
  wp_start as ⟨⟨%ids, Hidsf, Hids, Hidscap⟩, Hys, Hcap⟩
  ihave #Hc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave #Hsp : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  icases ownSlice_w64_len _ _ _ $$ Hys with ⟨Hys, %Hyb⟩
  wp_auto
  wp_apply (sort.wp_Sort (interface.mk go_etcd_io.bbolt.internal.common.Pgids.ty #idsl)
    (fun l => idsl ↦* l) pgLt slices.StrictWeakOrder_unsigned_lt ys)
    $$ [Hys] as %ys' ⟨Hys, %Hperm, %Hsorted⟩
  · iframe
    isplitl []
    · iapply Pgids_isSorter
    ipureintro; omega
  have Hys' : ys' = sortPgids ys := sort_post_eq Hperm Hsorted
  subst Hys'
  wp_apply (hVerify _ iprop(f_ptr ↦ a ∗ ids_ptr ↦ idsl ∗ idsl ↦* sortPgids ys ∗
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
      have Hysnd : (sortPgids ys).Nodup := (sortPgids_perm ys).nodup_iff.2 (List.nodup_append.1 Hnd).2.1
      have Hdisj := (List.nodup_append.1 Hnd).2.2
      ihave %Hyl := ownSlice_len _ _ _ $$ Hys
      ihave IH2 : iprop(∃ (k idv pv : w64),
          "i" ∷ i_ptr ↦ k ∗ "id" ∷ id_ptr ↦ idv ∗ "prev" ∷ prev_ptr ↦ pv ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ ((sortPgids ys).length : Int) ∧
            (sint.nat k = 0 ∧ pv = W64 0 ∨ 0 < sint.nat k ∧ (sortPgids ys)[sint.nat k - 1]? = some pv)⌝)
          $$ [i id prev]
      · iexists W64 0, _, W64 0
        iframe
        ipureintro
        exact ⟨by word, by word, Or.inl ⟨rfl, rfl⟩⟩
      wp_for IH2
      wp_if_destruct
      · have Hb : sint.nat k < (sortPgids ys).length := by word
        list_elem (sortPgids ys) (sint.nat k) as e
        have Hemem : e ∈ ys := (sortPgids_perm ys).mem_iff.1 (List.mem_of_getElem? He_lookup)
        rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
        wp_apply wp_load_slice_index idsl (sint.Z k) (sortPgids ys) _ e Hk.1 $$ [Hys] with Hys
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
  have Hsrt : PgidsSorted (sortPgids ys) :=
    (sortPgids_sorted ys).imp fun h => by simp only [uint.Z]; omega
  have Hfs : PgidsSorted free := Hinc.imp fun h => by simp only [uint.Z]; omega
  have Hyl : (sortPgids ys).length = ys.length := (sortPgids_perm ys).length_eq
  wp_apply (hMerge ids idsl free (sortPgids ys) (DFrac.own 1) (DFrac.own 1) Hfs Hsrt (by omega))
    $$ [Hids Hys] as %r %out ⟨%Hout, Hids, Hys, Hcase⟩
  · iframe
  have Hperm : out.Perm (free ++ ys) :=
    Hout.2.trans (List.Perm.append_left free (sortPgids_perm ys))
  have Hout' : out = sortPgids (free ++ ys) :=
    (sortPgids_eq_of_sorted (Hout.1.imp fun h => by simp only [uint.Z] at h; omega) Hperm).symm
  subst Hout'
  iapply HΦ
  iexists r
  iframe Hidsf
  icases Hcase with (%Hc1 | %Hc2 | Hr)
  · obtain ⟨_, rfl, Hc⟩ := Hc1
    rw [Hc]
    iframe
  · obtain ⟨_, _, rfl, Hc⟩ := Hc2
    rw [Hc]
    iframe
  · icases Hr with ⟨-, Hr, Hrc⟩
    iframe

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
