/-
`hashMap.mergeSpans` (U2 internal; ported from the old proof).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.hashMap.hashMap__mergeWithExistingSpan
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.hashMap.hashMap__idsFromFreemaps
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.hashMap.hashMap__idsFromForwardMap
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.hashMap.hashMap__idsFromBackwardMap
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.HashSegLemmas
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Callees
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

/-- `f.mergeSpans(ids)`: the ids (distinct, at least 2, not free) become free (the optional
checks hold: the maps agree, the ids are distinct and not free). -/
abbrev hashMap.mergeSpans.spec : Prop :=
  ∀ (h s : Loc) (free : List w64) (ids : GoSlice) (ys : List w64),
  (free ++ ys).Nodup → (∀ x ∈ free, 2 ≤ x.toNat) → (∀ y ∈ ys, 2 ≤ y.toNat) →
  free.length + ys.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      ownHashPart (GF := GF) h s free ∗ ids ↦* ys ∗ ownSliceCap w64 ids (DFrac.own 1) }}
    (App (Val (h @!! go.GoType.PointerType hashMap.ty @!! go!"mergeSpans")) (Val #ids))
  {{ RET #(); ownHashPart h s (sortPgids (free ++ ys)) }}

theorem hashMap.mergeSpans.wp_proof
    (hVerify : _root_.Perennial.EtcdGrove.bbolt.internal.common.Verify.spec (GF := GF) (hG := hG))
    (hIF : hashMap.idsFromFreemaps.spec (GF := GF) (hG := hG))
    (hIFw : hashMap.idsFromForwardMap.spec (GF := GF) (hG := hG))
    (hIBw : hashMap.idsFromBackwardMap.spec (GF := GF) (hG := hG))
    (hDE : _root_.Perennial.EtcdGrove.reflect.DeepEqual.spec_pgidSet (GF := GF) (hG := hG))
    (hMerge : hashMap.mergeWithExistingSpan.spec (GF := GF) (hG := hG)) :
    hashMap.mergeSpans.spec (GF := GF) (hG := hG) := by
  intro h s free idsl ys Hnd Hfge Hge2 Hlen
  wp_start as ⟨Hown, Hys, Hcap⟩
  ihave #Hc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave %Hyl := ownSlice_len _ _ _ $$ Hys
  iunfold ownHashPart at Hown
  icases Hown with ⟨%cnt0, %sp0, %bwm0, %sets0, Hraw0, %Hok0⟩
  ihave Hown : ownHashPart (GF := GF) h s free $$ [Hraw0]
  · unfold ownHashPart; iexists cnt0, sp0, bwm0, sets0; iframe; ipureintro; exact Hok0
  have Hfnd : free.Nodup := (List.nodup_append.1 Hnd).1
  have Hdisj := (List.nodup_append.1 Hnd).2.2
  wp_auto
  wp_if_destruct
  · have hys : ys = [] := by
      rw [Hif] at Hyl; exact List.eq_nil_of_length_eq_zero (by rw [Hyl.1]; rfl)
    subst hys
    iapply HΦ
    rw [List.append_nil, sortPgids_of_incr Hok0.2.1.1]
    iexact Hown
  ihave #Hsrt0 := Pgids_isSorter (GF := GF) idsl
  icases ownSlice_w64_len idsl ys _ $$ Hys with ⟨Hys, %Hkb⟩
  wp_apply (sort.wp_Sort (E := w64) (interface.mk go_etcd_io.bbolt.internal.common.Pgids.ty #idsl)
    (fun l => idsl ↦* l) pgLt slices.StrictWeakOrder_unsigned_lt ys) $$ [Hys]
    as %ys' ⟨Hys, %Hperm, %Hsorted⟩
  · iframe Hsrt0 Hys; ipureintro; omega
  have Hsrt2 : ys'.Perm ys := Hperm.symm
  have Hyseq : ys' = sortPgids ys := sort_post_eq Hperm Hsorted
  have Hysnd : ys'.Nodup := Hsrt2.nodup_iff.2 (List.nodup_append.1 Hnd).2.1
  have Hincr : PgidsIncr ys' := by rw [Hyseq]; exact sortPgids_incr (List.nodup_append.1 Hnd).2.1
  wp_apply (hVerify _ iprop(f_ptr ↦ h ∗ ids_ptr ↦ idsl ∗ idsl ↦* ys' ∗ ownHashPart h s free))
    $$ [f ids Hys Hown]
  · isplit
    · wp_auto
      wp_apply (hIF h s free) $$ [Hown] as %m1 %M1 ⟨Hm1, %HM1, Hown⟩
      · iexact Hown
      try wp_auto
      wp_apply (hIFw h s free) $$ [Hown] as %m2 %M2 ⟨Hm2, %HM2, Hown⟩
      · iexact Hown
      try wp_auto
      wp_apply (hIBw h s free) $$ [Hown] as %m3 %M3 ⟨Hm3, %HM3, Hown⟩
      · iexact Hown
      try wp_auto
      have HE12 : M1 = M2 := unit_map_eq (fun x => (HM1 x).trans (HM2 x).symm)
      have HE13 : M1 = M3 := unit_map_eq (fun x => (HM1 x).trans (HM3 x).symm)
      wp_apply (hDE m1 m2 M1 M2 (DFrac.own 1) (DFrac.own 1)) $$ [Hm1 Hm2] as %b ⟨%Hb, Hm1, Hm2⟩
      · iframe
      have Hbt : b = true := Hb.2 HE12
      subst Hbt
      try wp_auto
      wp_apply (hDE m1 m3 M1 M3 (DFrac.own 1) (DFrac.own 1)) $$ [Hm1 Hm3] as %b ⟨%Hb, Hm1, Hm3⟩
      · iframe
      have Hbt : b = true := Hb.2 HE13
      subst Hbt
      try wp_auto
      ihave %Hyl' := ownSlice_len _ _ _ $$ Hys
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
        have Hemem : e ∈ ys := Hsrt2.mem_iff.1 (List.mem_of_getElem? He_lookup)
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
        wp_apply wp_map_lookup2 $$ [Hm1] as Hm1
        · iexact Hm1
        try wp_auto
        wp_if_destruct
        · exfalso
          exact Hdisj e ((HM1 e).1 (by assumption)) e Hemem rfl
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
  iintro ⟨f, ids, Hys, Hown⟩
  have HL : ys'.length = ys.length := Hsrt2.length_eq
  have HL0 : 0 < ys'.length := by
    rw [HL, Hyl.1]
    have : idsl.len ≠ W64 0 := Hif
    word
  have Hfnd' : (free ++ ys').Nodup := (List.Perm.append_left free Hsrt2).nodup_iff.2 Hnd
  have Hge' : ∀ x ∈ free ++ ys', 2 ≤ x.toNat := by
    intro x hx
    rcases List.mem_append.1 hx with h' | h'
    · exact Hfge x h'
    · exact Hge2 x (Hsrt2.mem_iff.1 h')
  have Hlen' : free.length + ys'.length < 2 ^ 63 := by omega
  list_elem ys' 0 as a0
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
  wp_apply wp_load_slice_index idsl (sint.Z (W64 0)) ys' _ a0 (by word) $$ [Hys] with Hys
  · iframe; ipureintro; exact Ha0_lookup
  try wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
  wp_apply wp_load_slice_index idsl (sint.Z (W64 0)) ys' _ a0 (by word) $$ [Hys] with Hys
  · iframe; ipureintro; exact Ha0_lookup
  try wp_auto
  ihave IH : iprop(∃ (iv a b : w64) (st : Nat) (fk : List w64),
      "i" ∷ i_ptr ↦ iv ∗ "start" ∷ start_ptr ↦ a ∗ "Hend" ∷ end_ptr ↦ b ∗
      "Hys" ∷ idsl ↦* ys' ∗ "Hown" ∷ ownHashPart h s fk ∗
      "%Hi" ∷ ⌜1 ≤ sint.Z iv ∧ sint.Z iv ≤ (ys'.length : Int) ∧ st < sint.nat iv ∧
        ys'[st]? = some a ∧ ys'[sint.nat iv - 1]? = some b ∧
        (∀ j, st ≤ j → j + 1 < sint.nat iv → consec ys' j) ∧ fk.Perm (free ++ ys'.take st)⌝)
      $$ [i start «end» Hys Hown]
  · iexists W64 1, a0, a0, 0, free
    iframe
    ipureintro
    refine ⟨by word, by word, by word, Ha0_lookup, by rw [show sint.nat (W64 1) - 1 = 0 by word]; exact Ha0_lookup,
      fun j h1 h2 => by rw [show sint.nat (W64 1) = 1 by word] at h2; omega, by simp⟩
  wp_for IH
  obtain ⟨Hi1, Hi2, Hst, Ha, Hb, Hc, Hfk⟩ := Hi
  wp_if_destruct
  · have Hlt : sint.nat iv < ys'.length := by word
    list_elem ys' (sint.nat iv) as e
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index idsl (sint.Z iv) ys' _ e (by word) $$ [Hys] with Hys
    · iframe; ipureintro; exact He_lookup
    try wp_auto
    have hbe : b.toNat < e.toNat := by
      have := List.pairwise_iff_getElem.1 Hincr (sint.nat iv - 1) (sint.nat iv) (by omega) Hlt (by omega)
      obtain ⟨_, e1⟩ := List.getElem?_eq_some_iff.1 Hb
      obtain ⟨_, e2⟩ := List.getElem?_eq_some_iff.1 He_lookup
      rw [e1, e2] at this; exact this
    have hi1 : sint.nat (iv + W64 1) = sint.nat iv + 1 := by word
    wp_if_destruct
    · -- the next id is consecutive: the segment goes on
      try wp_auto
      wp_for_post
      iframe
      iexists iv + W64 1, a, _, st, fk
      iframe
      ipureintro
      rw [hi1]
      refine ⟨by word, by word, by omega, Ha, by rw [Nat.add_sub_cancel]; exact He_lookup,
        fun j h1 h2 => ?_, Hfk⟩
      rcases Nat.lt_or_ge (j + 1) (sint.nat iv) with h3 | h3
      · exact Hc j h1 h3
      · have hj : j = sint.nat iv - 1 := by omega
        subst hj
        unfold consec
        rw [show sint.nat iv - 1 + 1 = sint.nat iv by omega, getD_of_some He_lookup,
          getD_of_some Hb]
        word
    · -- a gap: merge the segment
      obtain ⟨M1, M2, M3, M4, M5, M6⟩ := seg_step Hfnd' Hge' Hst (by omega) Ha Hb Hc Hfk Hlen'
      wp_apply (hMerge h s fk a b M1 M2 M3 M4 M5) $$ [Hown] as %fk' ⟨%Hfk', Hown⟩
      · iframe
      try wp_auto
      wp_for_post
      iframe
      iexists iv + W64 1, e, e, sint.nat iv, fk'
      iframe
      ipureintro
      rw [hi1]
      exact ⟨by word, by word, by omega, He_lookup, by rw [Nat.add_sub_cancel]; exact He_lookup,
        fun j h1 h2 => by omega, M6 fk' Hfk'⟩
  · -- the last segment
    have Hall : sint.nat iv = ys'.length := by word
    rw [Hall] at Hb Hst Hc
    obtain ⟨M1, M2, M3, M4, M5, M6⟩ := seg_step Hfnd' Hge' Hst (by omega) Ha Hb Hc Hfk Hlen'
    try wp_auto
    wp_apply (hMerge h s fk a b M1 M2 M3 M4 M5) $$ [Hown] as %fk' ⟨%Hfk', Hown⟩
    · iframe
    try wp_auto
    have Hp : fk'.Perm (free ++ ys) := by
      have := M6 fk' Hfk'
      rw [List.take_length] at this
      exact this.trans (List.Perm.append_left free Hsrt2)
    iunfold ownHashPart at Hown
    icases Hown with ⟨%c1, %sp1, %bw1, %se1, Hraw1, %Hok1⟩
    have Heq : sortPgids (free ++ ys) = fk' :=
      sortPgids_eq_of_sorted (Hok1.2.1.1.imp fun h => Nat.le_of_lt h) Hp
    iapply HΦ
    rw [Heq]
    unfold ownHashPart; iexists c1, sp1, bw1, se1; iframe; ipureintro; exact Hok1

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
