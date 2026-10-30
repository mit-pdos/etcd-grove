module
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__mergeSpans
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__mergeWithExistingSpan
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__idsFromFreemaps
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__idsFromForwardMap
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__idsFromBackwardMap
public import Spec.go_etcd_io.bbolt.internal.common.Verify
public import Spec.sort.Sort
public import Spec.reflect.DeepEqualPgidSet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

/-- Two sets with the same elements are equal. -/
theorem unit_map_eq {M1 M2 : GMap w64 Unit} (h : ∀ x, (M1 !! x).isSome ↔ (M2 !! x).isSome) :
    M1 = M2 := by
  apply GMap.map_eq; intro k
  have := h k
  cases h1 : M1 !! k <;> cases h2 : M2 !! k <;> simp_all

/-- `n ≥ 1` consecutive ids of `f` from position `st` (the first `a`): they are the ids from
`a` on, the last `a + n - 1`. -/
theorem seg_mem {f : List w64} {st n : Nat} {a : w64} (hlen : st + n ≤ f.length) (hn : 1 ≤ n)
    (ha : f[st]? = some a) (hc : ∀ j, st ≤ j → j + 1 < st + n → consec f j) :
    uint.Z a + n ≤ 2 ^ 64 ∧ (∀ x, x ∈ (f.drop st).take n ↔ inRun a n x) ∧
    ∀ b, f[st + n - 1]? = some b → uint.Z b = uint.Z a + (n - 1) := by
  have hv : ∀ k, st ≤ k → k < st + n →
      f[k]? = some (f.getD k 0) ∧ uint.Z (f.getD k 0) = uint.Z a + (k - st) := by
    intro k h1 h2
    refine ⟨by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; simp, ?_⟩
    have := consec_sum (f := f) (st := st) (k - st) (fun j h1' h2' => hc j h1' (by omega))
    rw [show st + (k - st) = k by omega, getD_of_some ha] at this; omega
  have hlast := (hv (st + n - 1) (by omega) (by omega)).2
  have hb64 : uint.Z (f.getD (st + n - 1) 0) < 2 ^ 64 := by word
  refine ⟨by omega, fun x => ?_, fun b hb => ?_⟩
  · rw [List.mem_iff_getElem?]
    constructor
    · rintro ⟨k, hk⟩
      rw [List.getElem?_take] at hk
      split at hk
      · rename_i hkn
        rw [List.getElem?_drop] at hk
        obtain ⟨e1, e2⟩ := hv (st + k) (by omega) (by omega)
        rw [e1] at hk; cases hk
        unfold inRun; rw [e2]; omega
      · cases hk
    · intro hx
      unfold inRun at hx
      refine ⟨(uint.Z x - uint.Z a).toNat, ?_⟩
      rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop]
      obtain ⟨e1, e2⟩ := hv (st + (uint.Z x - uint.Z a).toNat) (by omega) (by omega)
      rw [e1]
      congr 1
      have : uint.Z (f.getD (st + (uint.Z x - uint.Z a).toNat) 0) = uint.Z x := by rw [e2]; omega
      word
  · obtain ⟨e1, e2⟩ := hv (st + n - 1) (by omega) (by omega)
    rw [e1] at hb; cases hb; rw [e2]; omega

/-- One merged segment of the sorted ids, from position `st` to `i - 1` (ids `a` to `b`): the
preconditions of `mergeWithExistingSpan(a, b)` on the free ids `fk` (the free ids and the
segments before), and the free ids after it. -/
theorem seg_step {ys' free fk : List w64} {st i : Nat} {a b : w64}
    (hfnd : (free ++ ys').Nodup) (hge : ∀ x ∈ free ++ ys', 2 ≤ uint.Z x) (hst : st < i)
    (hi : i ≤ ys'.length) (ha : ys'[st]? = some a) (hb : ys'[i - 1]? = some b)
    (hc : ∀ j, st ≤ j → j + 1 < i → consec ys' j) (hfk : fk.Perm (free ++ ys'.take st))
    (hlen : free.length + ys'.length < 2 ^ 63) :
    uint.Z a ≤ uint.Z b ∧ 1 ≤ uint.Z a ∧ (∀ x ∈ fk, 1 ≤ uint.Z x) ∧
    (∀ x, inRun a (uint.nat (b - a) + 1) x → x ∉ fk) ∧
    fk.length + (uint.nat (b - a) + 1) < 2 ^ 63 ∧
    ∀ fk' : List w64, fk'.Perm (fk ++ runIds a (uint.nat (b - a) + 1)) → fk'.Perm (free ++ ys'.take i) := by
  have hnd' : ys'.Nodup := (List.nodup_append.1 hfnd).2.1
  obtain ⟨hnw, hmem, hbv⟩ := seg_mem (f := ys') (st := st) (n := i - st) (by omega) (by omega) ha
    (fun j h1 h2 => hc j h1 (by omega))
  have hbz := hbv b (by rw [show st + (i - st) - 1 = i - 1 by omega]; exact hb)
  have hn : uint.nat (b - a) + 1 = i - st := by word
  rw [hn]
  have hsegsub : ∀ x, x ∈ (ys'.drop st).take (i - st) → x ∈ ys'.drop st :=
    fun x hx => List.take_subset _ _ hx
  have hdd := List.nodup_append.1 (by rw [List.take_append_drop]; exact hnd' :
    (ys'.take st ++ ys'.drop st).Nodup)
  have hfl : fk.length = free.length + st := by
    rw [hfk.length_eq, List.length_append, List.length_take]; omega
  refine ⟨by omega, by have := hge a (List.mem_append_right _ (List.mem_of_getElem? ha)); omega, fun x hx => ?_,
    fun x hx hxf => ?_, by omega, fun fk' hfk' => ?_⟩
  · have := hge x (by
      rcases List.mem_append.1 (hfk.mem_iff.1 hx) with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.take_subset _ _ h))
    omega
  · have hxs := hsegsub x ((hmem x).2 hx)
    rcases List.mem_append.1 (hfk.mem_iff.1 hxf) with h | h
    · exact (List.nodup_append.1 hfnd).2.2 x h x (List.drop_subset _ _ hxs) rfl
    · exact hdd.2.2 x h x hxs rfl
  · have hseg : (runIds a (i - st)).Perm ((ys'.drop st).take (i - st)) :=
      perm_of_mem (runIds_nodup hnw) ((hdd.2.1.sublist (List.take_sublist _ _)))
        (fun x => by rw [mem_runIds hnw, hmem x])
    refine hfk'.trans ((List.Perm.append hfk hseg).trans ?_)
    rw [List.append_assoc, ← List.take_add, show st + (i - st) = i by omega]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem hashMap.mergeSpans.wp_proof (hSort : sort.Sort.spec (GF := GF) (hG := hG))
    (hVerify : Verify.spec (GF := GF) (hG := hG))
    (hIF : hashMap.idsFromFreemaps.spec (GF := GF) (hG := hG))
    (hIFw : hashMap.idsFromForwardMap.spec (GF := GF) (hG := hG))
    (hIBw : hashMap.idsFromBackwardMap.spec (GF := GF) (hG := hG))
    (hDE : reflect.DeepEqual.spec (GF := GF) (hG := hG))
    (hMerge : hashMap.mergeWithExistingSpan.spec (GF := GF) (hG := hG)) :
    hashMap.mergeSpans.spec (GF := GF) (hG := hG) := by
  intro h s free idsl ys Hnd Hge2 Hlen
  wp_start as ⟨Hown, Hys, Hcap⟩
  unfold ownHashMap
  icases Hown with ⟨-, Hown, %Hfge⟩
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
    isplitr
    · ipureintro; exact ⟨Hok0.2.1.1, by simp⟩
    isplitl []
    · iexact Hpkg
    isplitl [Hown]
    · iexact Hown
    ipureintro; simpa using Hfge
  wp_apply (hSort _ _ ys (Or.inl rfl)) $$ Hys as %ys' ⟨%Hsrt, Hys⟩
  have Hysnd : ys'.Nodup := Hsrt.2.nodup_iff.2 (List.nodup_append.1 Hnd).2.1
  have Hincr : PgidsIncr ys' := pgidsIncr_of_sorted_nodup Hsrt.1 Hysnd
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
  have HL : ys'.length = ys.length := Hsrt.2.length_eq
  have HL0 : 0 < ys'.length := by
    rw [HL, Hyl.1]
    have : idsl.len ≠ W64 0 := Hif
    word
  have Hfnd' : (free ++ ys').Nodup := (List.Perm.append_left free Hsrt.2).nodup_iff.2 Hnd
  have Hge' : ∀ x ∈ free ++ ys', 2 ≤ uint.Z x := by
    intro x hx
    rcases List.mem_append.1 hx with h' | h'
    · exact Hfge x h'
    · exact Hge2 x (Hsrt.2.mem_iff.1 h')
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
    have hbe : uint.Z b < uint.Z e := by
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
      exact this.trans (List.Perm.append_left free Hsrt.2)
    iunfold ownHashPart at Hown
    icases Hown with ⟨%c1, %sp1, %bw1, %se1, Hraw1, %Hok1⟩
    iapply HΦ
    isplitr
    · ipureintro; exact ⟨Hok1.2.1.1, Hp⟩
    isplitl []
    · iexact Hpkg
    isplitl [Hraw1]
    · unfold ownHashPart; iexists c1, sp1, bw1, se1; iframe; ipureintro; exact Hok1
    ipureintro
    intro x hx
    have := Hp.mem_iff.1 hx
    rcases List.mem_append.1 this with h' | h'
    · exact Hfge x h'
    · exact Hge2 x h'

end proof

end bbolt
end EtcdGrove
end Perennial
