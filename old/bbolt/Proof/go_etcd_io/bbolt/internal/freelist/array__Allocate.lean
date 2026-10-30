module
public import Spec.go_etcd_io.bbolt.internal.freelist.array__Allocate
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas
public import Proof.go_etcd_io.bbolt.internal.freelist.ArrayLemmas

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

set_option maxHeartbeats 800000 in
theorem array.Allocate.wp_proof : array.Allocate.spec (GF := GF) (hG := hG) := by
  intro a s σ txid n Hn
  wp_start as Hfl
  iunfold ownFL at Hfl
  isimp only [arrayImpl] at Hfl
  iunfold arrayHdl, ownArrayPart, ownShared, ownSharedC at Hfl
  icases Hfl with ⟨#Hhdl, ⟨%sv, %c, Hsh, %Hok⟩, Hown⟩
  iNamed Hsh
  iNamed Hown
  obtain ⟨Hc, Hwf⟩ := Hok
  ihave %Hfl := ownSlice_len _ _ _ $$ Hids
  ihave %Hswf := ownSlice_wf _ _ _ $$ Hids
  have Hge2 : ∀ x ∈ σ.free, 2 ≤ uint.Z x :=
    fun x hx => Hwf.2.1 x (by unfold FLState.allIds; exact List.mem_append_left _ hx)
  wp_auto
  wp_if_destruct
  · iapply HΦ
    ileft
    isplitr
    · ipureintro
      refine ⟨rfl, fun i hr => ?_⟩
      have := hr.2.1
      word
    unfold ownFL; simp only [arrayImpl]; unfold arrayHdl ownArrayPart ownShared ownSharedC
    iframe Hhdl
    isplitl [Hs Hro Hro_cap Hallocs Hcache Hpending Hpds]
    · iexists sv, c
      isplitl
      · iexists pp; iframe; ipureintro; exact Hiface
      · ipureintro; exact ⟨Hc, Hwf⟩
    · iexists ids; iframe; ipureintro; exact Hincr
  try wp_auto
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => Hgi
  have Hn1 : 1 ≤ sint.nat n := by word
  ihave IH : iprop(∃ (k gi idv pv iv : w64),
      "i" ∷ i_ptr ↦ k ∗ "Hgi" ∷ gi_ptr ↦ gi ∗ "id" ∷ id_ptr ↦ idv ∗ "previd" ∷ previd_ptr ↦ pv ∗
      "initial" ∷ initial_ptr ↦ iv ∗ "Hids" ∷ ids ↦* σ.free ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (σ.free.length : Int) ∧
        scanInv σ.free (sint.nat k) pv iv ∧ ∀ i' < sint.nat k, ¬ runEnd σ.free (sint.nat n) i'⌝)
      $$ [i Hgi id previd initial Hids]
  · iexists W64 0, _, _, W64 0, _
    iframe
    ipureintro
    refine ⟨by word, by word, scanInv_zero _ _, fun i' h => ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl] at h; omega
  wp_for IH
  wp_if_destruct
  · have Hb : sint.nat k < σ.free.length := by word
    list_elem σ.free (sint.nat k) as e
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index ids (sint.Z k) σ.free _ e Hk.1 $$ [Hids] with Hids
    · iframe; ipureintro; exact He_lookup
    have He2 : 2 ≤ uint.Z e := Hge2 e (List.mem_of_getElem? He_lookup)
    try wp_auto
    rw [decide_eq_false (show ¬ uint.Z e ≤ uint.Z (W64 1) by word)]
    try wp_auto
    wp_join iprop(initial_ptr ↦ (if pv = W64 0 ∨ e - pv ≠ W64 1 then e else iv) ∗
        previd_ptr ↦ pv ∗ id_ptr ↦ e) at next with [initial previd id] as ⟨initial, previd, id⟩
    · try wp_auto
      wp_if_destruct
      · try wp_auto
        wp_join_done
      · wp_if_destruct
        · try wp_auto
          wp_join_done
          have hc : ¬(pv = W64 0 ∨ e - pv ≠ W64 1) := by rintro (h | h) <;> simp_all
          rw [if_neg hc]
          iframe
        · try wp_auto
          wp_join_done
          rw [if_pos (Or.inr Hif)]
          iframe
    obtain ⟨Hinv', Hle', Hrun'⟩ := scan_run Hn1 Hincr Hge2 He_lookup Hk.2.2.1 Hk.2.2.2
    generalize (if pv = W64 0 ∨ e - pv ≠ W64 1 then e else iv) = iv' at Hinv' Hle' Hrun' ⊢
    have Hdec : ((e - iv') + W64 1 = n) ↔ runEnd σ.free (sint.nat n) (sint.nat k) := by
      rw [Hrun']; constructor <;> intro h <;> word
    by_cases Hfound : runEnd σ.free (sint.nat n) (sint.nat k)
    · rw [decide_eq_true (Hdec.2 Hfound)]
      have Hstart := runEnd_start Hn1 Hfound He_lookup (Hrun'.1 Hfound)
      obtain ⟨Hcanb, Hcanin, Hfilt⟩ := run_remove Hn1 Hincr Hfound Hstart
      have Hnk : sint.nat n ≤ sint.nat k + 1 := Hfound.1
      have e4 : sint.nat (ids.len - n) =
          σ.free.length - (sint.nat k + 1 - (sint.nat k + 1 - sint.nat n)) := by word
      have e1 : sint.nat (k - n + W64 1) = sint.nat k + 1 - sint.nat n := by word
      have e3 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
      have e2 : sint.nat ids.len = σ.free.length := by word
      try wp_auto
      wp_join iprop(∃ (ids' : GoSlice), "Hidsf" ∷ structFieldRef array' go!"ids" a ↦ ids' ∗
          "Hids" ∷ ids' ↦* (σ.free.take (sint.nat k + 1 - sint.nat n) ++ σ.free.drop (sint.nat k + 1)) ∗
          "f" ∷ f_ptr ↦ a ∗ "n" ∷ n_ptr ↦ n ∗ "Hgi" ∷ gi_ptr ↦ k)
        with [Hidsf Hids f n Hgi] as ⟨%ids', Hidsf, Hids, f, n, Hgi⟩
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
        icases (ownSlice_split_all (k + W64 1) ids _ _ ⟨by word, by word⟩).1 $$ Hids with ⟨-, Hids⟩
        try wp_auto
        wp_join_done
        iexists _
        rw [show sint.nat k + 1 - sint.nat (k + W64 1) = 0 by word, List.take_zero, List.nil_append,
          show sint.nat k + 1 = sint.nat (k + W64 1) by word]
        iframe
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
        try wp_auto
        wp_apply (wp_slice_copy_within (st := go_etcd_io.bbolt.internal.common.Pgid.ty.SliceType)
          ids σ.free (k - n + W64 1) ids.len (k + W64 1) ids.len
          ⟨by word, by word, by word⟩ ⟨by word, by word, by word⟩) $$ [$Hids] as %m ⟨_, Hids⟩
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
        icases (ownSlice_split_all (ids.len - n) ids _ _ ⟨by word, by word⟩).1 $$ Hids with ⟨Hids, -⟩
        try wp_auto
        wp_join_done
        iexists _
        isimp only [e4, e1, e3, e2,
          copy_down_take σ.free (sint.nat k + 1 - sint.nat n) (sint.nat k + 1) (by omega) (by omega)]
          at Hids
        iframe
      have Hnn : uint.nat n = sint.nat n := by word
      have Hcanb' : uint.Z iv' + ↑(uint.nat n) ≤ 2 ^ 64 := by rw [Hnn]; exact Hcanb
      ihave IH3 : iprop(∃ (j : w64) (m' : GMap w64 Unit),
          "i" ∷ i_ptr ↦ j ∗ "Hcache" ∷ sv.cache' ↦$ m' ∗
          "%Hj" ∷ ⌜uint.Z j ≤ uint.Z n ∧
            ∀ x, (m' !! x).isSome ↔ (c !! x).isSome ∧ ¬ inRun iv' (uint.nat j) x⌝) $$ [i Hcache]
      · iexists W64 0, c
        iframe
        ipureintro
        refine ⟨by word, fun x => ?_⟩
        simp only [inRun, show uint.nat (W64 0) = 0 from rfl]
        constructor
        · intro h; exact ⟨h, by omega⟩
        · exact fun h => h.1
      wp_for IH3
      wp_if_destruct
      · try wp_auto
        wp_apply wp_mapDelete $$ Hcache as Hcache
        wp_for_post
        iframe
        iexists j + W64 1, _
        iframe
        ipureintro
        have hj1 : uint.nat (j + W64 1) = uint.nat j + 1 := by word
        refine ⟨by word, fun x => ?_⟩
        rw [hj1, inRun_succ Hcanb' (by word), GMap.lookup_delete_iff]
        by_cases hx : iv' + j = x
        · subst hx; simp
        · simp only [hx, if_false, Hj.2 x]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨h1, by rintro (h | h); exact h2 h; exact hx h.symm⟩
          · rintro ⟨h1, h2⟩
            exact ⟨h1, fun h => h2 (Or.inl h)⟩
      have Hjn : uint.nat j = sint.nat n := by word
      rw [Hjn] at Hj
      try wp_auto
      wp_apply wp_mapInsert $$ Hallocs as Hallocs
      try wp_auto
      wp_for_post
      try wp_auto
      iapply HΦ
      iright
      iexists (sint.nat k)
      isplitr
      · ipureintro; exact ⟨Hfound, Hk.2.2.2, Hstart⟩
      have Hcan : σ.canAllocate iv' (sint.nat n) := ⟨Hcanb, Hcanin⟩
      have Hwf' := allocate_WF Hwf txid iv' (sint.nat n)
      have Hc' := allocate_cacheOK (txid := txid) Hwf Hc Hcan Hj.2
      have Hfree : (σ.allocate txid iv' (sint.nat n)).free =
          σ.free.take (sint.nat k + 1 - sint.nat n) ++ σ.free.drop (sint.nat k + 1) := Hfilt
      unfold ownFL; simp only [arrayImpl]; unfold arrayHdl ownArrayPart ownShared ownSharedC
      iframe Hhdl
      isplitl [Hs Hro Hro_cap Hallocs Hcache Hpending Hpds]
      · iexists sv, m'
        isplitl
        · iexists pp
          simp only [FLState.allocate]
          iframe
          ipureintro; exact Hiface
        · ipureintro; exact ⟨Hc', Hwf'⟩
      · iexists ids'
        rw [Hfree]
        isplitl [Hidsf]
        · iexact Hidsf
        isplitr
        · ipureintro; rw [← Hfree]; exact Hwf'.2.2.1
        iexact Hids
      done
    · rw [decide_eq_false (fun h => Hfound (Hdec.1 h))]
      try wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, _, e, e, iv'
      iframe
      ipureintro
      have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
      rw [hk1]
      refine ⟨by word, by word, Hinv', fun i' h => ?_⟩
      rcases Nat.lt_or_ge i' (sint.nat k) with h' | h'
      · exact Hk.2.2.2 i' h'
      · rw [show i' = sint.nat k by omega]; exact Hfound
  have Hall : sint.nat k = σ.free.length := by word
  iapply HΦ
  ileft
  isplitr
  · ipureintro
    refine ⟨rfl, runEnd_none (fun i' h => Hk.2.2.2 i' (by omega))⟩
  unfold ownFL; simp only [arrayImpl]; unfold arrayHdl ownArrayPart ownShared ownSharedC
  iframe Hhdl
  isplitl [Hs Hro Hro_cap Hallocs Hcache Hpending Hpds]
  · iexists sv, c
    isplitl
    · iexists pp; iframe; ipureintro; exact Hiface
    · ipureintro; exact ⟨Hc, Hwf⟩
  · iexists ids; iframe; ipureintro; exact Hincr
  done

end proof

end bbolt
end EtcdGrove
end Perennial
