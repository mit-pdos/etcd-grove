/-
`array.Allocate(txid, n)` (U2 internal): the first run of `n` consecutive free ids, removed
from the free ids and the cache and allocated by `txid`; `0` if there is none.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Own
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.ArrayLemmas

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

set_option maxHeartbeats 800000 in
theorem arrayImpl_allocate' (a : Loc) : (arrayImpl (GF := GF) a).AllocateSpec := by
  intro s fl txid n Hn
  dsimp only [arrayImpl]
  wp_start as ⟨#Hhdl, Hsh, ⟨%ids, Hidsf, Hids, Hidscap⟩⟩
  iunfold ownSh at Hsh
  icases Hsh with ⟨%c, Hsh, %Hok⟩
  iunfold ownShC at Hsh
  iNamed Hsh
  obtain ⟨Hc, Hwf⟩ := Hok
  have Hincr : PgidsIncr fl.free := Hwf.2.2.1
  ihave %Hfl := ownSlice_len _ _ _ $$ Hids
  ihave %Hswf := ownSlice_wf _ _ _ $$ Hids
  have Hge2 : ∀ x ∈ fl.free, 2 ≤ x.toNat :=
    fun x hx => Hwf.2.1 x (by unfold FLPg.allIds; exact List.mem_append_left _ hx)
  wp_auto
  wp_if_destruct
  · iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    isplitl [Hif Hal Hallocs Hca Hcache Hpe Hpending Hpds]
    · iunfold ownSh
      iexists c
      isplitl
      · iunfold ownShC
        iexists al, ca, pe, pp
        iframe
      · ipureintro; exact ⟨Hc, Hwf⟩
    · iexists ids; iframe
  try wp_auto
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => Hgi
  have Hn1 : 1 ≤ sint.nat n := by word
  ihave IH : iprop(∃ (k gi idv pv iv : w64),
      "i" ∷ i_ptr ↦ k ∗ "Hgi" ∷ gi_ptr ↦ gi ∗ "id" ∷ id_ptr ↦ idv ∗ "previd" ∷ previd_ptr ↦ pv ∗
      "initial" ∷ initial_ptr ↦ iv ∗ "Hids" ∷ ids ↦* fl.free ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (fl.free.length : Int) ∧
        scanInv fl.free (sint.nat k) pv iv ∧ ∀ i' < sint.nat k, ¬ runEnd fl.free (sint.nat n) i'⌝)
      $$ [i Hgi id previd initial Hids]
  · iexists W64 0, _, _, W64 0, _
    iframe
    ipureintro
    refine ⟨by word, by word, scanInv_zero _ _, fun i' h => ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl] at h; omega
  wp_for IH
  wp_if_destruct
  · have Hb : sint.nat k < fl.free.length := by word
    list_elem fl.free (sint.nat k) as e
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index ids (sint.Z k) fl.free _ e Hk.1 $$ [Hids] with Hids
    · iframe; ipureintro; exact He_lookup
    have He2 : 2 ≤ uint.Z e := by
      have := Hge2 e (List.mem_of_getElem? He_lookup); simp only [uint.Z]; omega
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
    have Hdec : ((e - iv') + W64 1 = n) ↔ runEnd fl.free (sint.nat n) (sint.nat k) := by
      rw [Hrun']; constructor <;> intro h <;> word
    by_cases Hfound : runEnd fl.free (sint.nat n) (sint.nat k)
    · rw [decide_eq_true (Hdec.2 Hfound)]
      have Hstart := runEnd_start Hn1 Hfound He_lookup (Hrun'.1 Hfound)
      obtain ⟨Hcanb, Hcanin, Hfilt⟩ := run_remove Hn1 Hincr Hfound Hstart
      have Hnk : sint.nat n ≤ sint.nat k + 1 := Hfound.1
      have e4 : sint.nat (ids.len - n) =
          fl.free.length - (sint.nat k + 1 - (sint.nat k + 1 - sint.nat n)) := by word
      have e1 : sint.nat (k - n + W64 1) = sint.nat k + 1 - sint.nat n := by word
      have e3 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
      have e2 : sint.nat ids.len = fl.free.length := by word
      try wp_auto
      wp_join iprop(∃ (ids' : GoSlice), "Hidsf" ∷ structFieldRef array' go!"ids" a ↦ ids' ∗
          "Hids" ∷ ids' ↦* (fl.free.take (sint.nat k + 1 - sint.nat n) ++ fl.free.drop (sint.nat k + 1)) ∗
          "Hidscap" ∷ ownSliceCap w64 ids' (DFrac.own 1) ∗
          "f" ∷ f_ptr ↦ a ∗ "n" ∷ n_ptr ↦ n ∗ "Hgi" ∷ gi_ptr ↦ k)
        with [Hidsf Hids Hidscap f n Hgi] as ⟨%ids', Hidsf, Hids, Hidscap, f, n, Hgi⟩
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
        icases (ownSlice_split_all (k + W64 1) ids _ _ ⟨by word, by word⟩).1 $$ Hids with ⟨-, Hids⟩
        icases (ownSliceCap_slice ids (k + W64 1) _ ⟨by word, by word, Hswf.2⟩).1 $$ Hidscap
          with Hidscap
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
          ids fl.free (k - n + W64 1) ids.len (k + W64 1) ids.len
          ⟨by word, by word, by word⟩ ⟨by word, by word, by word⟩) $$ [$Hids] as %m ⟨_, Hids⟩
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
        icases (ownSlice_split_all (ids.len - n) ids _ _ ⟨by word, by word⟩).1 $$ Hids
          with ⟨Hids, Htail⟩
        ihave Hidscap := ownSlice_slice_absorb_capacity ids _ (W64 0) (ids.len - n)
          ⟨by word, by word, by word⟩ $$ [Htail Hidscap]
        · iframe
        try wp_auto
        wp_join_done
        iexists _
        isimp only [e4, e1, e3, e2,
          copy_down_take fl.free (sint.nat k + 1 - sint.nat n) (sint.nat k + 1) (by omega) (by omega)]
          at Hids
        iframe
      have Hnn : uint.nat n = sint.nat n := by word
      have Hcanb' : iv'.toNat + uint.nat n ≤ 2 ^ 64 := by rw [Hnn]; exact Hcanb
      ihave IH3 : iprop(∃ (j : w64) (m' : GMap w64 Unit),
          "i" ∷ i_ptr ↦ j ∗ "Hcache" ∷ ca ↦$ m' ∗
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
      have Hcan : fl.canAlloc iv' (sint.nat n) := ⟨Hcanb, Hcanin⟩
      have Hiv0 : iv' ≠ W64 0 := by
        have := Hge2 iv' (Hcanin iv' ⟨Nat.le_refl _, by omega⟩); intro h; subst h; simp at this
      isplitr
      · ipureintro; exact ⟨Hiv0, Hcan⟩
      have Hwf' := alloc_WF Hwf txid iv' (sint.nat n)
      have Hc' : cacheOK m' (fl.alloc txid iv' (sint.nat n)) := by
        intro x; rw [Hj.2 x, Hc x, alloc_allIds Hwf Hcan x]
      have Hfree : (fl.alloc txid iv' (sint.nat n)).free =
          fl.free.take (sint.nat k + 1 - sint.nat n) ++ fl.free.drop (sint.nat k + 1) := Hfilt
      isplitl [Hif Hal Hallocs Hca Hcache Hpe Hpending Hpds]
      · iunfold ownSh
        iexists m'
        isplitl
        · iunfold ownShC
          iexists al, ca, pe, pp
          iframe
        · ipureintro; exact ⟨Hc', Hwf'⟩
      · iexists ids'
        rw [Hfree]
        iframe
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
  have Hall : sint.nat k = fl.free.length := by word
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  isplitl [Hif Hal Hallocs Hca Hcache Hpe Hpending Hpds]
  · iunfold ownSh
    iexists c
    isplitl
    · iunfold ownShC
      iexists al, ca, pe, pp
      iframe
    · ipureintro; exact ⟨Hc, Hwf⟩
  · iexists ids; iframe
  done



end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
