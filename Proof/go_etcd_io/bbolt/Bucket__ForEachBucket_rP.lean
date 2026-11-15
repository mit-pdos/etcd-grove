/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__ForEachBucket_rP.lean` (U6c, `notes/bbolt-proof-plan.md`):
the reader's `db` is not nil; a cursor, `first`, then `next` over the bucket's entries in order
(`rCurKV`), the callback on the nested buckets' (`bktNames_at`, the count before the entry
`bktBefore`).
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__ForEachBucket_rP
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_i
public import Spec.go_etcd_io.bbolt.Cursor__first_r
public import Proof.go_etcd_io.bbolt.Read.Iter

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem rEnts_get_lt (v : View) (bv : List w8) (i : Nat) (pg : List w8) (idx : Nat)
    (h : (rEnts v bv)[i]? = some (pg, idx)) : idx < pageCount pg := by
  have hm := List.mem_of_getElem? h
  unfold rEnts lEnts at hm
  obtain ⟨pg', -, hm'⟩ := List.mem_flatMap.mp hm
  obtain ⟨j, hj, he⟩ := List.mem_map.mp hm'
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact List.mem_range.mp hj

theorem Bucket.ForEachBucket_rP.wp_proof
    (hcur : Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hfst : Cursor.first_r.spec (GF := GF) (hG := hG))
    (hnx : Cursor.next_r.spec (GF := GF) (hG := hG)) :
    Bucket.ForEachBucket_rP.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v b dq bv ibp pp fn I E hbv
  wp_start as ⟨Hk, Hb, HI, #Hfn⟩
  icases (persistent_entails_left (rdTxK_view K tx src q T v)) $$ Hk with ⟨Hk, %Hvw⟩
  have hok := rBktOK_of v Hvw.2 bv hbv
  ihave #Hpkg := (rdTxK_pkgInit K tx src q T v) $$ Hk
  unfold rBktP
  icases Hb with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hhdr, Hil⟩
  wp_auto
  icases rdTxK_db_acc K tx src q T v $$ Hk with ⟨%dd, Hdb, %Hnn, Hdbb⟩
  wp_auto
  simp only [decide_eq_false Hnn]
  wp_auto
  ihave Hk := Hdbb $$ Hdb
  icases rdTxK_stats_acc K tx src q T v $$ Hk with ⟨%r, #Hcore, #Hreg, Hst, Hkb⟩
  wp_apply hcur K tx r true q b dq $$ [Hst Htx] as %c ⟨%stk, Hc, Hs, Hcap, Hst, Htx⟩
  · iframe; iframe #
  ihave Hk := Hkb $$ Hst
  try wp_auto
  wp_apply hfst K tx src q T v b dq bv ibp pp c stk [] hok
    $$ [Hk HIB Htx Hbks Hpage Hroot Hnodes Hhdr Hil Hc Hs Hcap]
    as %k %vl %fl ⟨%stk1, %els1, %vl1, Hk, Hb, Hc, Hs, Hcap, Hcur, -⟩
  · iframe; iframe #; unfold rBktP; iframe
  try wp_auto
  ihave IH : (∃ (p : Nat) (k : GoSlice) (vl : GoSlice) (fl : w32) (stk1 : GoSlice)
      (els1 : List elemRef),
      "k" ∷ k_ptr ↦ k ∗ "flags" ∷ flags_ptr ↦ fl ∗ "Hk" ∷ rdTxK K tx src q T v ∗
      "Hb" ∷ rBktP v tx b dq bv ibp pp ∗ "Hc" ∷ c ↦ Cursor.mk b stk1 ∗ "Hs" ∷ stk1 ↦* els1 ∗
      "Hcap" ∷ ownSliceCap elemRef stk1 (DFrac.own 1) ∗ "HI" ∷ I (bktBefore v bv p) ∗
      "Hcur" ∷ rCurKV v bv pp els1 p k vl fl : IProp GF) $$ [k flags Hk Hb Hc Hs Hcap HI Hcur]
  · iexists 0, k, vl1, fl, stk1, els1
    simp only [named]
    iframe
  wp_for IH
  cleanup_bool_decide
  by_cases hkn : k = slice.nil
  · simp only [hkn, _root_.decide_true, Bool.not_true, intoVal_eq_iff, Bool.false_eq_true,
      _root_.decide_false, ↓reduceIte]
    wp_auto
    unfold rCurKV
    icases Hcur with (⟨%pg, %idx, ⟨-, -, %hent⟩, Hkv⟩ | %Hnil)
    · unfold rKV
      rw [if_pos (rEnts_get_lt v bv p pg idx hent)]
      icases Hkv with ⟨%ks, %vs, ⟨%hkn', -⟩, -⟩
      exact absurd rfl hkn'
    · iapply HΦ
      unfold rBktP
      rw [Hnil.1, bktBefore_end]
      iframe
      ileft
      iframe
      ipureintro; rfl
  · simp only [hkn, _root_.decide_false, Bool.not_false, _root_.decide_true,
      ↓reduceIte]
    unfold rCurKV
    icases Hcur with (⟨%pg, %idx, ⟨%hpos, -, %hent⟩, Hkv⟩ | %Hnil)
    · unfold rKV
      have hic := rEnts_get_lt v bv p pg idx hent
      rw [if_pos hic]
      icases Hkv with ⟨%ks, %vs, ⟨-, %hks, %hvs, %hfl⟩, #Hks, #Hvs⟩
      wp_auto
      have hlf : leafFlags pg idx = fl.toNat := by unfold leafFlags; rw [hfl]
      have hand : fl &&& W32 1 = W32 0 ↔ fl.toNat % 2 = 0 := by
        rw [BitVec.toNat_eq]; simp [BitVec.toNat_and, Nat.and_one_is_mod]
      have hget : (rEnts v bv)[p]? = some (pg, idx) := hent
      by_cases hb : fl &&& W32 1 = W32 0
      · rw [decide_eq_true hb]
        simp only [Bool.not_true]
        wp_auto
        have hnb : entBkt (pg, idx) = false := by
          unfold entBkt; simp only [decide_eq_false_iff_not]; rw [hlf, (hand).1 hb]
          simp [bucketLeafFlag]
        have hbb := bktBefore_succ v bv p _ hent
        rw [hnb] at hbb; simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hbb
        wp_for_post
        wp_apply hnx K tx src q T v b dq bv ibp pp c stk1 els1 p (p + 1) hok hpos
          $$ [Hk Hb Hc Hs Hcap] as %k' %vl' %fl' ⟨%stk2, %els2, Hk, Hb, Hc, Hs, Hcap, Hcur, -⟩
        · iframe
        try wp_auto
        iframe
        iexists p + 1, k', vl', fl', stk2, els2
        simp only [named]
        rw [hbb]
        unfold rCurKV
        iframe
      · rw [decide_eq_false hb]
        simp only [Bool.not_false]
        wp_auto
        have hyb : entBkt (pg, idx) = true := by
          unfold entBkt; simp only [decide_eq_true_eq]; rw [hlf]
          have := (not_congr hand).1 hb; simp [bucketLeafFlag]; omega
        have hbb := bktBefore_succ v bv p _ hent
        rw [hyb] at hbb; simp only [↓reduceIte] at hbb
        ihave #Hf := Hfn $$ %(bktBefore v bv p) %k %(leafKey pg idx) %ks
        wp_apply Hf $$ [Hk Hb HI Hks] as %err ⟨Hk, Hb, HIE⟩
        · unfold rBktP; iframe; iframe #
          ipureintro; exact ⟨hks, bktNames_at v bv p pg idx hent hyb⟩
        try wp_auto
        cases err with
        | ok ie =>
          icases HIE with (⟨%He, -⟩ | ⟨%He, HE⟩)
          · cases He
          wp_auto
          wp_for_post
          iapply HΦ
          iframe
          isplitl [Hb]
          · iExactEq Hb; rfl
          iright
          iframe
          ipureintro; exact He
        | nil =>
          icases HIE with (⟨-, HI⟩ | ⟨%He, -⟩)
          rotate_left
          · exact absurd rfl He
          wp_auto
          wp_for_post
          wp_apply hnx K tx src q T v b dq bv ibp pp c stk1 els1 p (p + 1) hok hpos
            $$ [Hk Hb Hc Hs Hcap] as %k' %vl' %fl' ⟨%stk2, %els2, Hk, Hb, Hc, Hs, Hcap, Hcur, -⟩
          · iframe; unfold rBktP; iExactEq Hb; rfl
          try wp_auto
          iframe
          iexists p + 1, k', vl', fl', stk2, els2
          simp only [named]
          rw [hbb]
          unfold rCurKV
          iframe

    · exact absurd Hnil.2.1 hkn

end proof

end bbolt
end EtcdGrove
end Perennial
