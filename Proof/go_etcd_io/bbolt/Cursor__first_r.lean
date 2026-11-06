/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__first_r.lean` (U6, `notes/bbolt-proof-plan.md`): the
stack reset to the root at index `0`, the descent (`goToFirstElementOnTheStack`), `next` from an
empty first leaf, then `keyValue` (a nested bucket's value dropped).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__first_r
public import Spec.go_etcd_io.bbolt.Cursor__goToFirstElementOnTheStack_r
public import Spec.go_etcd_io.bbolt.Bucket__pageNode_r
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Proof.go_etcd_io.bbolt.Read.Root

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Cursor.first_r.wp_proof
    (hg : Cursor.goToFirstElementOnTheStack_r.spec (GF := GF) (hG := hG))
    (hnx : Cursor.next_r.spec (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue_r.spec (GF := GF) (hG := hG))
    (hpn : Bucket.pageNode_r.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG)) :
    Cursor.first_r.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v b dq bv ibp pp c stk els hok
  wp_start as ⟨Hk, Hb, Hc, Hs, Hcap⟩
  icases (persistent_entails_left (rdTxK_view K tx src q T v)) $$ Hk with ⟨Hk, %Hvw⟩
  obtain ⟨-, C, hokC, hvC⟩ := Hvw
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  obtain ⟨-, -, -, pht, hpht⟩ := hokC.1
  rw [← hpv] at hpht
  obtain ⟨hrt, hrh⟩ := rRoot_ok pht hpht hok
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  wp_auto
  rw [if_pos ⟨by decide, by decide, by word⟩]
  icases ownSlice_slice_with_cap (V := elemRef) (W64 0) (W64 0) stk els ⟨by decide, by decide, by word⟩
    $$ [Hs Hcap] with ⟨-, Hs, Hcap⟩
  · iframe
  have hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 0)) els = ([] : List elemRef) := by
    simp [subslice]
  rw [hsub]
  wp_auto
  unfold rBktP
  icases Hb with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hhdr, Hil⟩
  rw [show (Cursor.mk (Cursor.mk b stk).bucket' (slice.slice stk elemRef (W64 0) (W64 0))).bucket' = b from rfl]
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_rd_rootPage hRP K tx src q T v bv ibp hok.1 $$ [Hk Hhdr] as ⟨Hk, Hhdr⟩
  · iframe
  rw [show (decode (List.take 8 (bytesAt bv 0 16)) : w64) = (inBucketOf bv).root' from rfl]
  have hroot : (inBucketOf bv).root'.toNat = inBucketRoot bv := rfl
  obtain ⟨l, pg, hpa, h16, hpg⟩ := rTree_page v bv pp (inBucketRoot bv) hrt
  wp_apply hpn K tx src q T v b dq bv ibp pp (inBucketOf bv).root' l pg hok.1 (by rw [hroot]; exact hpa)
    $$ [Hk HIB Htx Hbks Hpage Hroot Hnodes Hhdr Hil] as ⟨Hk, Hb⟩
  · iframe; unfold rBktP; iframe
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl', -⟩
  wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl'] as %s1 ⟨Hs, Hcap, -⟩
  try wp_auto
  have hhd : rHdF v bv pp (rFuel v bv) (inBucketRoot bv) ⟨l, null, W64 0⟩ 0 := by
    rcases hpg with ⟨hlf, -⟩ | ⟨hbr, hi, -, hwm, hbwf, -⟩
    · right; exact ⟨pg, ⟨hpa, rfl, hlf, Nat.zero_le _, rfl⟩, Or.inl rfl⟩
    · left; exact ⟨pg, 0, ⟨hi, hpa, rfl, hbr, hbwf.1, rfl⟩, by rw [entsBefore_zero]⟩
  have hm : 0 < rFuel v bv := by unfold rFuel; split <;> omega
  wp_apply hg K tx src q T v b dq bv ibp pp c s1 [] _ (rFuel v bv) (inBucketRoot bv) 0 0 pht hok.1
    hpht hrt hrh (by simp [rPreF]) hm hhd $$ [Hk Hb Hc Hs Hcap]
    as ⟨%stk2, %els2, %s2, Hk, Hb, Hc, Hs, Hcap, %Hpos2⟩
  · iframe
  obtain ⟨hpos2, e, pidL, pgL, idx, hlast, hlf, hidx0, hlwf, h16L⟩ := Hpos2
  have hsp2 : els2.dropLast ++ [e] = els2 := by
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast; simp
  rw [← hsp2] at hpos2 ⊢
  ihave %Hsl2 := ownSlice_len _ _ _ $$ Hs
  have hidx2 : sint.Z (stk2.len - W64 1) = (els2.dropLast.length : Int) := by
    have h1 := Hsl2.1; have h2 := Hsl2.2
    rw [show sint.nat stk2.len = (sint.Z stk2.len).toNat from rfl] at h1
    simp only [List.length_append, List.length_singleton] at h1; word
  try wp_auto
  have hb2 : 0 ≤ sint.Z (stk2.len - W64 1) ∧ sint.Z (stk2.len - W64 1) < sint.Z stk2.len := by
    rw [hidx2]; have h1 := Hsl2.1; have h2 := Hsl2.2
    rw [show sint.nat stk2.len = (sint.Z stk2.len).toNat from rfl] at h1
    simp only [List.length_append, List.length_singleton] at h1; omega
  rw [if_pos hb2]
  icases ownSlice_elem_acc (sint.Z (stk2.len - W64 1)) e _ _ (els2.dropLast ++ [e]) (by omega)
    (by rw [hidx2]; simp) $$ Hs with ⟨He, Hsback⟩
  rw [hidx2]
  wp_auto
  wp_method_call; wp_call
  wp_auto
  rw [hlf.2.1]
  wp_auto
  icases rd_hdr_acc K tx src q T v b dq bv ibp pp pidL e.page' pgL hlf.1 h16L $$ [Hk Hb]
    with ⟨%dqh2, Hh, Hhb⟩
  · iframe
  obtain ⟨hd2, hH2⟩ : ∃ hd, pageHdr pgL = hd := ⟨_, rfl⟩
  have hcz2 : uint.Z hd2.count' = (pageCount pgL : Int) := by unfold pageCount; rw [hH2]
  have hcL := pageCount_lt pgL
  rw [hH2]
  wp_apply hCnt e.page' hd2 dqh2 $$ [Hh] as Hh
  · iexact Hh
  ihave Hkb := Hhb $$ Hh
  icases Hkb with ⟨Hk, Hb⟩
  ihave Hs := Hsback $$ He
  rw [show (els2.dropLast ++ [e]).set (↑els2.dropLast.length : Int).toNat e =
    els2.dropLast ++ [e] by simp]
  have hsl := rPosAt_last _ _ _ hpos2 e pidL pgL idx (by simp) hlf
  have hix : sint.Z e.index' = (idx : Int) := by
    rw [hlf.2.2.2.2]; have := hlf.2.2.2.1; word
  by_cases hc0 : pageCount pgL = 0
  · have : W64 (uint.Z hd2.count') = W64 0 := by rw [hcz2, hc0]; rfl
    rw [this]
    wp_auto
    rw [hc0] at hsl; simp at hsl; rw [hsl] at hpos2
    have hoff2 : rOffEnt v bv pp (els2.dropLast ++ [e]) :=
      ⟨e, pidL, pgL, idx, by simp, hlf, by omega, hlwf, h16L⟩
    wp_apply hnx K tx src q T v b dq bv ibp pp c stk2 (els2.dropLast ++ [e]) 0 0 hok hpos2
      $$ [Hk Hb Hc Hs Hcap] as %k0 %vl0 %fl0 ⟨%stk3, %els3, Hk, Hb, Hc, Hs, Hcap, Hcur, %Hoff, -⟩
    · iframe
    try wp_auto
    unfold rCurKV
    icases Hcur with (⟨%pg3, %idx3, ⟨%hpos3, %hland3, -⟩, -⟩ | %Hnil)
    · obtain ⟨e3, pid3, pgx, idxx, hl3, hlf3, -, hlwf3, h163⟩ := hland3
      have hsp3 : els3.dropLast ++ [e3] = els3 := by
        obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl3; simp
      rw [← hsp3] at hpos3 ⊢
      have hsl3 := rPosAt_last _ _ _ hpos3 e3 pid3 pgx idxx (by simp) hlf3
      have hil3 : idxx < pageCount pgx := by
        by_cases h : idxx < pageCount pgx
        · exact h
        · rw [if_neg h] at hsl3; omega
      have hent3' := rPosAt_ent' _ _ _ hpos3 (by omega) e3 pid3 pgx idxx (by simp) hlf3
      have hix3 : sint.Z e3.index' = (idxx : Int) := by
        rw [hlf3.2.2.2.2]; have := hlf3.2.2.2.1; have := pageCount_lt pgx; word
      wp_apply hkv K tx src q T v b dq bv ibp pp c stk3 els3.dropLast e3 pid3 pgx hlf3.1 hlf3.2.1
        hlf3.2.2.1 hlwf3 h163 (by omega) $$ [Hk Hb Hc Hs] as %k %vl %fl ⟨Hk, Hb, Hc, Hs, Hkv⟩
      · iframe
      try wp_auto
      by_cases hfb : fl &&& W32 1 = W32 0
      · rw [decide_eq_true hfb]
        simp only [Bool.not_true]
        wp_auto
        iapply HΦ
        unfold rBktP
        iexists stk3, (els3.dropLast ++ [e3]), vl
        iframe
        isplitl
        · ileft; iexists pgx, idxx; rw [hix3, Int.toNat_natCast]; iframe
          ipureintro; exact ⟨hpos3, ⟨e3, pid3, pgx, idxx, by simp, hlf3, Or.inr hil3, hlwf3, h163⟩, hent3'⟩
        · ipureintro; intro _; rfl
      · rw [decide_eq_false hfb]
        simp only [Bool.not_false]
        wp_auto
        iapply HΦ
        unfold rBktP
        iexists stk3, (els3.dropLast ++ [e3]), vl
        iframe
        isplitl
        · ileft; iexists pgx, idxx; rw [hix3, Int.toNat_natCast]; iframe
          ipureintro; exact ⟨hpos3, ⟨e3, pid3, pgx, idxx, by simp, hlf3, Or.inr hil3, hlwf3, h163⟩, hent3'⟩
        · ipureintro; intro h; exact absurd h hfb
    · rcases Hoff hoff2 with ⟨e3, pid3, pgx, idxx, hl3, hlf3, hge, hlwf3, h163⟩ | h
      · have hsp3 : els3.dropLast ++ [e3] = els3 := by
          obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl3; simp
        rw [← hsp3]
        have hix3 : sint.Z e3.index' = (idxx : Int) := by
          rw [hlf3.2.2.2.2]; have := hlf3.2.2.2.1; have := pageCount_lt pgx; word
        wp_apply hkv K tx src q T v b dq bv ibp pp c stk3 els3.dropLast e3 pid3 pgx hlf3.1 hlf3.2.1
          hlf3.2.2.1 hlwf3 h163 (by omega) $$ [Hk Hb Hc Hs] as %k %vl %fl ⟨Hk, Hb, Hc, Hs, Hkv⟩
        · iframe
        unfold rKV
        rw [hix3, Int.toNat_natCast, if_neg (show ¬ idxx < pageCount pgx by omega)]
        icases Hkv with %Hk0
        obtain ⟨rfl, rfl, rfl⟩ := Hk0
        try wp_auto
        try wp_auto
        iapply HΦ
        unfold rBktP
        iexists stk3, els3.dropLast ++ [e3], slice.nil
        iframe
        isplitl
        · iright; ipureintro; exact ⟨Hnil.1, rfl, rfl, rfl, by rw [hsp3]; exact Hnil.2.2.2.2⟩
        · ipureintro; intro _; rfl
      · omega
  · have hne0 : W64 (uint.Z hd2.count') ≠ W64 0 := by
      rw [hcz2]; intro h; apply hc0; have := congrArg BitVec.toNat h; simp at this; omega
    rw [decide_eq_false hne0]
    wp_auto
    have hil : idx < pageCount pgL := by omega
    rw [if_pos hil] at hsl
    rw [hsl] at hpos2
    have hent := rPosAt_ent' _ _ _ hpos2 (by omega) e pidL pgL idx (by simp) hlf
    wp_apply hkv K tx src q T v b dq bv ibp pp c stk2 els2.dropLast e pidL pgL hlf.1 hlf.2.1
      hlf.2.2.1 hlwf h16L (by omega) $$ [Hk Hb Hc Hs] as %k %vl %fl ⟨Hk, Hb, Hc, Hs, Hkv⟩
    · iframe
    try wp_auto
    by_cases hfb : fl &&& W32 1 = W32 0
    · rw [decide_eq_true hfb]
      simp only [Bool.not_true]
      wp_auto
      iapply HΦ
      unfold rBktP
      iexists stk2, (els2.dropLast ++ [e]), vl
      iframe
      isplitl
      · unfold rCurKV; ileft; iexists pgL, idx; rw [hix, Int.toNat_natCast]; iframe
        ipureintro; exact ⟨hpos2, ⟨e, pidL, pgL, idx, by simp, hlf, Or.inr hil, hlwf, h16L⟩, hent⟩
      · ipureintro; intro _; rfl
    · rw [decide_eq_false hfb]
      simp only [Bool.not_false]
      wp_auto
      iapply HΦ
      unfold rBktP
      iexists stk2, (els2.dropLast ++ [e]), vl
      iframe
      isplitl
      · unfold rCurKV; ileft; iexists pgL, idx; rw [hix, Int.toNat_natCast]; iframe
        ipureintro; exact ⟨hpos2, ⟨e, pidL, pgL, idx, by simp, hlf, Or.inr hil, hlwf, h16L⟩, hent⟩
      · ipureintro; intro h; exact absurd h hfb

end proof

end bbolt
end EtcdGrove
end Perennial
