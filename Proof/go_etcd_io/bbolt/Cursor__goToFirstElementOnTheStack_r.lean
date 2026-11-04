/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__goToFirstElementOnTheStack_r.lean` (U6,
`notes/bbolt-proof-plan.md`): the loop pushes the first child of a branch top (`rHdF_down`) until
the top is a leaf (`rHdF_leaf`).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__goToFirstElementOnTheStack_r
public import Spec.go_etcd_io.bbolt.Bucket__pageNode_r
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElement
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Pgid

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

theorem Cursor.goToFirstElementOnTheStack_r.wp_proof
    (hpn : Bucket.pageNode_r.spec (GF := GF) (hG := hG))
    (hIL : internal.common.Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG)) :
    Cursor.goToFirstElementOnTheStack_r.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v b dq bv ibp pp c stk pre e m pid o t pht hbv hht htree hh hpre hm hhd
  wp_start as ⟨Hk, Hb, Hc, Hs, Hcap⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  ihave IH : (∃ (stk1 : GoSlice) (pre1 : List elemRef) (e1 : elemRef) (m1 pid1 o1 t1 : Nat),
      "Hk" ∷ rdTxK K tx src q T v ∗ "Hb" ∷ rBktP v tx b dq bv ibp pp ∗
      "Hc" ∷ c_ptr ↦ c ∗ "Hcc" ∷ c ↦ Cursor.mk b stk1 ∗ "Hs" ∷ stk1 ↦* (pre1 ++ [e1]) ∗
      "Hcap" ∷ ownSliceCap elemRef stk1 (DFrac.own 1) ∗
      "%Hinv" ∷ ⌜rPreF v bv pp (rFuel v bv) (inBucketRoot bv) pre1 m1 pid1 o1 ∧ 0 < m1 ∧
        rHdF v bv pp m1 pid1 e1 t1 ∧ o1 + t1 = o + t ∧ rTree v bv pid1 ∧
        (inBucketRoot bv = 0 ∨ pht pid1 < m1)⌝ : IProp GF) $$ [Hk Hb c Hc Hs Hcap]
  · iexists stk, pre, e, m, pid, o, t
    simp only [named]
    iframe
    ipureintro; refine ⟨hpre, hm, hhd, ?_, htree, hh⟩; first | rfl | trivial
  wp_for IH
  obtain ⟨hp1, hm1, hhd1, ht1, htr1, hh1⟩ := Hinv
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  have hidx : sint.Z (stk1.len - W64 1) = (pre1.length : Int) := by
    simp only [List.length_append, List.length_singleton] at Hsl; word
  rw [if_pos (by rw [hidx]; word)]
  icases ownSlice_elem_acc (sint.Z (stk1.len - W64 1)) e1 _ _ (pre1 ++ [e1]) (by omega)
    (by rw [hidx]; simp) $$ Hs with ⟨He, Hsback⟩
  rw [hidx]
  wp_auto
  obtain ⟨l, pg, hpa, h16, hpg⟩ := rTree_page v bv pp pid1 htr1
  have hnode : e1.node' = null := by
    rcases hhd1 with ⟨_, _, hbr, _⟩ | ⟨_, hlf⟩
    · exact hbr.2.2.1
    · exact hlf.2.1
  have hl : l = e1.page' := by
    rcases hhd1 with ⟨pg', _, hbr, _⟩ | ⟨pg', hlf⟩
    · have := hbr.2.1; rw [hpa] at this; exact congrArg Prod.fst (Option.some.inj this)
    · have := hlf.1; rw [hpa] at this; exact congrArg Prod.fst (Option.some.inj this)
  subst hl
  wp_method_call; wp_call
  wp_auto
  rw [hnode]
  wp_auto
  icases rd_hdr_acc K tx src q T v b dq bv ibp pp pid1 e1.page' pg hpa h16 $$ [Hk Hb]
    with ⟨%dqh, Hh, Hhb⟩
  · iframe
  obtain ⟨hd, hH⟩ : ∃ hd, pageHdr pg = hd := ⟨_, rfl⟩
  have hfz : pageFlags pg = hd.flags'.toNat := by unfold pageFlags; rw [hH]
  rw [hH]
  wp_apply hIL e1.page' hd dqh $$ [Hh] as Hh
  · iexact Hh
  ihave Hkb := Hhb $$ Hh
  icases Hkb with ⟨Hk, Hb⟩
  rcases hhd1 with ⟨pg', j, hbr, htj⟩ | ⟨pg', hlf⟩
  · -- a branch: push its child `j`
    have hpg := rPageAt_same hbr.2.1 hpa
    subst hpg
    have hf1 : hd.flags' = W16 1 := by
      apply BitVec.eq_of_toNat_eq; rw [← hfz, hbr.2.2.2.1]; rfl
    rw [hf1]
    wp_auto
    rw [hnode]
    wp_auto
    ihave Hs := Hsback $$ He
    rw [show (pre1 ++ [e1]).set (↑pre1.length : Int).toNat e1 = pre1 ++ [e1] by simp]
    rcases hpg with ⟨hl, -⟩ | ⟨-, hi, hpgv, hwm, hbwf, hch⟩
    · rw [hbr.2.2.2.1] at hl; simp [branchPageFlag, leafPageFlag] at hl
    obtain ⟨hc0, -, hcnt, helems, -⟩ := hbwf
    have hjc := hbr.2.2.2.2.1
    have hcnt16 := pageCount_lt pg'
    rw [hbr.2.2.2.2.2]
    icases rd_page_bounds K tx src q T v b dq bv ibp pp pid1 e1.page' pg' hpa
      (by intro e; simp [e] at h16) $$ [Hk Hb] with ⟨⟨Hk, Hb⟩, %Hlb⟩
    · iframe
    have hu : uint.Z (W16 (sint.Z (W64 (j : Int)))) = (j : Int) := by word
    wp_apply hBE e1.page' (W16 (sint.Z (W64 (j : Int)))) Hlb.1
      (by rw [hu]; unfold elemOff at hcnt; omega)
    rw [hu]
    have hoff : (16 + 16 * (j : Int)) = ((elemOff j : Nat) : Int) := by
      unfold elemOff; push_cast; rfl
    rw [hoff]
    icases rd_elem_acc (V := branchPageElement) K tx src q T v b dq bv ibp pp pid1 e1.page' pg' hpa j
      (by unfold elemOff at hcnt ⊢; omega) $$ [Hk Hb] with ⟨%dqe, Hel, Helb⟩
    · iframe
    rw [show (decode (bytesAt pg' (elemOff j) 16) : branchPageElement) = branchElem pg' j from rfl]
    obtain ⟨be, hbe⟩ : ∃ be, branchElem pg' j = be := ⟨_, rfl⟩
    rw [hbe]
    wp_apply hBP (e1.page' +ₗ ((elemOff j : Nat) : Int)) be dqe $$ [Hel] as Hel
    · iexact Hel
    ihave Hkb := Helb $$ Hel
    icases Hkb with ⟨Hk, Hb⟩
    have hchild : be.pgid'.toNat = branchPgid pg' j := by unfold branchPgid; rw [hbe]
    have htc := hch j hjc
    obtain ⟨lc, pgc, hpac, h16c, hpgc⟩ := rTree_page v bv pp (branchPgid pg' j) htc
    try wp_auto
    wp_apply hpn K tx src q T v b dq bv ibp pp be.pgid' lc pgc hbv (by rw [hchild]; exact hpac)
      $$ [Hk Hb] as ⟨Hk, Hb⟩
    · iframe
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s1 ⟨Hs, Hcap, -⟩
    try wp_auto
    wp_for_post
    iframe
    have hfc : pageFlags pgc = branchPageFlag ∨ pageFlags pgc = leafPageFlag := by
      rcases hpgc with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
    have hc0c : pageFlags pgc = branchPageFlag → 0 < pageCount pgc := by
      intro hb
      rcases hpgc with ⟨h, -⟩ | ⟨-, -, -, hwm2, hbw, -⟩
      · rw [hb] at h; simp [branchPageFlag, leafPageFlag] at h
      · exact hbw.1
    have hht' := (hht pid1 pg' hpgv).2 hbr.2.2.2.1 j hjc
    have hpm : pht pid1 < m1 := by rcases hh1 with h | h; exact absurd h hi; exact h
    obtain ⟨hp2, hhd2⟩ := rHdF_down pre1 (inBucketRoot bv) m1 pid1 o1 t1 e1
      { page' := lc, node' := null, index' := W64 0 } pgc hp1 pg' j hbr htj hm1 hpac rfl rfl hfc hc0c
    iexists s1, pre1 ++ [e1], { page' := lc, node' := null, index' := W64 0 }, m1 - 1,
      branchPgid pg' j, o1 + t1, 0
    simp only [named]
    iframe
    ipureintro
    exact ⟨hp2, by omega, hhd2, by omega, htc, Or.inr (by omega)⟩
  · -- a leaf: done
    have hpg := rPageAt_same hlf.1 hpa
    subst hpg
    have hf2 : hd.flags' = W16 2 := by
      apply BitVec.eq_of_toNat_eq; rw [← hfz, hlf.2.2.1]; rfl
    rw [hf2]
    wp_auto
    wp_for_post
    ihave Hs := Hsback $$ He
    rw [show (pre1 ++ [e1]).set (↑pre1.length : Int).toNat e1 = pre1 ++ [e1] by simp]
    iapply HΦ
    iexists stk1, pre1 ++ [e1], _
    iframe
    ipureintro
    rw [← ht1]
    exact rHdF_leaf pre1 m1 pid1 o1 t1 e1 pg' hp1 hm1 hlf

end proof

end bbolt
end EtcdGrove
end Perennial
