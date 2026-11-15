/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__last_r.lean` (U6h, `notes/bbolt-proof-plan.md`): the
descent by last children (`rTlF_down`; each child not empty by the reader's B+tree keys,
`rKeys_child_pg`, so its last index `count - 1` is an entry), as `goToFirstElementOnTheStack`'s by
first children; a leaf on top ends it.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__last_r
public import Spec.go_etcd_io.bbolt.Bucket__pageNode_r
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElement
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count

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

theorem Cursor.last_r.wp_proof
    (hpn : Bucket.pageNode_r.spec (GF := GF) (hG := hG))
    (hIL : internal.common.Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG)) :
    Cursor.last_r.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v b dq bv ibp pp c stk pre e m pid o s hok hpre hm hcase
  wp_start as ⟨Hk, Hb, Hc, Hs, Hcap⟩
  icases (persistent_entails_left (rdTxK_view K tx src q T v)) $$ Hk with ⟨Hk, %Hvw⟩
  obtain ⟨-, C, hokC, hvC⟩ := Hvw
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  obtain ⟨-, -, -, pht, hht⟩ := hokC.1
  rw [← hpv] at hht
  obtain ⟨hrt, hrh⟩ := rRoot_ok pht hht hok
  obtain ⟨htree, hh⟩ := rPreF_tree pht hht _ _ _ _ _ _ hpre hrt hrh
  have hkeys := rPreF_keys _ _ _ _ _ _ hpre (rKeys_root hok)
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  ihave IH : (∃ (stk1 : GoSlice) (pre1 : List elemRef) (e1 : elemRef) (m1 pid1 o1 s1 : Nat),
      "Hk" ∷ rdTxK K tx src q T v ∗ "Hb" ∷ rBktP v tx b dq bv ibp pp ∗
      "Hc" ∷ c_ptr ↦ c ∗ "Hcc" ∷ c ↦ Cursor.mk b stk1 ∗ "Hs" ∷ stk1 ↦* (pre1 ++ [e1]) ∗
      "Hcap" ∷ ownSliceCap elemRef stk1 (DFrac.own 1) ∗
      "%Hinv" ∷ ⌜rPreF v bv pp (rFuel v bv) (inBucketRoot bv) pre1 m1 pid1 o1 ∧ 0 < m1 ∧
        rTree v bv pid1 ∧ (inBucketRoot bv = 0 ∨ pht pid1 < m1) ∧ rKeysAt v bv pid1 ∧
        (rTlF v bv pp m1 pid1 e1 s1 ∨ rLfTop v bv pp pid1 e1) ∧
        (rLfTop v bv pp pid e → pre1 = pre ∧ e1 = e) ∧
        (rTlF v bv pp m pid e s → rTlF v bv pp m1 pid1 e1 s1 ∧ o1 + s1 = o + s)⌝ : IProp GF)
      $$ [Hk Hb c Hc Hs Hcap]
  · iexists stk, pre, e, m, pid, o, s
    simp only [named]
    iframe
    ipureintro
    refine ⟨hpre, hm, htree, hh, hkeys, hcase, ?_, ?_⟩ <;> simp
  wp_for IH
  obtain ⟨hp1, hm1, htr1, hh1, hk1, hc1, hlt1, htl1⟩ := Hinv
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
    rcases hc1 with (⟨_, _, hbr, _⟩ | ⟨_, _, hlf, _⟩) | ⟨_, _, hn, _⟩
    · exact hbr.2.2.1
    · exact hlf.2.1
    · exact hn
  have hl : l = e1.page' := by
    rcases hc1 with (⟨pg', _, hbr, _⟩ | ⟨pg', _, hlf, _⟩) | ⟨pg', hpa', _, _⟩
    · have := hbr.2.1; rw [hpa] at this; exact congrArg Prod.fst (Option.some.inj this)
    · have := hlf.1; rw [hpa] at this; exact congrArg Prod.fst (Option.some.inj this)
    · rw [hpa] at hpa'; exact congrArg Prod.fst (Option.some.inj hpa')
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
  by_cases hbf : pageFlags pg = branchPageFlag
  · -- a branch: push its child `j`, at its last index
    obtain ⟨pg', j, hbr, hsj⟩ : ∃ pg' j, rBrAt v bv pp pid1 e1 pg' j ∧
        s1 = entsBefore v.pages (m1 - 1) pg' (j + 1) := by
      rcases hc1 with (⟨pg', j, hbr, hsj⟩ | ⟨pg', i, hlf, -⟩) | ⟨pg', hpa', -, hfl⟩
      · exact ⟨pg', j, hbr, hsj⟩
      · have := rPageAt_same hlf.1 hpa; subst this
        rw [hlf.2.2.1] at hbf; simp [branchPageFlag, leafPageFlag] at hbf
      · have := rPageAt_same hpa' hpa; subst this
        rw [hfl] at hbf; simp [branchPageFlag, leafPageFlag] at hbf
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
    wp_apply hpn K tx src q T v b dq bv ibp pp be.pgid' lc pgc hok.1 (by rw [hchild]; exact hpac)
      $$ [Hk Hb] as ⟨Hk, Hb⟩
    · iframe
    try wp_auto
    -- `nextRef.count()`: the child's page count
    wp_method_call; wp_call
    wp_auto
    icases rd_hdr_acc K tx src q T v b dq bv ibp pp (branchPgid pg' j) lc pgc hpac h16c $$ [Hk Hb]
      with ⟨%dqh2, Hh, Hhb⟩
    · iframe
    obtain ⟨hd2, hH2⟩ : ∃ hd, pageHdr pgc = hd := ⟨_, rfl⟩
    have hcz2 : uint.Z hd2.count' = (pageCount pgc : Int) := by unfold pageCount; rw [hH2]
    rw [hH2]
    wp_apply hCnt lc hd2 dqh2 $$ [Hh] as Hh
    · iexact Hh
    ihave Hkb := Hhb $$ Hh
    icases Hkb with ⟨Hk, Hb⟩
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s1' ⟨Hs, Hcap, -⟩
    try wp_auto
    wp_for_post
    iframe
    have hfc : pageFlags pgc = branchPageFlag ∨ pageFlags pgc = leafPageFlag := by
      rcases hpgc with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
    have hcc : 0 < pageCount pgc := rKeys_child_pg hk1 hbr hpac
    have hht' := (hht pid1 pg' hpgv).2 hbr.2.2.2.1 j hjc
    have hpm : pht pid1 < m1 := by rcases hh1 with h | h; exact absurd h hi; exact h
    have hm1' : 1 < m1 := by omega
    have hci : W64 (uint.Z hd2.count') - W64 1 = W64 ((pageCount pgc : Int) - 1) := by
      rw [hcz2]; word
    rw [hci]
    obtain ⟨hp2, s2, htl2, hs2⟩ := rTlF_down pre1 m1 pid1 o1 s1 e1
      { page' := lc, node' := null, index' := W64 ((pageCount pgc : Int) - 1) } pg' pgc j hp1 hm1'
      hbr hsj hpac rfl hcc rfl hfc
    iexists s1', pre1 ++ [e1], { page' := lc, node' := null, index' := W64 ((pageCount pgc : Int) - 1) },
      m1 - 1, branchPgid pg' j, o1 + entsBefore v.pages (m1 - 1) pg' j, s2
    simp only [named]
    iframe
    ipureintro
    refine ⟨hp2, by omega, htc, Or.inr (by omega), (rKeys_child hk1 hbr).1, Or.inl htl2, ?_, ?_⟩
    · intro hlt
      obtain ⟨rfl, rfl⟩ := hlt1 hlt
      obtain ⟨hm2, hpid2, -⟩ := rPreF_det _ _ _ _ _ _ _ _ _ hpre hp1
      subst hm2 hpid2
      obtain ⟨pg3, hpa3, -, hfl3⟩ := hlt
      have := rPageAt_same hpa3 hpa; subst this
      rw [hfl3] at hbf; simp [branchPageFlag, leafPageFlag] at hbf
    · intro htl
      obtain ⟨-, ho⟩ := htl1 htl
      exact ⟨htl2, by omega⟩
  · -- a leaf: done
    have hlfl : pageFlags pg = leafPageFlag := by
      rcases hpg with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hbf
    have hf2 : hd.flags' = W16 2 := by
      apply BitVec.eq_of_toNat_eq; rw [← hfz, hlfl]; rfl
    rw [hf2]
    wp_auto
    wp_for_post
    ihave Hs := Hsback $$ He
    rw [show (pre1 ++ [e1]).set (↑pre1.length : Int).toNat e1 = pre1 ++ [e1] by simp]
    iapply HΦ
    iexists stk1, pre1 ++ [e1]
    iframe
    ipureintro
    refine ⟨fun htl => ?_, fun hlt => by obtain ⟨rfl, rfl⟩ := hlt1 hlt; rfl⟩
    obtain ⟨htl', ho⟩ := htl1 htl
    rcases htl' with ⟨pg', j, hbr, -⟩ | ⟨pg', i, hlf, hi, hsi⟩
    · have := rPageAt_same hbr.2.1 hpa; subst this
      rw [hbr.2.2.2.1] at hlfl; simp [branchPageFlag, leafPageFlag] at hlfl
    have := rPageAt_same hlf.1 hpa; subst this
    have hlwf : leafWF pg' pg'.length := by
      rcases hpg with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hbf
    refine ⟨o1 + i, by omega, ?_, e1, pid1, pg', i, by simp, hlf, Or.inr hi, hlwf, h16⟩
    have := rTlF_leaf pre1 m1 pid1 o1 e1 pg' i hp1 hm1 hlf hi
    rw [show o + s = o1 + i + 1 by omega]; exact this

end proof

end bbolt
end EtcdGrove
end Perennial
