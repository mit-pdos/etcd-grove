/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__next_r0.lean` (U6i, `notes/bbolt-proof-plan.md`): the
up-loop runs over no element (the empty stack) or over the empty root leaf, whose index (`0` or
`-1`) is not below its count less one (`-1`); then `i == -1`: nil, nil, `0`, the stack unchanged.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__next_r0
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

theorem Cursor.next_r0.wp_proof
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG)) :
    Cursor.next_r0.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v b dq bv ibp pp c stk els hok hel
  wp_start as ⟨Hk, Hb, Hc, Hs, Hcap⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  have hlen : els.length ≤ 1 := by
    rcases hel with rfl | ⟨-, e, pg, rfl, -⟩ <;> simp
  have hsl' : sint.Z stk.len = (els.length : Int) := by
    have h1 := Hsl.1; have h2 := Hsl.2
    rw [show sint.nat stk.len = (sint.Z stk.len).toNat from rfl] at h1; omega
  wp_auto
  ihave IH : ("Hk" ∷ rdTxK K tx src q T v ∗ "Hb" ∷ rBktP v tx b dq bv ibp pp ∗
      "Hcc" ∷ c ↦ Cursor.mk b stk ∗ "Hs" ∷ stk ↦* els ∗
      "Hcap" ∷ ownSliceCap elemRef stk (DFrac.own 1) : IProp GF) $$ [Hk Hb Hc Hs Hcap]
  · simp only [named]
    iframe
  wp_for IH
  ihave IH2 : (∃ (kk : Nat), "i" ∷ i_ptr ↦ W64 ((kk : Int) - 1) ∗ "Hs" ∷ stk ↦* els ∗
      "Hk" ∷ rdTxK K tx src q T v ∗ "Hb" ∷ rBktP v tx b dq bv ibp pp ∗
      "%Hu" ∷ ⌜kk ≤ els.length⌝ : IProp GF) $$ [i Hs Hk Hb]
  · iexists els.length
    simp only [named]
    iframe
    isplitl
    · iExactEq i; congr 1; word
    · ipureintro; exact Nat.le_refl _
  wp_for IH2
  wp_if_destruct
  · -- the up-loop's body: the empty root leaf
    have hkz : sint.Z (W64 ((kk : Int) - 1)) = (kk : Int) - 1 := by word
    have hk1 : 1 ≤ kk := by rw [hkz] at Hif; simp at Hif; omega
    obtain ⟨-, e, pg, rfl, hpa, hnode, hfl, hc0, hix⟩ : rEmptyAt v bv pp els := by
      rcases hel with rfl | h
      · simp at Hu; omega
      · exact h
    have hk : kk = 1 := by simp at Hu; omega
    subst hk
    rw [if_pos ⟨by rw [hkz]; omega, by rw [hkz, hsl']; simp⟩]
    have hget : [e][(sint.Z (W64 (((1 : Nat) : Int) - 1))).toNat]? = some e := by
      rw [hkz]; simp
    icases ownSlice_elem_acc (sint.Z (W64 (((1 : Nat) : Int) - 1))) e _ _ [e] (by rw [hkz]; simp)
      hget $$ Hs with ⟨He, Hsback⟩
    obtain ⟨l2, pg2, hpa2, h16, -⟩ := rTree_page v bv pp _ hok.2.1
    have hpg2 := rPageAt_same hpa2 hpa
    subst hpg2
    wp_auto
    wp_method_call; wp_call
    wp_auto
    rw [hnode]
    wp_auto
    icases rd_hdr_acc K tx src q T v b dq bv ibp pp _ e.page' pg2 hpa h16 $$ [Hk Hb]
      with ⟨%dqh, Hh, Hhb⟩
    · iframe
    obtain ⟨hd, hH⟩ : ∃ hd, pageHdr pg2 = hd := ⟨_, rfl⟩
    have hcz : uint.Z hd.count' = (pageCount pg2 : Int) := by unfold pageCount; rw [hH]
    rw [hH]
    wp_apply hCnt e.page' hd dqh $$ [Hh] as Hh
    · iexact Hh
    ihave Hkb := Hhb $$ Hh
    icases Hkb with ⟨Hk, Hb⟩
    have hcm : sint.Z (W64 (uint.Z hd.count') - W64 1) = -1 := by
      rw [hcz, hc0]; rfl
    try wp_auto
    rw [hcm]
    have hlt : ¬ sint.Z e.index' < -1 := by
      rcases hix with h | h <;> rw [h] <;> decide
    rw [decide_eq_false hlt]
    wp_auto
    ihave Hs := Hsback $$ He
    rw [show [e].set (sint.Z (W64 (((1 : Nat) : Int) - 1))).toNat e = [e] by rw [hkz]; simp]
    wp_for_post
    iframe
    iexists 0
    simp only [named]
    iframe
    ipureintro; omega
  · have hk0 : kk = 0 := by
      rcases Nat.eq_zero_or_pos kk with h | h
      · exact h
      · have hkz : sint.Z (W64 ((kk : Int) - 1)) = (kk : Int) - 1 := by word
        rw [hkz] at Hif; simp at Hif; omega
    subst hk0
    rw [decide_eq_true (by rfl)]
    wp_auto
    wp_for_post
    iapply HΦ
    iframe

end proof

end bbolt
end EtcdGrove
end Perennial
