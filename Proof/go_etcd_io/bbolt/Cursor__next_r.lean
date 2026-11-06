/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__next_r.lean` (U6, `notes/bbolt-proof-plan.md`): the
up-loop over the stack's elements at their end (`rUpInv`), then nil past the last entry
(`rUpInv_none`), or the element found moved one further and the descent from it
(`rUpInv_found`, `goToFirstElementOnTheStack`); an empty leaf restarts the loop.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__next_r
public import Spec.go_etcd_io.bbolt.Cursor__goToFirstElementOnTheStack_r
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Proof.go_etcd_io.bbolt.Read.PubRPos

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

theorem take_set_succ {α : Type} (l : List α) (n : Nat) (x : α) (hn : n < l.length) :
    (l.set n x).take (n + 1) = l.take n ++ [x] := by
  rw [List.take_succ, List.take_set, List.set_eq_of_length_le (by simp; omega)]
  simp [hn]

theorem Cursor.next_r.wp_proof
    (hg : Cursor.goToFirstElementOnTheStack_r.spec (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue_r.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG)) :
    Cursor.next_r.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v b dq bv ibp pp c stk els i s hok hpos
  wp_start as ⟨Hk, Hb, Hc, Hs, Hcap⟩
  icases (persistent_entails_left (rdTxK_view K tx src q T v)) $$ Hk with ⟨Hk, %Hvw⟩
  obtain ⟨-, C, hokC, hvC⟩ := Hvw
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  obtain ⟨-, -, -, pht, hpht⟩ := hokC.1
  rw [← hpv] at hpht
  obtain ⟨hrt, hrh⟩ := rRoot_ok pht hpht hok
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  ihave IH : (∃ (stk1 : GoSlice) (els1 : List elemRef) (i1 : Nat),
      "Hk" ∷ rdTxK K tx src q T v ∗ "Hb" ∷ rBktP v tx b dq bv ibp pp ∗
      "Hcc" ∷ c ↦ Cursor.mk b stk1 ∗ "Hs" ∷ stk1 ↦* els1 ∗
      "Hcap" ∷ ownSliceCap elemRef stk1 (DFrac.own 1) ∗
      "%Hp" ∷ ⌜rPosAt v bv pp els1 i1 s⌝ ∗
      "%Hoff" ∷ ⌜rOffEnt v bv pp els → rOffEnt v bv pp els1⌝ ∗
      "%Hsame" ∷ ⌜els1 = els⌝ : IProp GF) $$ [Hk Hb Hc Hs Hcap]
  · iexists stk, els, i
    simp only [named]
    iframe
    ipureintro; exact ⟨hpos, id, trivial⟩
  wp_for IH
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave IH2 : (∃ (kk : Nat), "i" ∷ i_ptr ↦ W64 ((kk : Int) - 1) ∗ "Hs" ∷ stk1 ↦* els1 ∗
      "Hk" ∷ rdTxK K tx src q T v ∗ "Hb" ∷ rBktP v tx b dq bv ibp pp ∗
      "%Hu" ∷ ⌜kk ≤ els1.length ∧ rUpInv v bv pp els1 s kk⌝ : IProp GF) $$ [i Hs Hk Hb]
  · iexists els1.length
    simp only [named]
    iframe
    isplitl
    · iExactEq i; congr 1; word
    · ipureintro; exact ⟨Nat.le_refl _, rUpInv_start els1 s⟩
  wp_for IH2
  wp_if_destruct
  · -- the up-loop's body at element `kk - 1`
    have hlen : els1.length < 2 ^ 63 := by
      have h1 := Hsl.1; rw [show sint.nat stk1.len = (sint.Z stk1.len).toNat from rfl] at h1; word
    have hkz : sint.Z (W64 ((kk : Int) - 1)) = (kk : Int) - 1 := by have := Hu.1; word
    have hk1 : 1 ≤ kk := by rw [hkz] at Hif; simp at Hif; omega
    have hkl : kk - 1 < els1.length := by omega
    have hsl' : sint.Z stk1.len = (els1.length : Int) := by
      have h1 := Hsl.1; have h2 := Hsl.2
      rw [show sint.nat stk1.len = (sint.Z stk1.len).toNat from rfl] at h1; omega
    rw [if_pos ⟨by rw [hkz]; omega, by rw [hkz, hsl']; omega⟩]
    have hget : els1[(sint.Z (W64 ((kk : Int) - 1))).toNat]? = some els1[kk - 1] := by
      rw [hkz, show ((kk : Int) - 1).toNat = kk - 1 by omega]; simp
    icases ownSlice_elem_acc (sint.Z (W64 ((kk : Int) - 1))) els1[kk - 1] _ _ els1 (by omega)
      hget $$ Hs with ⟨He, Hsback⟩
    -- the element's page
    have hsplit : els1 = els1.take (kk - 1) ++ els1[kk - 1] :: els1.drop (kk - 1 + 1) := by simp
    have hp1 := Hp
    unfold rPosAt at hp1
    rw [hsplit] at hp1
    obtain ⟨m, pid', o, i', s', pg, hpre, hr, -, -, hpa, hnode⟩ := rPosF_top _ _ _ _ _ _ _ hp1
    obtain ⟨htp, -⟩ := rPreF_tree pht hpht _ _ _ _ _ _ hpre hrt hrh
    obtain ⟨l2, pg2, hpa2, h16, -⟩ := rTree_page v bv pp pid' htp
    have hpg2 := rPageAt_same hpa2 hpa
    have hl2 : l2 = els1[kk - 1].page' := by
      rw [hpa2] at hpa; exact congrArg Prod.fst (Option.some.inj hpa)
    subst hpg2 hl2
    wp_auto
    wp_method_call; wp_call
    wp_auto
    rw [hnode]
    wp_auto
    icases rd_hdr_acc K tx src q T v b dq bv ibp pp pid' els1[kk - 1].page' pg2 hpa h16 $$ [Hk Hb]
      with ⟨%dqh, Hh, Hhb⟩
    · iframe
    obtain ⟨hd, hH⟩ : ∃ hd, pageHdr pg2 = hd := ⟨_, rfl⟩
    have hcz : uint.Z hd.count' = (pageCount pg2 : Int) := by unfold pageCount; rw [hH]
    have hcnt16 := pageCount_lt pg2
    rw [hH]
    wp_apply hCnt els1[kk - 1].page' hd dqh $$ [Hh] as Hh
    · iexact Hh
    ihave Hkb := Hhb $$ Hh
    icases Hkb with ⟨Hk, Hb⟩
    have hcm : sint.Z (W64 (uint.Z hd.count') - W64 1) = (pageCount pg2 : Int) - 1 := by
      rw [hcz]; word
    try wp_auto
    rw [hcm]
    by_cases hlt : sint.Z els1[kk - 1].index' < (pageCount pg2 : Int) - 1
    · rw [decide_eq_true hlt]
      wp_auto
      ihave Hs := Hsback $$ He
      ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
      have hu1 : rUpInv v bv pp els1 s (kk - 1 + 1) := by rw [Nat.sub_add_cancel hk1]; exact Hu.2
      obtain ⟨m2, pid2, o2, t2, hpre2, hm2, -, hhd2, hs2⟩ :=
        rUpInv_found els1 i1 s (kk - 1) Hp hkl hu1 pid' pg2 hpa hlt
      obtain ⟨htp2, hh2⟩ := rPreF_tree pht hpht _ _ _ _ _ _ hpre2 hrt hrh
      wp_for_post
      have hne : W64 ((kk : Int) - 1) ≠ W64 (-1) := by
        intro h; have := congrArg sint.Z h; rw [hkz] at this; simp at this; omega
      rw [decide_eq_false hne]
      wp_auto
      have hkw : W64 ((kk : Int) - 1) + W64 1 = W64 (kk : Int) := by word
      have hkk : sint.Z (W64 (kk : Int)) = (kk : Int) := by word
      rw [hkw]
      rw [if_pos ⟨by decide, by rw [hkk]; simp, by rw [hkk]; word⟩]
      icases ownSlice_slice_with_cap (V := elemRef) (W64 0) (W64 (kk : Int)) stk1 _
        ⟨by decide, by rw [hkk]; simp, by rw [hkk, hsl']; omega⟩ $$ [Hs Hcap] with ⟨-, Hs, Hcap⟩
      · iframe
      have hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 (kk : Int)))
          (els1.set (sint.Z (W64 ((kk : Int) - 1))).toNat
            { page' := els1[kk - 1].page', node' := els1[kk - 1].node',
              index' := els1[kk - 1].index' + W64 1 }) =
          els1.take (kk - 1) ++ [{ els1[kk - 1] with index' := els1[kk - 1].index' + W64 1 }] := by
        rw [hkz, show ((kk : Int) - 1).toNat = kk - 1 by omega,
          show sint.nat (W64 (kk : Int)) = kk by unfold sint.nat; rw [show (W64 (kk : Int)).toInt = kk from hkk]; simp,
          show sint.nat (W64 0) = 0 from rfl]
        unfold subslice
        rw [List.drop_zero]
        have h := take_set_succ els1 (kk - 1)
          ⟨els1[kk - 1].page', els1[kk - 1].node', els1[kk - 1].index' + W64 1⟩ hkl
        rw [Nat.sub_add_cancel hk1] at h
        exact h
      rw [hsub]
      wp_auto
      wp_apply hg K tx src q T v b dq bv ibp pp c _ (els1.take (kk - 1)) _ m2 pid2 o2 t2 pht hok.1
        hpht htp2 hh2 hpre2 hm2 hhd2 $$ [Hk Hb Hcc Hs Hcap]
        as ⟨%stk2, %els2, %s2, Hk, Hb, Hcc, Hs, Hcap, %Hpos2⟩
      · iframe
      obtain ⟨hpos2, e, pidL, pgL, idx, hlast, hlf, hidx0, hlwf, h16L⟩ := Hpos2
      rw [← hs2] at hpos2
      have hsp2 : els2.dropLast ++ [e] = els2 := by
        obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast; simp
      rw [← hsp2] at hpos2 ⊢
      ihave %Hsl2 := ownSlice_len _ _ _ $$ Hs
      have hidx2 : sint.Z (stk2.len - W64 1) = (els2.dropLast.length : Int) := by
        have h1 := Hsl2.1; have h2 := Hsl2.2
        rw [show sint.nat stk2.len = (sint.Z stk2.len).toNat from rfl] at h1
        simp only [List.length_append, List.length_singleton] at h1; word
      rw [if_pos (by rw [hidx2]; word)]
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
      · -- unreachable (`rBktOK`): an empty leaf is the root alone, which holds no element to move
        exfalso
        obtain ⟨-, hroot⟩ := rPosAt_empty_top hok _ _ _ hpos2 e pidL pgL idx (by simp) hlf hc0
        obtain ⟨x, hx, hxl⟩ := rPosAt_root_leaf els1 i1 s Hp _ _ hroot hlf.2.2.1
        have hk0 : kk - 1 = 0 := by rw [hx] at hkl; simp at hkl; omega
        have hxe : els1[kk - 1] = x := by
          have h : els1[kk - 1]? = some x := by rw [hx, hk0]; rfl
          exact (List.getElem?_eq_some_iff.mp h).2
        rw [hxe] at hpa hlt
        have hpg := rPageAt_det v bv pp _ _ _ _ _ hpa hxl.1
        subst hpg
        have := hxl.2.2.2.1
        rw [hxl.2.2.2.2] at hlt
        rw [hc0] at hlt this
        have : i1 = 0 := by omega
        subst this
        simp at hlt
      · have hne0 : W64 (uint.Z hd2.count') ≠ W64 0 := by
          rw [hcz2]; intro h; apply hc0; have := congrArg BitVec.toNat h; simp at this; omega
        rw [decide_eq_false hne0]
        wp_auto
        have hil : idx < pageCount pgL := by omega
        rw [if_pos hil] at hsl
        rw [hsl] at hpos2
        wp_apply hkv K tx src q T v b dq bv ibp pp c stk2 els2.dropLast e pidL pgL hlf.1 hlf.2.1
          hlf.2.2.1 hlwf h16L (by omega) $$ [Hk Hb Hcc Hs] as %k %vl %fl ⟨Hk, Hb, Hcc, Hs, Hkv⟩
        · iframe
        wp_for_post
        iapply HΦ
        iexists stk2, els2.dropLast ++ [e]
        have hent := rPosAt_ent' _ _ _ hpos2 (by omega) e pidL pgL idx (by simp) hlf
        iframe
        isplitl
        · unfold rCurKV
          ileft
          iexists pgL, idx
          rw [hix, Int.toNat_natCast]
          iframe
          ipureintro
          exact ⟨hpos2, ⟨e, pidL, pgL, idx, by simp, hlf, Or.inr hil, hlwf, h16L⟩, hent⟩
        · ipureintro
          have hslt := (List.getElem?_eq_some_iff.mp hent).1
          exact ⟨fun _ => Or.inr hslt, fun h => absurd h (by omega)⟩
    · rw [decide_eq_false hlt]
      wp_auto
      ihave Hs := Hsback $$ He
      rw [show els1.set (sint.Z (W64 ((kk : Int) - 1))).toNat els1[kk - 1] = els1 by
        rw [hkz, show ((kk : Int) - 1).toNat = kk - 1 by omega]; simp]
      wp_for_post
      iframe
      iexists kk - 1
      simp only [named]
      iframe
      isplitl
      · iExactEq i; congr 1
        rw [show ((kk - 1 : Nat) : Int) = (kk : Int) - 1 by omega]; word
      · ipureintro
        refine ⟨by omega, rUpInv_step els1 i1 s (kk - 1) Hp hkl ?_ pid' pg2 hpa (by omega)⟩
        rw [Nat.sub_add_cancel hk1]; exact Hu.2
  · have hlen : els1.length < 2 ^ 63 := by
      have h1 := Hsl.1; rw [show sint.nat stk1.len = (sint.Z stk1.len).toNat from rfl] at h1; word
    have hk0 : kk = 0 := by
      rcases Nat.eq_zero_or_pos kk with h | h
      · exact h
      · have hkz : sint.Z (W64 ((kk : Int) - 1)) = (kk : Int) - 1 := by have := Hu.1; word
        rw [hkz] at Hif; simp at Hif; omega
    subst hk0
    rw [decide_eq_true (by rfl)]
    wp_auto
    wp_for_post
    iapply HΦ
    iexists stk1, els1
    iframe
    isplitl
    · unfold rCurKV
      iright
      ipureintro
      exact ⟨rUpInv_none els1 i1 s Hp Hu.2, rfl, rfl, rfl, i1, Hp⟩
    · ipureintro; exact ⟨fun h => Or.inl (Hoff h), fun _ => Hsame⟩

end proof

end bbolt
end EtcdGrove
end Perennial
