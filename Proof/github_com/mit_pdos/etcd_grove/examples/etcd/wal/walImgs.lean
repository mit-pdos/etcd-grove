/- Lean-first (no Rocq counterpart). The proof of `walImgs`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walImgs
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.copyOps
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.copyEnts
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.hsEmpty
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RefLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- `walImgs`'s `out` before position `j`. -/
def imgsAcc (h : List TOp) (n j : Nat) : List (List TOp) :=
  (List.range' n (j - n)).flatMap (fun j => h.take j :: tTornImgs h j)

theorem imgsAcc_succ (h : List TOp) (n j : Nat) (hj : n ≤ j) :
    imgsAcc h n (j + 1) = imgsAcc h n j ++ (h.take j :: tTornImgs h j) := by
  unfold imgsAcc
  rw [show j + 1 - n = (j - n) + 1 by omega, List.range'_concat, List.flatMap_append]
  simp [show n + (j - n) = j by omega]

/-- `walImgs`'s torn images at position `j` before `k`. -/
def tornAcc (h : List TOp) (j : Nat) (ents : List TEnt) (k : Nat) : List (List TOp) :=
  (List.range k).map (fun k => h.take j ++ [tTornOp (ents.take k)])

theorem tornAcc_succ (h : List TOp) (j : Nat) (ents : List TEnt) (k : Nat) :
    tornAcc h j ents (k + 1) = tornAcc h j ents k ++ [h.take j ++ [tTornOp (ents.take k)]] := by
  unfold tornAcc; rw [List.range_succ, List.map_append]; rfl

theorem tornAcc_cons_succ (A : List (List TOp)) (x : List TOp) (h : List TOp) (j : Nat)
    (ents : List TEnt) (k : Nat) :
    A ++ x :: tornAcc h j ents (k + 1) =
      (A ++ x :: tornAcc h j ents k) ++ [h.take j ++ [tTornOp (ents.take k)]] := by
  rw [tornAcc_succ]; simp

theorem walImgs.wp_proof (wp_copyOps : copyOps.spec (GF := GF) (hG := hG))
    (wp_copyEnts : copyEnts.spec (GF := GF) (hG := hG))
    (wp_hsEmpty : hsEmpty.spec (GF := GF) (hG := hG)) :
    walImgs.spec (GF := GF) (hG := hG) := by
  intro s h n hn
  wp_start as #Hr
  ihave Hr2 := Hr
  iunfold opsRep at Hr2
  icases Hr2 with ⟨%es, #Hs, #Hel⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf $$ Hs
  ihave %Hel_len := opsElems_length $$ Hel
  wp_auto
  wp_apply +noauto (wp_slice_make2 (V := GoSlice) (W64 0)) as %o0 ⟨Ho0, Ho0cap⟩
  · ipureintro; word
  simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
  ipersist Ho0
  wp_auto
  wp_if_destruct
  · have : h.length + 1 - sint.nat n = 0 := by word
    iapply HΦ
    unfold tImgs; rw [this]
    simp only [List.range'_zero, List.flatMap_nil]
    iunfold imgsRep
    iexists []
    isplitl []
    · iexact Ho0
    iapply imgsElems_nil
  ihave HI : (∃ (j : w64) (o : GoSlice) (ovs : List GoSlice),
      "j" ∷ j_ptr ↦ j ∗ "out" ∷ out_ptr ↦ o ∗
      "Ho" ∷ o ↦*□ ovs ∗ "Hocap" ∷ ownSliceCap GoSlice o (DFrac.own 1) ∗
      "Hoe" ∷ imgsElems ovs (imgsAcc h (sint.nat n) (sint.nat j)) ∗
      "h" ∷ h_ptr ↦ s ∗
      "%Hj" ∷ ⌜sint.Z n ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ : IProp GF) $$ [j out Ho0cap h]
  · iexists n, o0, []
    unfold imgsAcc
    simp only [Nat.sub_self, List.range'_zero, List.flatMap_nil]
    iframe
    isplitl []
    · iexact Ho0
    isplitl []
    · iapply imgsElems_nil
    ipureintro; constructor <;> word
  wp_for HI
  icases Ho with #Ho
  icases Hoe with #Hoe
  have hj0 : 0 ≤ sint.Z j := by omega
  have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.cap :=
    ⟨by word, hj0, by omega⟩
  simp only [hb0, _root_.and_self, ↓reduceIte]
  ihave Hpre := opsRep_slice s h (W64 0) j ⟨by word, hj0, Hj.2⟩ $$ Hr
  have hpre : subslice (sint.nat (W64 0)) (sint.nat j) h = h.take (sint.nat j) := by
    rw [show sint.nat (W64 0) = 0 from rfl]; simp [subslice]
  rw [hpre]
  wp_apply wp_copyOps as %c ⟨%cvs, Hc, -, #Hce⟩
  · iexact Hpre
  ipersist Hc
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  wp_auto
  wp_apply wp_slice_append_persistent (sl := o) (vs := ovs) $$ [$Hocap $Hosl] as %o' ⟨Ho', Hocap, -⟩
  · iexact Ho
  ihave Hoe' := imgsElems_snoc ovs _ c (h.take (sint.nat j)) $$ [$Hoe]
  · iunfold opsRep; iexists cvs; isplitl []
    · iexact Hc
    · iexact Hce
  have hjn : sint.nat n ≤ sint.nat j := by word
  wp_join iprop(∃ (o2 : GoSlice) (ovs2 : List GoSlice), out_ptr ↦ o2 ∗ o2 ↦*□ ovs2 ∗
      ownSliceCap GoSlice o2 (DFrac.own 1) ∗ imgsElems ovs2 (imgsAcc h (sint.nat n) (sint.nat j + 1)) ∗
      h_ptr ↦ s ∗ j_ptr ↦ j)
    at next with [out Ho' Hocap Hoe' h j] as ⟨%o2, %ovs2, out, #Ho2, Hocap, #Hoe2, h, j⟩
  · rw [imgsAcc_succ h _ _ hjn]
    by_cases hlt : sint.Z j < sint.Z s.len
    · have hil : sint.nat j < es.length := by
        have : sint.nat j < sint.nat s.len := by word
        omega
      obtain ⟨v, Hv⟩ : ∃ v, es[sint.nat j]? = some v := ⟨_, List.getElem?_eq_getElem hil⟩
      have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨hj0, hlt⟩
      icases ownSlice_elem_acc (sint.Z j) v s DFrac.discard es hj0 (by simpa [sint.nat] using Hv) $$ Hs
        with ⟨Hv, -⟩
      icases opsElems_lookup es h (sint.nat j) v Hv $$ Hel with ⟨%op, %Hop, #Hopr⟩
      iunfold opRep at Hopr
      icases Hopr with ⟨%Hf, #Hoe⟩
      obtain ⟨hsn, hhs, -, -⟩ := Hf
      ihave %Hoel := ownSlice_len $$ Hoe
      iStructNamed Hv
      simp only [hlt, decide_true]
      wp_auto
      repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
      rw [hsn]
      cases hos : op.snap
      · wp_auto
        ihave HI2 : (∃ (k : w64) (o2 : GoSlice) (ovs2 : List GoSlice),
            "k" ∷ k_ptr ↦ k ∗ "out" ∷ out_ptr ↦ o2 ∗
            "Ho2" ∷ o2 ↦*□ ovs2 ∗ "Hocap" ∷ ownSliceCap GoSlice o2 (DFrac.own 1) ∗
            "Hoe2" ∷ imgsElems ovs2 (imgsAcc h (sint.nat n) (sint.nat j) ++
              h.take (sint.nat j) :: tornAcc h (sint.nat j) op.ents (sint.nat k)) ∗
            "h" ∷ h_ptr ↦ s ∗ "j" ∷ j_ptr ↦ j ∗
            "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z v.ents'.len⌝ : IProp GF)
          $$ [k out Ho' Hocap Hoe' h j]
        · iexists W64 0, o', ovs ++ [c]
          rw [show sint.nat (W64 0) = 0 from rfl]
          iframe
          ipureintro; constructor <;> word
        wp_for HI2
        icases Ho2 with #Ho2
        icases Hoe2 with #Hoe2
        ihave %Hewf := ownSlice_wf $$ Hoe
        repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
        by_cases hk : k = v.ents'.len
        · subst hk
          have htorn : tTornImgs h (sint.nat j) = tornAcc h (sint.nat j) op.ents
              (if tHsEmpty op.hs then op.ents.length else op.ents.length + 1) := by
            simp [tTornImgs, Hop, hos, tornAcc]
          simp only [decide_true]
          wp_auto
          repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
          wp_apply wp_hsEmpty
          rw [hhs]
          cases hhe : tHsEmpty op.hs
          · simp only [hhe, Bool.false_eq_true, ↓reduceIte] at htorn
            wp_auto
            simp only [hb0, _root_.and_self, ↓reduceIte]
            wp_apply wp_copyOps as %img ⟨%ivs, Hi, Hicap, #Hie⟩
            · iexact Hpre
            repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
            have hkb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z v.ents'.len ∧ sint.Z v.ents'.len ≤ sint.Z v.ents'.cap :=
              ⟨by word, Hk.1, by omega⟩
            simp only [hkb, _root_.and_self, ↓reduceIte]
            icases (ownSlice_slice (W64 0) v.ents'.len v.ents' DFrac.discard op.ents ⟨by word, Hk.1, Hk.2⟩).1 $$ Hoe
              with ⟨-, #Hek, -⟩
            wp_apply wp_copyEnts as %e' ⟨He', -, -⟩
            · iexact Hek
            ipersist He'
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %wsl ⟨Hwsl, -⟩
            wp_apply wp_slice_append $$ [$Hi $Hicap $Hwsl] as %img' ⟨Hi', -, -⟩
            ipersist Hi'
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %osl2 ⟨Hosl2, -⟩
            wp_apply wp_slice_append_persistent (sl := o2) (vs := ovs2) $$ [$Hocap $Hosl2]
              as %o3 ⟨Ho3, Hocap, -⟩
            · iexact Ho2
            repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
            wp_for_post
            wp_join_done
            iexists o3, ovs2 ++ [img']
            iframe
            rw [htorn, show op.ents.length = sint.nat v.ents'.len by omega, tornAcc_cons_succ]
            iapply imgsElems_snoc
            isplitl []
            · iexact Hoe2
            iunfold opsRep
            iexists _
            isplitl []
            · iexact Hi'
            iapply opsElems_snoc
            isplitl []
            · iexact Hie
            iunfold opRep
            isplitl []
            · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
            rw [show subslice (sint.nat (W64 0)) (sint.nat v.ents'.len) op.ents = op.ents.take (sint.nat v.ents'.len) by
              rw [show sint.nat (W64 0) = 0 from rfl]; simp [subslice]]
            dsimp only [tTornOp]
            iexact He'
          · simp only [hhe, ↓reduceIte] at htorn
            wp_auto
            wp_for_post
            wp_join_done
            iexists o2, ovs2
            iframe
            isplitl []
            · iexact Ho2
            rw [htorn, show op.ents.length = sint.nat v.ents'.len by omega]
            iexact Hoe2
        · simp only [hk, decide_false]
          wp_auto
          simp only [hb0, _root_.and_self, ↓reduceIte]
          wp_apply wp_copyOps as %img ⟨%ivs, Hi, Hicap, #Hie⟩
          · iexact Hpre
          repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
          have hkb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z k ∧ sint.Z k ≤ sint.Z v.ents'.cap :=
            ⟨by word, Hk.1, by omega⟩
          simp only [hkb, _root_.and_self, ↓reduceIte]
          icases (ownSlice_slice (W64 0) k v.ents' DFrac.discard op.ents ⟨by word, Hk.1, Hk.2⟩).1 $$ Hoe
            with ⟨-, #Hek, -⟩
          wp_apply wp_copyEnts as %e' ⟨He', -, -⟩
          · iexact Hek
          ipersist He'
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %wsl ⟨Hwsl, -⟩
          wp_apply wp_slice_append $$ [$Hi $Hicap $Hwsl] as %img' ⟨Hi', -, -⟩
          ipersist Hi'
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %osl2 ⟨Hosl2, -⟩
          wp_apply wp_slice_append_persistent (sl := o2) (vs := ovs2) $$ [$Hocap $Hosl2]
            as %o3 ⟨Ho3, Hocap, -⟩
          · iexact Ho2
          repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
          simp only [hk, decide_false]
          wp_auto
          wp_for_post
          iframe
          have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by
            have : sint.Z k ≠ sint.Z v.ents'.len := by intro h'; apply hk; word
            word
          iexists k + W64 1, o3, ovs2 ++ [img']
          rw [hk1]
          iframe
          isplitl []
          · rw [tornAcc_cons_succ]
            iapply imgsElems_snoc
            isplitl []
            · iexact Hoe2
            iunfold opsRep
            iexists _
            isplitl []
            · iexact Hi'
            iapply opsElems_snoc
            isplitl []
            · iexact Hie
            iunfold opRep
            isplitl []
            · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
            rw [show subslice (sint.nat (W64 0)) (sint.nat k) op.ents = op.ents.take (sint.nat k) by
              rw [show sint.nat (W64 0) = 0 from rfl]; simp [subslice]]
            dsimp only [tTornOp]
            iexact He'
          ipureintro
          have : sint.Z k ≠ sint.Z v.ents'.len := by intro h'; apply hk; word
          constructor <;> word
      · wp_auto
        have ht : tTornImgs h (sint.nat j) = [] := by simp [tTornImgs, Hop, hos]
        rw [ht]
        wp_join_done
    · simp only [hlt, decide_false]
      wp_auto
      have ht : tTornImgs h (sint.nat j) = [] := by
        have : h.length ≤ sint.nat j := by word
        simp [tTornImgs, List.getElem?_eq_none this]
      rw [ht]
      wp_join_done
  wp_if_destruct
  · wp_for_post
    iapply HΦ
    iunfold imgsRep
    iexists ovs2
    isplitl []
    · iexact Ho2
    have : sint.nat s.len = h.length := by omega
    rw [this] at *
    rw [show tImgs h (sint.nat n) = imgsAcc h (sint.nat n) (h.length + 1) from rfl]
    iexact Hoe2
  · wp_for_post
    iframe
    have : j ≠ s.len := Hif
    have : sint.Z j ≠ sint.Z s.len := by intro h'; apply this; word
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    iexists j + W64 1, o2, ovs2
    rw [hj1]
    iframe
    isplitl []
    · iexact Ho2
    isplitl []
    · iexact Hoe2
    ipureintro; constructor <;> word

end proof

end etcd_wal
end EtcdGrove
end Perennial
