module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.mlist
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.parseRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.pastRead
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.predicate
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.keyInScope
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.listOptions
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.encodeItems
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PredOk
public import Spec.k8s_io.apiserver.pkg.storage.PrepareKey

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem mlist.wp_proof
    (wp_parseRV : parseRV.spec (GF := GF) (hG := hG))
    (wp_pastRead : pastRead.spec (GF := GF) (hG := hG))
    (wp_histAt : histAt.spec (GF := GF) (hG := hG))
    (wp_predicate : predicate.spec (GF := GF) (hG := hG))
    (wp_storeKey : storeKey.spec (GF := GF) (hG := hG))
    (wp_keyInScope : keyInScope.spec (GF := GF) (hG := hG))
    (wp_listOptions : listOptions.spec (GF := GF) (hG := hG))
    (wp_encodeItems : encodeItems.spec (GF := GF) (hG := hG))
    (wp_Matches : mlistMatches.spec (GF := GF) (hG := hG))
    (wp_PrepareKey : storage.PrepareKey.spec (GF := GF) (hG := hG))
    (wp_PrepareContinueToken : mlistPCT.spec (GF := GF) (hG := hG)) :
    mlist.spec (GF := GF) (hG := hG) := by
  intro x c g
  wp_start as #Hc
  unfold cfgOwn storeOwn
  icases Hc with ⟨⟨#Hk, %Hr⟩, #Hh, #Hp, %Hhl⟩
  wp_auto
  wp_apply wp_parseRV as %req %err Hpr
  cases hp : parseRVD x.MinRV' with
  | none =>
    isimp only [hp] at Hpr
    icases Hpr with ⟨%hne, -⟩
    cases err with
    | nil => exact absurd rfl hne
    | ok i =>
      (try wp_auto)
      have : mlistL x g.st = otherL := by simp [mlistL, hp]
      rw [this]
      simp only [otherL, errOutL]
      iapply HΦ
      itrivial
  | some m =>
    isimp only [hp] at Hpr
    icases Hpr with ⟨%he, %hm⟩
    subst he hm
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      have : mlistL x g.st = tooLargeL := by
        simp only [mlistL, hp]; rw [if_pos (by rw [← Hr]; word)]
      rw [this]
      simp only [tooLargeL, errOutL]
      iapply HΦ
      itrivial
    have hle : ¬ uint.nat g.st.st.rv < uint.nat req := by rw [← Hr]; word
    wp_apply wp_pastRead
    (try wp_auto)
    wp_join iprop(∃ s : mstore, st_ptr ↦ s ∗ storeOwn s (listStL x g.st req) ∗ c_ptr ↦ c ∗
        req_ptr ↦ req) at next with [st c req]
      as ⟨%s, st, #Hs, c, req⟩
    · cases Hif : pastReadL x req
      · (try wp_auto)
        wp_join_done
        iexists c.st'
        iframe
        simp only [listStL, Hif, Bool.false_eq_true, ↓reduceIte]
        unfold storeOwn
        isplit
        · iexact Hk
        · ipureintro; exact Hr
      · (try wp_auto)
        wp_apply wp_histAt $$ [$Hh] as %s #Hs
        · ipureintro; exact Hhl
        (try wp_auto)
        wp_join_done
        iexists s
        iframe
        simp only [listStL, Hif, Bool.false_eq_true, ↓reduceIte]
        iexact Hs
    wp_apply wp_predicate
    (try wp_auto)
    obtain ⟨S, hS⟩ : ∃ S, listStL x g.st req = S := ⟨_, rfl⟩
    rw [hS]
    unfold storeOwn
    icases Hs with ⟨#Hsi, %Hsr⟩
    ihave %Hsl := ownSlice_len $$ Hsi
    have hSl : S.items.length < 2 ^ 63 := by have := Hsl; word
    ihave HI : (∃ (j : w64) (itv : item) (isl : GoSlice),
        "i" ∷ i_ptr ↦ j ∗ "it" ∷ it_ptr ↦ itv ∗ "items" ∷ items_ptr ↦ isl ∗
        "Hisl" ∷ isl ↦* (listLoopL x (S.items.take (sint.nat j))).items.reverse ∗
        "Hcap" ∷ ownSliceCap Obj isl (DFrac.own 1) ∗
        "lastKey" ∷ lastKey_ptr ↦ ((listLoopL x (S.items.take (sint.nat j))).last.getD []) ∗
        "hasMore" ∷ hasMore_ptr ↦ (listLoopL x (S.items.take (sint.nat j))).more ∗
        "total" ∷ total_ptr ↦ W64 ((listLoopL x (S.items.take (sint.nat j))).total : Int) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.items'.len⌝ : IProp GF)
        $$ [i it items lastKey hasMore total]
    · iexists W64 0, _, slice.nil
      rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero,
        show listLoopL x [] = ⟨[], none, false, 0⟩ from rfl]
      simp only [List.reverse_nil]
      iframe
      isplitl
      · iapply ownSlice_nil
      isplitl
      · iapply ownSliceCap_nil
      ipureintro; refine ⟨by word, by word⟩
    irename : (in_ptr ↦ x : IProp GF) => Hin
    wp_for HI
    wp_if_destruct
    · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.items'.len := ⟨Hj.1, Hif⟩
      simp only [Hb', _root_.and_self, ↓reduceIte]
      list_elem S.items (sint.nat j) as itm
      wp_apply wp_load_slice_index s.items' (sint.Z j) S.items DFrac.discard itm Hj.1 $$ [Hsi] as -
      · isplit
        · iexact Hsi
        · ipureintro; exact Hitm_lookup
      (try wp_auto)
      wp_apply wp_storeKey
      (try wp_auto)
      wp_apply wp_keyInScope
      (try wp_auto)
      have hstep := listLoopL_take_succ x S.items (sint.nat j) itm Hitm_lookup
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      obtain ⟨hLi0, hLt0⟩ := listLoopL_le x (S.items.take (sint.nat j))
      have hLt0' : (listLoopL x (S.items.take (sint.nat j))).total ≤ sint.nat j := by
        have := List.length_take_le (sint.nat j) S.items; omega
      obtain ⟨L0, hL0⟩ : ∃ L0, listLoopL x (S.items.take (sint.nat j)) = L0 := ⟨_, rfl⟩
      rw [hL0] at hstep hLi0 hLt0' ⊢
      cases hsc : keyInScopeL x.ListKey' x.Recursive' (storeKeyL itm.key')
      · simp only [hsc, ↓reduceIte, Bool.false_eq_true] at hstep
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, itm, isl
        rw [hj1, hstep]
        iframe
        ipureintro; refine ⟨by word, by word⟩
      · simp only [hsc, ↓reduceIte] at hstep
        (try wp_auto)
        ihave %Hil := ownSlice_len $$ Hisl
        have htot : W64 (L0.total : Int) + W64 1 = W64 ((L0.total + 1 : Nat) : Int) := by word
        rw [htot]
        wp_if_destruct
        · have hln : limitN x = (sint.Z x.Limit').toNat := by
            unfold limitN; rw [if_pos (by word)]
          wp_if_destruct
          · have hst : listLoopL x (S.items.take (sint.nat j + 1)) =
                ⟨L0.items, L0.last, true, L0.total + 1⟩ := by
              have hf : 0 < limitN x ∧ limitN x ≤ L0.items.length := by
                rw [hln]; simp only [List.length_reverse] at Hil; word
              rw [hstep]; simp [ListModel.lstep, hf]
            (try wp_auto)
            wp_for_post
            iframe
            iexists j + W64 1, itm, isl
            rw [hj1, hst]
            iframe
            ipureintro; refine ⟨by word, by word⟩
          · have hnf : ¬ (0 < limitN x ∧ limitN x ≤ L0.items.length) := by
              rw [hln]; simp only [List.length_reverse] at Hil; word
            (try wp_auto)
            wp_apply wp_Matches $$ [$pred $o] as ⟨pred, o⟩
            (try wp_auto)
            cases hsel : selOkL x itm.obj'
            · have hst : listLoopL x (S.items.take (sint.nat j + 1)) =
                  ⟨L0.items, L0.last, L0.more, L0.total + 1⟩ := by
                rw [hstep]; simp [ListModel.lstep, hnf, hsel]
              (try wp_auto)
              wp_for_post
              iframe
              iexists j + W64 1, itm, isl
              rw [hj1, hst]
              iframe
              ipureintro; refine ⟨by word, by word⟩
            · have hst : listLoopL x (S.items.take (sint.nat j + 1)) =
                  ⟨itm.obj' :: L0.items, some (storeKeyL itm.key'), L0.more, L0.total + 1⟩ := by
                rw [hstep]; simp [ListModel.lstep, hnf, hsel]
              (try wp_auto)
              wp_apply wp_slice_literal
              isplitr
              · ipureintro; rfl
              iintro %osl ⟨Hosl, -⟩
              (try wp_auto)
              wp_apply wp_slice_append $$ [$Hisl $Hcap $Hosl] as %isl' ⟨Hisl, Hcap, -⟩
              (try wp_auto)
              wp_for_post
              iframe
              iexists j + W64 1, itm, isl'
              rw [hj1, hst]
              simp only [List.reverse_cons, Option.getD_some]
              iframe
              ipureintro; refine ⟨by word, by word⟩
        · have hnf : ¬ (0 < limitN x ∧ limitN x ≤ L0.items.length) := by
            unfold limitN; rw [if_neg (by word)]; omega
          (try wp_auto)
          wp_apply wp_Matches $$ [$pred $o] as ⟨pred, o⟩
          (try wp_auto)
          cases hsel : selOkL x itm.obj'
          · have hst : listLoopL x (S.items.take (sint.nat j + 1)) =
                ⟨L0.items, L0.last, L0.more, L0.total + 1⟩ := by
              rw [hstep]; simp [ListModel.lstep, hnf, hsel]
            (try wp_auto)
            wp_for_post
            iframe
            iexists j + W64 1, itm, isl
            rw [hj1, hst]
            iframe
            ipureintro; refine ⟨by word, by word⟩
          · have hst : listLoopL x (S.items.take (sint.nat j + 1)) =
                ⟨itm.obj' :: L0.items, some (storeKeyL itm.key'), L0.more, L0.total + 1⟩ := by
              rw [hstep]; simp [ListModel.lstep, hnf, hsel]
            (try wp_auto)
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %osl ⟨Hosl, -⟩
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hisl $Hcap $Hosl] as %isl' ⟨Hisl, Hcap, -⟩
            (try wp_auto)
            wp_for_post
            iframe
            iexists j + W64 1, itm, isl'
            rw [hj1, hst]
            simp only [List.reverse_cons, Option.getD_some]
            iframe
            ipureintro; refine ⟨by word, by word⟩
    · have htake : S.items.take (sint.nat j) = S.items := List.take_of_length_le (by word)
      rw [htake]
      obtain ⟨hLi, hLt⟩ := listLoopL_le x S.items
      obtain ⟨L, hL⟩ : ∃ L, listLoopL x S.items = L := ⟨_, rfl⟩
      rw [hL] at hLi hLt ⊢
      wp_apply wp_PrepareKey as %prep %err2 %Hpk
      cases hk : k8s.prepareKeyM go!"/objs" x.ListKey' x.Recursive' with
      | none =>
        rw [hk] at Hpk
        cases err2 with
        | nil => exact absurd rfl Hpk
        | ok i =>
          (try wp_auto)
          have : mlistL x g.st = otherL := by simp [mlistL, hp, hle, hk]
          rw [this]
          simp only [otherL, errOutL]
          iapply HΦ
          itrivial
      | some p =>
        rw [hk] at Hpk
        obtain ⟨rfl, rfl⟩ := Hpk
        (try wp_auto)
        wp_apply wp_listOptions
        (try wp_auto)
        wp_apply wp_PrepareContinueToken as %cont %rem %err3 Hct
        have hm : mlistL x g.st = listOutL x S L prep := by
          simp [mlistL, hp, hle, hk, hS, hL]
        rw [hm]
        imod ownSlice_persist _ _ _ $$ Hisl with #Hisl
        cases hmore : L.more
        · isimp only [Bool.false_eq_true, ↓reduceIte] at Hct
          icases Hct with %Hct
          obtain ⟨rfl, rfl, rfl⟩ := Hct
          (try wp_auto)
          wp_apply wp_encodeItems $$ [$Hisl]
          (try wp_auto)
          simp only [listOutL, hmore, Bool.false_eq_true, ↓reduceIte, Hsr]
          iapply HΦ; itrivial
        · isimp only [↓reduceIte] at Hct
          cases henc : encOkL (go!"/registry" ++ L.last.getD [] ++ [W8 0]) (go!"/registry" ++ prep)
          · isimp only [Bool.false_eq_true, ↓reduceIte] at Hct
            icases Hct with %Hct
            cases err3 with
            | nil => exact absurd rfl Hct
            | ok i =>
              (try wp_auto)
              simp only [listOutL, hmore, henc, Bool.false_eq_true, ↓reduceIte, otherL, errOutL]
              iapply HΦ; itrivial
          · isimp only [↓reduceIte] at Hct
            icases Hct with ⟨%Hct, Hrem⟩
            obtain ⟨rfl, rfl⟩ := Hct
            (try wp_auto)
            wp_apply wp_encodeItems $$ [$Hisl]
            (try wp_auto)
            cases hpe : predEmptyL x
            · isimp only [Bool.false_eq_true, ↓reduceIte] at Hrem
              icases Hrem with %Hrem
              subst Hrem
              (try wp_auto)
              simp only [listOutL, hmore, henc, hpe, Bool.false_eq_true, ↓reduceIte, Hsr]
              iapply HΦ; itrivial
            · isimp only [↓reduceIte] at Hrem
              icases typedPointsto_not_null_dup _ _ _ $$ Hrem with ⟨Hrem, %Hnn⟩
              (try wp_auto)
              simp only [Hnn, decide_false, Bool.not_false, ↓reduceIte]
              (try wp_auto)
              simp only [listOutL, hmore, henc, hpe, ↓reduceIte, Hsr]
              iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
