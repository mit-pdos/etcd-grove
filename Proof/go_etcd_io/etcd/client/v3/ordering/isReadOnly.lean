/-
Proof of `Spec/go_etcd_io/etcd/client/v3/ordering/isReadOnly.lean`.
`isReadOnly` is recursive over nested `OpTxn`s; the proof is by induction on `t.size` (`OpT.size`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ordering.isReadOnly
public import Spec.go_etcd_io.etcd.client.v3.Op__IsGet
public import Spec.go_etcd_io.etcd.client.v3.Op__IsTxn
public import Spec.go_etcd_io.etcd.client.v3.Op__Txn

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ordering

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.ordering

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.ordering.Assumptions]

theorem isReadOnly_wp_size
    (hIsGet : EtcdGrove.Op.IsGet.spec (GF := GF) (hG := hG))
    (hIsTxn : EtcdGrove.Op.IsTxn.spec (GF := GF) (hG := hG))
    (hTxn : EtcdGrove.Op.Txn.spec (GF := GF) (hG := hG)) :
    ∀ (N : Nat) (t : OpT), t.size < N →
    ∀ (opv : go_etcd_io.etcd.client.v3.Op),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.ordering ∗
      opTAtC false opv t }}
    (App (Val (@! isReadOnly)) (Val #opv))
  {{ RET #(isReadOnlyM t); True }} := by
  intro N
  induction N with
  | zero => intro t h; omega
  | succ N IH =>
  intro t ht opv
  wp_start as #Ht
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  cases t with
  | leaf o =>
    iunfold opTAtC at Ht
    icases Ht with ⟨#Hat, %Ho4⟩
    wp_auto
    wp_apply hIsGet $$ [$op $Hat] as op
    by_cases h1 : o.t = W64 1
    · simp only [isReadOnlyM, h1, decide_true, ↓reduceIte]
      wp_auto
      iapply HΦ; itrivial
    · simp only [isReadOnlyM, decide_eq_false h1, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_apply hIsTxn $$ [$op $Hat] as op
      simp only [decide_eq_false Ho4, Bool.not_false, ↓reduceIte]
      wp_auto
      iapply HΦ; itrivial
  | txn o cs ts es =>
    iunfold opTAtC at Ht
    icases Ht with ⟨#Hat, %Ho4, #Hcs, %tvs, %evs, #Htvs, #Hevs, -, #Hts, #Hes⟩
    have Ho1 : o.t ≠ W64 1 := by rw [Ho4]; decide
    ihave %Hlen_t := opListAtC_length false tvs ts $$ Hts
    ihave %Hlen_e := opListAtC_length false evs es $$ Hes
    ihave %Hsl_t := ownSlice_len _ _ _ $$ Htvs
    ihave %Hsl_e := ownSlice_len _ _ _ $$ Hevs
    wp_auto
    wp_apply hIsGet $$ [$op $Hat] as op
    simp only [decide_eq_false Ho1, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_apply hIsTxn $$ [$op $Hat] as op
    simp only [decide_eq_true Ho4, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_apply hTxn $$ [$op] as op
    (try wp_auto)
    wp_apply wp_slice_literal (l := [opv.thenOps', opv.elseOps'])
    isplitr
    · ipureintro; rfl
    iintro %bsl ⟨Hbsl, -⟩
    ihave %Hsl_b := ownSlice_len _ _ _ $$ Hbsl
    simp only [List.length_cons, List.length_nil] at Hsl_b
    (try wp_auto)
    ihave IH_outer : iprop(∃ (b : w64) (br : GoSlice),
        "Hi_outer" ∷ i_ptr ↦ b ∗ "branch" ∷ branch_ptr ↦ br ∗
        "Hbsl" ∷ slice.mk bsl (W64 (go.arrayLiteralSize
          [KeyedElement none (ElementExpression go_etcd_io.etcd.client.v3.Op.ty.SliceType #opv.thenOps'),
           KeyedElement none (ElementExpression go_etcd_io.etcd.client.v3.Op.ty.SliceType #opv.elseOps')]))
          (W64 (go.arrayLiteralSize
          [KeyedElement none (ElementExpression go_etcd_io.etcd.client.v3.Op.ty.SliceType #opv.thenOps'),
           KeyedElement none (ElementExpression go_etcd_io.etcd.client.v3.Op.ty.SliceType #opv.elseOps')])) ↦*
          [opv.thenOps', opv.elseOps'] ∗
        "%Hb" ∷ ⌜0 ≤ sint.Z b ∧ sint.Z b ≤ 2 ∧
          (1 ≤ sint.nat b → isReadOnlyListM ts = true) ∧
          (2 ≤ sint.nat b → isReadOnlyListM es = true)⌝) $$ [i branch Hbsl]
    · iexists W64 0, slice.nil
      simp only [named, show sint.nat (W64 0) = 0 from rfl]
      iframe
      ipureintro; refine ⟨by word, by word, by omega, by omega⟩
    wp_for IH_outer
    wp_if_destruct
    · simp only [Hb.1, Hif, _root_.and_self, ↓reduceIte]
      have Hb01 : sint.nat b = 0 ∨ sint.nat b = 1 := by
        change sint.Z b < sint.Z (W64 2) at Hif
        word
      rcases Hb01 with hb0 | hb1
      · -- Outer iteration 0: `thenOps` (`ts`)
        have Hbi : ([opv.thenOps', opv.elseOps'] : List GoSlice)[sint.nat b]? = some opv.thenOps' := by
          rw [hb0]; rfl
        wp_apply wp_load_slice_index _ (sint.Z b)
          [opv.thenOps', opv.elseOps'] (DFrac.own 1) opv.thenOps' Hb.1 $$ [$Hbsl] as Hbsl
        · ipureintro; exact Hbi
        ihave IH_inner : iprop(∃ (j : w64) (nop : go_etcd_io.etcd.client.v3.Op),
            "branch" ∷ branch_ptr ↦ opv.thenOps' ∗
            "Hi_inner" ∷ i_ptr ↦ j ∗
            "nestedOp" ∷ nestedOp_ptr ↦ nop ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (tvs.length : Int) ∧
              isReadOnlyListM (ts.take (sint.nat j)) = true⌝) $$ [branch i nestedOp]
        · iexists W64 0, _
          simp only [named, show sint.nat (W64 0) = 0 from rfl, List.take_zero, isReadOnlyListM]
          iframe
          ipureintro; refine ⟨by word, by word, trivial⟩
        wp_for IH_inner
        by_cases Hif_inner : sint.Z j < sint.Z opv.thenOps'.len
        · simp only [Hif_inner, _root_.decide_true, ↓reduceIte]
          wp_auto
          have Hjlt : sint.nat j < tvs.length := by word
          obtain ⟨v, Hvi⟩ : ∃ v, tvs[sint.nat j]? = some v := ⟨_, List.getElem?_eq_getElem Hjlt⟩
          obtain ⟨sub, Hsubi⟩ : ∃ sub, ts[sint.nat j]? = some sub :=
            ⟨_, List.getElem?_eq_getElem (by rw [← Hlen_t]; exact Hjlt)⟩
          have Hjbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z opv.thenOps'.len := ⟨Hj.1, Hif_inner⟩
          simp only [Hjbnd, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index opv.thenOps' (sint.Z j) tvs DFrac.discard v Hj.1 $$ [Htvs] as -
          · iframe #; ipureintro; exact Hvi
          ihave ⟨#Hsub, -⟩ := opListAtC_get false tvs ts (sint.nat j) v sub Hvi Hsubi $$ Hts
          have Hsub_sz : sub.size < N := by
            have := OpT.size_le_of_getElem? ts (sint.nat j) sub Hsubi
            simp only [OpT.size] at ht
            omega
          (try wp_auto)
          wp_apply (IH sub Hsub_sz v) $$ [$Hsub]
          cases hro : isReadOnlyM sub
          · -- `isReadOnly(nestedOp)` returned `false`: return `false` immediately
            simp only [Bool.not_false, ↓reduceIte]
            wp_auto
            wp_for_post
            wp_for_post
            have hts_false : isReadOnlyListM ts = false :=
              isReadOnlyListM_false_of_getElem? ts (sint.nat j) sub Hsubi hro
            simp only [isReadOnlyM, hts_false, Bool.false_and]
            iapply HΦ; itrivial
          · -- `isReadOnly(nestedOp)` returned `true`: continue inner loop
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            wp_auto
            wp_for_post
            iframe
            iexists (j + W64 1), v
            simp only [named]
            iframe
            ipureintro
            refine ⟨by word, by word, ?_⟩
            rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word,
              isReadOnlyListM_take_succ ts (sint.nat j) sub Hsubi, Hj.2.2, hro]
        · -- Inner loop finished on `thenOps`
          simp only [Hif_inner, _root_.decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte,
            show ((#false : val) = #true) ↔ False from ⟨false_neq_true, False.elim⟩]
          have Hfull : sint.nat j = ts.length := by rw [← Hlen_t]; word
          have Hts_ok : isReadOnlyListM ts = true := by
            have := Hj.2.2; rw [Hfull, List.take_length] at this; exact this
          wp_for_post
          iframe
          iexists (b + W64 1), opv.thenOps'
          simp only [named]
          iframe
          ipureintro
          refine ⟨by word, by word, fun _ => Hts_ok, by word⟩
      · -- Outer iteration 1: `elseOps` (`es`)
        have Hbi : ([opv.thenOps', opv.elseOps'] : List GoSlice)[sint.nat b]? = some opv.elseOps' := by
          rw [hb1]; rfl
        have Hts_ok : isReadOnlyListM ts = true := Hb.2.2.1 (by omega)
        wp_apply wp_load_slice_index _ (sint.Z b)
          [opv.thenOps', opv.elseOps'] (DFrac.own 1) opv.elseOps' Hb.1 $$ [$Hbsl] as Hbsl
        · ipureintro; exact Hbi
        ihave IH_inner : iprop(∃ (j : w64) (nop : go_etcd_io.etcd.client.v3.Op),
            "branch" ∷ branch_ptr ↦ opv.elseOps' ∗
            "Hi_inner" ∷ i_ptr ↦ j ∗
            "nestedOp" ∷ nestedOp_ptr ↦ nop ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (evs.length : Int) ∧
              isReadOnlyListM (es.take (sint.nat j)) = true⌝) $$ [branch i nestedOp]
        · iexists W64 0, _
          simp only [named, show sint.nat (W64 0) = 0 from rfl, List.take_zero, isReadOnlyListM]
          iframe
          ipureintro; refine ⟨by word, by word, trivial⟩
        wp_for IH_inner
        by_cases Hif_inner : sint.Z j < sint.Z opv.elseOps'.len
        · simp only [Hif_inner, _root_.decide_true, ↓reduceIte]
          wp_auto
          have Hjlt : sint.nat j < evs.length := by word
          obtain ⟨v, Hvi⟩ : ∃ v, evs[sint.nat j]? = some v := ⟨_, List.getElem?_eq_getElem Hjlt⟩
          obtain ⟨sub, Hsubi⟩ : ∃ sub, es[sint.nat j]? = some sub :=
            ⟨_, List.getElem?_eq_getElem (by rw [← Hlen_e]; exact Hjlt)⟩
          have Hjbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z opv.elseOps'.len := ⟨Hj.1, Hif_inner⟩
          simp only [Hjbnd, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index opv.elseOps' (sint.Z j) evs DFrac.discard v Hj.1 $$ [Hevs] as -
          · iframe #; ipureintro; exact Hvi
          ihave ⟨#Hsub, -⟩ := opListAtC_get false evs es (sint.nat j) v sub Hvi Hsubi $$ Hes
          have Hsub_sz : sub.size < N := by
            have := OpT.size_le_of_getElem? es (sint.nat j) sub Hsubi
            simp only [OpT.size] at ht
            omega
          (try wp_auto)
          wp_apply (IH sub Hsub_sz v) $$ [$Hsub]
          cases hro : isReadOnlyM sub
          · -- `isReadOnly(nestedOp)` returned `false`: return `false` immediately
            simp only [Bool.not_false, ↓reduceIte]
            wp_auto
            wp_for_post
            wp_for_post
            have hes_false : isReadOnlyListM es = false :=
              isReadOnlyListM_false_of_getElem? es (sint.nat j) sub Hsubi hro
            simp only [isReadOnlyM, Hts_ok, hes_false, Bool.and_false]
            iapply HΦ; itrivial
          · -- `isReadOnly(nestedOp)` returned `true`: continue inner loop
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            wp_auto
            wp_for_post
            iframe
            iexists (j + W64 1), v
            simp only [named]
            iframe
            ipureintro
            refine ⟨by word, by word, ?_⟩
            rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word,
              isReadOnlyListM_take_succ es (sint.nat j) sub Hsubi, Hj.2.2, hro]
        · -- Inner loop finished on `elseOps`
          simp only [Hif_inner, _root_.decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte,
            show ((#false : val) = #true) ↔ False from ⟨false_neq_true, False.elim⟩]
          have Hfull : sint.nat j = es.length := by rw [← Hlen_e]; word
          have Hes_ok : isReadOnlyListM es = true := by
            have := Hj.2.2; rw [Hfull, List.take_length] at this; exact this
          wp_for_post
          iframe
          iexists (b + W64 1), opv.elseOps'
          simp only [named]
          iframe
          ipureintro
          refine ⟨by word, by word, fun _ => Hts_ok, fun _ => Hes_ok⟩
    · -- Outer loop finished (`b = 2`)
      change ¬ sint.Z b < sint.Z (W64 2) at Hif
      have Hb2 : sint.nat b = 2 := by word
      have Hts_ok : isReadOnlyListM ts = true := Hb.2.2.1 (by omega)
      have Hes_ok : isReadOnlyListM es = true := Hb.2.2.2 (by omega)
      (try wp_auto)
      simp only [isReadOnlyM, Hts_ok, Hes_ok, Bool.and_self]
      iapply HΦ; itrivial

theorem isReadOnly.wp_proof
    (hIsGet : EtcdGrove.Op.IsGet.spec (GF := GF) (hG := hG))
    (hIsTxn : EtcdGrove.Op.IsTxn.spec (GF := GF) (hG := hG))
    (hTxn : EtcdGrove.Op.Txn.spec (GF := GF) (hG := hG)) :
    isReadOnly.spec (GF := GF) (hG := hG) := by
  intro opv t
  exact isReadOnly_wp_size hIsGet hIsTxn hTxn (t.size + 1) t (Nat.lt_succ_self _) opv

end proof

end ordering
end EtcdGrove
end Perennial
