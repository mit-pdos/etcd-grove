/-
`value.FieldList.Equals`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.FieldList__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.Equals
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

theorem value.FieldList.Equals.wp_proof
    (h_Equals : value.Equals.spec (GF := GF)) :
    value.FieldList.Equals.spec (GF := GF) := fun f g fl gl => by
  wp_start as ⟨#Hf, #Hg⟩
  icases isFieldList_val $$ Hf with ⟨%fs, #Hfs, #HfL⟩
  icases isFieldList_val $$ Hg with ⟨%gs, #Hgs, #HgL⟩
  ihave %Hfl := isFieldsL_length $$ HfL
  ihave %Hgl := isFieldsL_length $$ HgL
  ihave %Hfsl := ownSlice_len $$ Hfs
  ihave %Hgsl := ownSlice_len $$ Hgs
  wp_auto
  wp_if_destruct
  · rename_i ik_ptr
    have hlenEq : f.len = g.len := Hif
    ihave HI : (∃ (j : w64) (k : w64), "i" ∷ i_ptr ↦ j ∗ "ik" ∷ ik_ptr ↦ k ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z f.len ∧
          fl.take (sint.nat j) = gl.take (sint.nat j)⌝ : IProp GF) $$ [-HΦ «$res0» f rhs]
    · iexists _, _; iframe; ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (W64 0) = 0 from rfl]; rfl
    wp_for HI
    wp_if_destruct
    · obtain ⟨hj0, hjl, htake⟩ := Hj
      have hjf : sint.Z j < sint.Z f.len := Hif
      have hjn : sint.nat j < fs.length := by rw [Hfsl.1]; word
      have hjn' : sint.nat j < gs.length := by rw [Hgsl.1, ← hlenEq]; word
      list_elem fs (sint.nat j) as x
      list_elem gs (sint.nat j) as y
      simp only [hj0, Hif, _root_.and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index f (sint.Z j) fs DFrac.discard x hj0)
      · isplitr; · iexact Hfs
        ipureintro; exact Hx_lookup
      iintro -
      have hj0' : sint.Z j < sint.Z g.len := by rw [← hlenEq]; exact Hif
      ihave ⟨#Hx, -⟩ := ownSlice_elem_acc (sint.Z j) x f DFrac.discard fs hj0 Hx_lookup $$ Hfs
      ihave ⟨#Hy, -⟩ := ownSlice_elem_acc (sint.Z j) y g DFrac.discard gs hj0 Hy_lookup $$ Hgs
      icases (value.Field.Field_access_load_Name _ x DFrac.discard).access_strict $$ Hx with ⟨#Hxn, -⟩
      icases (value.Field.Field_access_load_Name _ y DFrac.discard).access_strict $$ Hy with ⟨#Hyn, -⟩
      icases (value.Field.Field_access_load_Value _ x DFrac.discard).access_strict $$ Hx with ⟨#Hxv, -⟩
      icases (value.Field.Field_access_load_Value _ y DFrac.discard).access_strict $$ Hy with ⟨#Hyv, -⟩
      wp_auto
      simp only [hj0, Hif, hj0', _root_.and_self, ↓reduceIte]
      wp_auto
      simp only [hj0, Hif, hj0', _root_.and_self, ↓reduceIte]
      wp_auto
      have hjfl : sint.nat j < fl.length := by omega
      have hjgl : sint.nat j < gl.length := by omega
      have he1 : fl[sint.nat j]? = some (fl[sint.nat j]'hjfl) := List.getElem?_eq_getElem hjfl
      have he2 : gl[sint.nat j]? = some (gl[sint.nat j]'hjgl) := List.getElem?_eq_getElem hjgl
      generalize fl[sint.nat j]'hjfl = e1 at he1
      generalize gl[sint.nat j]'hjgl = e2 at he2
      obtain ⟨n1, v1⟩ := e1
      obtain ⟨n2, v2⟩ := e2
      ihave ⟨%x', %hx', #Hxval⟩ := isFieldsL_lookup fs fl (sint.nat j) n1 v1 he1 $$ HfL
      ihave ⟨%y', %hy', #Hyval⟩ := isFieldsL_lookup gs gl (sint.nat j) n2 v2 he2 $$ HgL
      rw [Hx_lookup] at hx'
      rw [Hy_lookup] at hy'
      obtain ⟨hxx, hn1⟩ := hx'
      obtain ⟨hyy, hn2⟩ := hy'
      cases hxx; cases hyy
      have hstep : fl[sint.nat j]? = gl[sint.nat j]? → fl.take (sint.nat j + 1) = gl.take (sint.nat j + 1) := by
        intro h; rw [List.take_add_one, List.take_add_one, htake, h]
      wp_if_destruct
      · simp only [hj0, hjf, hj0', _root_.and_self, ↓reduceIte]
        wp_auto
        simp only [hj0, hjf, hj0', _root_.and_self, ↓reduceIte]
        wp_auto
        wp_apply (h_Equals _ _ DFrac.discard DFrac.discard v1 v2) $$ [$Hxval $Hyval] as %r ⟨-, -, %hr⟩
        cases r <;> wp_auto
        · wp_for_post
          iapply HΦ
          ipureintro
          simp only [Bool.false_eq_true, false_iff]
          intro h; subst h
          rw [he1] at he2; cases he2
          simp at hr
        · wp_for_post
          iframe
          iexists j + 1, j
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [show sint.nat (j + 1) = sint.nat j + 1 by word]
          apply hstep
          rw [he1, he2, (hr.1 rfl), ← hn1, ← hn2, Hif]
      · wp_for_post
        iapply HΦ
        ipureintro
        simp only [Bool.false_eq_true, false_iff]
        intro h; subst h
        rw [he1] at he2; cases he2
        exact Hif (hn1.trans hn2.symm)
    · obtain ⟨hj0, hjl, htake⟩ := Hj
      iapply HΦ
      ipureintro
      simp only [_root_.true_iff]
      have h1 : sint.nat j = fl.length := by rw [← Hfl, Hfsl.1]; word
      have h2 : fl.length = gl.length := by rw [← Hfl, ← Hgl, Hfsl.1, Hgsl.1, hlenEq]
      rw [h1, List.take_length, h2, List.take_length] at htake
      exact htake
  · iapply HΦ
    ipureintro
    simp only [Bool.false_eq_true, false_iff]
    intro h; subst h
    apply Hif
    have : sint.nat f.len = sint.nat g.len := by rw [← Hfsl.1, ← Hgsl.1, Hfl, Hgl]
    word

end proof

end smd
end EtcdGrove
end Perennial
