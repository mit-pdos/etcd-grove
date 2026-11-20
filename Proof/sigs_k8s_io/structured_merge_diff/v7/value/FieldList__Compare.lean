/-
`value.FieldList.Compare`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.FieldList__Compare
public import Perennial.Spec.strings.Compare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.Compare
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

theorem flCompare_nil_left : ∀ l : FieldList, l ≠ [] → flCompare [] l = -1
  | [], h => absurd rfl h
  | _ :: _, _ => by simp [flCompare]
theorem flCompare_nil_right : ∀ l : FieldList, l ≠ [] → flCompare l [] = 1
  | [], h => absurd rfl h
  | _ :: _, _ => by simp [flCompare]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

theorem value.FieldList.Compare.wp_proof
    (h_strings_Compare : _root_.Perennial.strings.Compare.spec (GF := GF))
    (h_Compare : value.Compare.spec (GF := GF)) :
    value.FieldList.Compare.spec (GF := GF) := fun f g fl gl => by
  wp_start as ⟨#Hf, #Hg⟩
  icases isFieldList_val $$ Hf with ⟨%fs, #Hfs, #HfL⟩
  icases isFieldList_val $$ Hg with ⟨%gs, #Hgs, #HgL⟩
  ihave %Hfl := isFieldsL_length $$ HfL
  ihave %Hgl := isFieldsL_length $$ HgL
  ihave %Hfsl := ownSlice_len $$ Hfs
  ihave %Hgsl := ownSlice_len $$ Hgs
  wp_auto
  ihave HI : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ fl.length ∧
      sint.nat j ≤ gl.length ∧
      flCompare fl gl = flCompare (fl.drop (sint.nat j)) (gl.drop (sint.nat j))⌝ : IProp GF) $$ [i]
  · iexists _; iframe; ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    refine ⟨by word, ?_, ?_, ?_⟩ <;> rw [h0] <;> simp
  wp_for HI
  obtain ⟨hj0, hjf, hjg, hc⟩ := Hj
  have hfz : sint.nat f.len = fl.length := by rw [← Hfl, Hfsl.1]
  have hgz : sint.nat g.len = gl.length := by rw [← Hgl, Hgsl.1]
  have hjz : (sint.nat j : Int) = sint.Z j := by word
  have hfz2 : (sint.nat f.len : Int) = sint.Z f.len := by word
  have hgz2 : (sint.nat g.len : Int) = sint.Z g.len := by word
  wp_if_destruct
  · have hA := Hif
    have hjF : sint.nat j = fl.length := by omega
    wp_if_destruct
    · have hjG : sint.nat j = gl.length := by omega
      wp_for_post
      iapply HΦ
      ipureintro
      rw [hc, show fl.drop (sint.nat j) = [] by simp; omega,
        show gl.drop (sint.nat j) = [] by simp; omega]
      rfl
    · have hne : gl.drop (sint.nat j) ≠ [] := by simp; omega
      wp_if_destruct
      · wp_for_post
        iapply HΦ
        ipureintro
        rw [hc, show fl.drop (sint.nat j) = [] by simp; omega, flCompare_nil_left _ hne]
        rfl
      · exact absurd hA Hif
  · have hB := Hif
    have hneF : fl.drop (sint.nat j) ≠ [] := by simp; omega
    wp_if_destruct
    · exact absurd Hif hB
    · wp_if_destruct
      · wp_for_post
        iapply HΦ
        ipureintro
        rw [hc, show gl.drop (sint.nat j) = [] by simp; omega, flCompare_nil_right _ hneF]
        rfl
      · have hC := Hif
        have hjn : sint.nat j < fs.length := by omega
        have hjn' : sint.nat j < gs.length := by omega
        have hjfl : sint.nat j < fl.length := by omega
        have hjgl : sint.nat j < gl.length := by omega
        list_elem fs (sint.nat j) as x
        list_elem gs (sint.nat j) as y
        have hjf : sint.Z j < sint.Z f.len := by omega
        have hjg : sint.Z j < sint.Z g.len := by omega
        ihave ⟨#Hx, -⟩ := ownSlice_elem_acc (sint.Z j) x f DFrac.discard fs hj0 Hx_lookup $$ Hfs
        ihave ⟨#Hy, -⟩ := ownSlice_elem_acc (sint.Z j) y g DFrac.discard gs hj0 Hy_lookup $$ Hgs
        icases (value.Field.Field_access_load_Name _ x DFrac.discard).access_strict $$ Hx with ⟨#Hxn, -⟩
        icases (value.Field.Field_access_load_Name _ y DFrac.discard).access_strict $$ Hy with ⟨#Hyn, -⟩
        icases (value.Field.Field_access_load_Value _ x DFrac.discard).access_strict $$ Hx with ⟨#Hxv, -⟩
        icases (value.Field.Field_access_load_Value _ y DFrac.discard).access_strict $$ Hy with ⟨#Hyv, -⟩
        have he1 : fl[sint.nat j]? = some (fl[sint.nat j]'hjfl) := List.getElem?_eq_getElem hjfl
        have he2 : gl[sint.nat j]? = some (gl[sint.nat j]'hjgl) := List.getElem?_eq_getElem hjgl
        have hd1 : fl.drop (sint.nat j) = fl[sint.nat j]'hjfl :: fl.drop (sint.nat j + 1) :=
          List.drop_eq_getElem_cons hjfl
        have hd2 : gl.drop (sint.nat j) = gl[sint.nat j]'hjgl :: gl.drop (sint.nat j + 1) :=
          List.drop_eq_getElem_cons hjgl
        generalize fl[sint.nat j]'hjfl = e1 at he1 hd1
        generalize gl[sint.nat j]'hjgl = e2 at he2 hd2
        obtain ⟨n1, v1⟩ := e1
        obtain ⟨n2, v2⟩ := e2
        ihave ⟨%x', %hx', #Hxval⟩ := isFieldsL_lookup fs fl (sint.nat j) n1 v1 he1 $$ HfL
        ihave ⟨%y', %hy', #Hyval⟩ := isFieldsL_lookup gs gl (sint.nat j) n2 v2 he2 $$ HgL
        rw [Hx_lookup] at hx'
        rw [Hy_lookup] at hy'
        obtain ⟨hxx, hn1⟩ := hx'
        obtain ⟨hyy, hn2⟩ := hy'
        cases hxx; cases hyy
        simp only [hj0, hjf, hjg, _root_.and_self, ↓reduceIte]
        wp_auto
        simp only [hj0, hjf, hjg, _root_.and_self, ↓reduceIte]
        wp_auto
        have hgs := ValuePure.compareResult_gs x.Name' y.Name'
        rw [hn1, hn2] at hgs
        wp_apply h_strings_Compare
        wp_if_destruct
        · have hc0 : gsCompare n1 n2 = 0 := by rw [← hgs, ← hn1, ← hn2, Hif]; rfl
          simp only [hj0, hjf, hjg, _root_.and_self, ↓reduceIte]
          wp_auto
          simp only [hj0, hjf, hjg, _root_.and_self, ↓reduceIte]
          wp_auto
          wp_apply (h_Compare _ _ DFrac.discard DFrac.discard v1 v2) $$ [$Hxval $Hyval] as %r ⟨-, -, %hr⟩
          wp_if_destruct
          · wp_for_post
            iframe
            iexists j + 1
            iframe
            ipureintro
            have hj1 : sint.nat (j + 1) = sint.nat j + 1 := by word
            refine ⟨by word, by omega, by omega, ?_⟩
            rw [hj1, hc, hd1, hd2]
            have : UVal.compare v1 v2 = 0 := by rw [← hr]; rfl
            simp [flCompare, hc0, this]
          · wp_for_post
            iapply HΦ
            ipureintro
            rw [hc, hd1, hd2]
            have : UVal.compare v1 v2 ≠ 0 := by rw [← hr]; intro h0; apply Hif; word
            simp [flCompare, hc0, hr, this]
        · wp_for_post
          iapply HΦ
          ipureintro
          rw [hc, hd1, hd2, hn1, hn2, hgs]
          have : gsCompare n1 n2 ≠ 0 := by
            rw [← hgs]; intro h0; apply Hif; rw [hn1, hn2]; word
          simp [flCompare, this]

end proof

end smd
end EtcdGrove
end Perennial
