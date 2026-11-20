/-
`fieldpath.PathElement.Compare`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Compare
public import Perennial.Spec.strings.Compare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.Compare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.FieldList__Compare
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep

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
variable [package_sem : fieldpath.Assumptions]

/-- A branch on a field's nil-ness: the impossible side closed from the elements' shapes. -/
local macro "pe_if" : tactic => `(tactic| (wp_if_destruct <;> try (exfalso; simp_all; done)))

theorem fieldpath.PathElement.Compare.wp_proof
    (h_strings_Compare : _root_.Perennial.strings.Compare.spec (GF := GF))
    (h_Compare : value.Compare.spec (GF := GF))
    (h_FieldList_Compare : value.FieldList.Compare.spec (GF := GF)) :
    fieldpath.PathElement.Compare.spec (GF := GF) := fun e e' a b => by
  wp_start as ⟨#Ha, #Hb⟩
  ihave %na := fpL.isPE_null e a $$ Ha
  ihave %nb := fpL.isPE_null e' b $$ Hb
  wp_auto
  cases a <;> cases b <;> simp only at na nb <;> unfold isPE
  case field.field n n' =>
    icases Ha with ⟨-, Ha⟩
    icases Hb with ⟨-, Hb⟩
    pe_if; pe_if
    wp_apply h_strings_Compare
    wp_end
    ipureintro
    simp only [PE.compare]
    exact fpL.compareResult_gs n n'
  case key.key fl fl' =>
    icases Ha with ⟨%hk, %s, Hs, Hfl⟩
    icases Hb with ⟨%hk', %s', Hs', Hfl'⟩
    pe_if; pe_if; pe_if; pe_if
    wp_method_call; wp_call; wp_auto
    wp_apply (h_FieldList_Compare s s' fl fl') $$ [$Hfl $Hfl'] as %r %hr
    · iframe #; ipureintro; exact ⟨hk.2, hk'.2⟩
    wp_end
  case value.value x x' =>
    icases Ha with ⟨%hk, %v, Hs, Hv⟩
    icases Hb with ⟨%hk', %v', Hs', Hv'⟩
    pe_if; pe_if; pe_if; pe_if; pe_if; pe_if
    wp_apply (h_Compare v v' DFrac.discard DFrac.discard x x') $$ [$Hv $Hv'] as %r ⟨-, -, %hr⟩
    · iframe; ipureintro; exact ⟨hk.2.2, hk'.2.2⟩
    wp_end
  case index.index i i' =>
    icases Ha with ⟨-, Hs⟩
    icases Hb with ⟨-, Hs'⟩
    pe_if; pe_if; pe_if; pe_if; pe_if; pe_if; pe_if; pe_if
    wp_if_destruct
    · wp_end; ipureintro; simp only [PE.compare, intCompare]
      simp only [sint.Z] at Hif ⊢
      rw [if_neg (by omega), if_neg (by simp; omega)]; rfl
    wp_if_destruct
    · wp_end; ipureintro; simp only [PE.compare, intCompare]
      subst Hif
      rw [if_neg (by omega), if_pos (by simp)]; rfl
    wp_end; ipureintro; simp only [PE.compare, intCompare]
    have : i.toInt ≠ i'.toInt := fun h => Hif (BitVec.toInt_inj.1 h)
    simp only [sint.Z] at *
    rw [if_pos (by omega)]; rfl
  all_goals
    repeat pe_if
    wp_end
  all_goals (ipureintro; simp only [PE.compare]; rfl)

end proof

end smd
end EtcdGrove
end Perennial
