/-
`fieldpath.PathElement.Equals`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.FieldList__Equals
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

theorem fieldpath.PathElement.Equals.wp_proof
    (h_Equals : value.Equals.spec (GF := GF))
    (h_FieldList_Equals : value.FieldList.Equals.spec (GF := GF)) :
    fieldpath.PathElement.Equals.spec (GF := GF) := fun e e' a b => by
  wp_start as ⟨#Ha, #Hb⟩
  ihave %na := fpL.isPE_null e a $$ Ha
  ihave %nb := fpL.isPE_null e' b $$ Hb
  wp_auto
  cases a <;> cases b <;> simp only at na nb <;> unfold isPE
  case field.field n n' =>
    pe_if; pe_if
    wp_end
  case key.key fl fl' =>
    icases Ha with ⟨-, %s, Hs, Hfl⟩
    icases Hb with ⟨-, %s', Hs', Hfl'⟩
    pe_if; pe_if; pe_if; pe_if
    wp_method_call; wp_call; wp_auto
    wp_apply (h_FieldList_Equals s s' fl fl') $$ [$Hfl $Hfl'] as %r %hr
    wp_end
  case value.value x x' =>
    icases Ha with ⟨-, %v, Hs, Hv⟩
    icases Hb with ⟨-, %v', Hs', Hv'⟩
    pe_if; pe_if; pe_if; pe_if; pe_if; pe_if
    wp_apply (h_Equals v v' DFrac.discard DFrac.discard x x') $$ [$Hv $Hv'] as %r ⟨-, -, %hr⟩
    wp_end
  case index.index i i' =>
    icases Ha with ⟨-, Hs⟩
    icases Hb with ⟨-, Hs'⟩
    pe_if; pe_if; pe_if; pe_if; pe_if; pe_if; pe_if; pe_if
    wp_end
  all_goals
    repeat pe_if
    wp_end
  all_goals (ipureintro; simp)

end proof

end smd
end EtcdGrove
end Perennial
