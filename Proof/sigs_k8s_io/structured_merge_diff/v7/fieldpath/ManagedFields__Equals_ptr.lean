/-
`fieldpath.ManagedFields.Equals_ptr`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.ManagedFields__Equals_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.ManagedFields__Equals
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

theorem fieldpath.ManagedFields.Equals_ptr.wp_proof
    (h_ManagedFields_Equals : fieldpath.ManagedFields.Equals.spec (GF := GF)) :
    fieldpath.ManagedFields.Equals_ptr.spec (GF := GF) := fun p dq m1 m2 a b => by
  wp_start as ⟨Hp, #Ha, #Hb⟩
  wp_auto
  wp_apply (h_ManagedFields_Equals m1 m2 a b) $$ [$Ha $Hb] as %r %hr
  wp_end

end proof

end smd
end EtcdGrove
end Perennial
