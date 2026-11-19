/-
`typed.toFieldSetWalker.toFieldSet`: a member of the recursion cluster `typed.toFieldSetWalkerRec` (`toFieldSetWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `toFieldSetWalker__toFieldSetBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__toFieldSetBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.resolveSchema
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__doScalar

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
variable [package_sem : typed.Assumptions]

theorem typed.toFieldSetWalker.toFieldSet.wp_proofBody
    (h_resolveSchema : typed.resolveSchema.spec (GF := GF))
    (h_toFieldSetWalker_doScalar : typed.toFieldSetWalker.doScalar.spec (GF := GF)) :
    typed.toFieldSetWalker.toFieldSet.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
