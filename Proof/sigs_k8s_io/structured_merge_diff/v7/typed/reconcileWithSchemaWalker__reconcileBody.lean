/-
`typed.reconcileWithSchemaWalker.reconcile`: a member of the recursion cluster `typed.reconcileWithSchemaWalkerRec` (`reconcileWithSchemaWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `reconcileWithSchemaWalker__reconcileBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__reconcileBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.handleAtom
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__doScalar

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

theorem typed.reconcileWithSchemaWalker.reconcile.wp_proofBody
    (h_Schema_Resolve : schema.Schema.Resolve.spec (GF := GF))
    (h_handleAtom : typed.handleAtom.spec (GF := GF))
    (h_reconcileWithSchemaWalker_doScalar : typed.reconcileWithSchemaWalker.doScalar.spec (GF := GF)) :
    typed.reconcileWithSchemaWalker.reconcile.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
