/-
`typed.mergingWalker.merge`: a member of the recursion cluster `typed.mergingWalkerRec` (`mergingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `mergingWalker__mergeBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__mergeBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Atom__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationErrors__WithLazyPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.deduceAtom
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.handleAtom
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__doScalar

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

theorem typed.mergingWalker.merge.wp_proofBody
    (h_Atom_Equals : schema.Atom.Equals.spec (GF := GF))
    (h_Schema_Resolve : schema.Schema.Resolve.spec (GF := GF))
    (h_ValidationErrors_WithLazyPrefix : typed.ValidationErrors.WithLazyPrefix.spec (GF := GF))
    (h_deduceAtom : typed.deduceAtom.spec (GF := GF))
    (h_handleAtom : typed.handleAtom.spec (GF := GF))
    (h_mergingWalker_doScalar : typed.mergingWalker.doScalar.spec (GF := GF)) :
    typed.mergingWalker.merge.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
