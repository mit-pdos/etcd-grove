/-
`fieldpath.versionedSet.Applied`: a projection of the `versionedSet` struct.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Applied
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
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

theorem fieldpath.versionedSet.Applied.wp_proof :
    fieldpath.versionedSet.Applied.spec (GF := GF) := fun v e => by
  wp_start as Hv
  unfold isVSet
  iNamed Hv
  icases Hv with ⟨%Heq, Hs⟩
  simp only [interface_mkOk_inj, true_and] at Heq
  have Heq := fpL.versionedSet_inj (package_sem := package_sem) Heq
  subst Heq
  wp_auto
  wp_end

end proof

end smd
end EtcdGrove
end Perennial
