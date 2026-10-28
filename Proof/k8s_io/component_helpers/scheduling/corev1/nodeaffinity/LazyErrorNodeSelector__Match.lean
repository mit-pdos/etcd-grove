/-
Proof of `Spec/k8s_io/component_helpers/scheduling/corev1/nodeaffinity/LazyErrorNodeSelector__Match.lean`,
over gap D2's body hypothesis. Lean-first.
-/
module

public import Spec.k8s_io.component_helpers.scheduling.corev1.nodeaffinity.LazyErrorNodeSelector__Match
public import Spec.k8s_io.component_helpers.scheduling.corev1.nodeaffinity.LazyErrorNodeSelector__Match_body
public import Spec.k8s_io.component_helpers.scheduling.corev1.nodeaffinity.extractNodeFields
public import Spec.k8s_io.component_helpers.scheduling.corev1.nodeaffinity.nodeSelectorTerm__match
public import Spec.k8s_io.apimachinery.pkg.util.errors.NewAggregate
public import Spec.k8s_io.apimachinery.pkg.util.errors.Flatten

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel k8s_io.component_helpers.scheduling.corev1.nodeaffinity

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.component_helpers.scheduling.corev1.nodeaffinity.Assumptions]

theorem LazyErrorNodeSelector.Match.wp_proof
    (h_body : LazyErrorNodeSelector.Match_body.spec (sem := sem))
    (wp_extractNodeFields : extractNodeFields.spec (GF := GF) (hG := hG))
    (wp_match : nodeSelectorTerm.match.spec (GF := GF) (hG := hG))
    (wp_NewAggregate : utilerrors.NewAggregate.spec (GF := GF) (hG := hG))
    (wp_Flatten : utilerrors.Flatten.spec (GF := GF) (hG := hG)) :
    LazyErrorNodeSelector.Match.spec (GF := GF) (hG := hG) := by
  haveI := h_body
  intro ns node dq d
  wp_start as ⟨#Hns, Hn⟩
  iunfold lesOk at Hns
  icases Hns with ⟨%s, %ts, #Hns, #Hs, #Hts⟩
  iunfold nodeAt at Hn
  icases Hn with ⟨%v, Hl, Hd⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
  wp_auto
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
