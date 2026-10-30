/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/newTable.lean`.
Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.newTable

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem newTable.wp_proof : newTable.spec (GF := GF) (hG := hG) := by
  intro _ r empty
  wp_start as #Hemp
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := Key) (V := GoInterface)) as %m Hm
  iStructNamedSuffix «$r0» "_f"
  ipersist resource_f
  ipersist namespaced_f
  ipersist objs_f
  ipersist empty_f
  imodintro
  iapply HΦ
  unfold tableFixed tableLocked
  iframe #
  iexists ∅, slice.nil, []
  iframe
  isplitl []
  · iapply (BigSepM2.bigSepM2_empty (PROP := IProp GF) _).2; itrivial
  isplitl []
  · iapply ownSlice_nil
  isplitl []
  · iapply ownSliceCap_nil
  iapply BigSepL2.bigSepL2_nil.2; itrivial

end proof

end apimodel
end EtcdGrove
end Perennial
