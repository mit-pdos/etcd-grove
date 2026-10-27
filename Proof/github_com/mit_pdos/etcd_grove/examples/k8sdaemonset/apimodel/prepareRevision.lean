/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/prepareRevision.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.prepareRevision

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem prepareRevision.wp_proof : prepareRevision.spec (GF := GF) (hG := hG) := by
  intro x o
  wp_start as ⟨Hx, %Hr⟩
  wp_auto
  iapply HΦ
  cases o <;> simp only [Obj.res] at Hr <;> first | exact absurd Hr (by decide) | (unfold prepareD; iexact Hx)

end proof

end apimodel
end EtcdGrove
end Perennial
