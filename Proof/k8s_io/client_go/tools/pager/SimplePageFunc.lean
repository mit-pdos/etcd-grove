/-
Proof of `Spec/k8s_io/client_go/tools/pager/SimplePageFunc.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.pager.SimplePageFunc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace pager

open Iris Iris.BI Iris.ProofMode apimodel cache k8s_io.client_go.tools.pager

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.pager.Assumptions]

theorem SimplePageFunc.wp_proof : SimplePageFunc.spec (GF := GF) (hG := hG) := by
  intro fn res S
  wp_start as #Hfn
  iapply wp_fupd
  wp_auto
  irename «fn» => Hcell
  ipersist Hcell
  imodintro
  simp only [recv_eq_func_mk]
  iapply HΦ
  unfold pfnOk
  imodintro
  iintro %ctx %opts %dq %lo %Φ' Hlo HΦ'
  wp_auto
  iunfold fnOk at Hfn
  wp_apply Hfn $$ [$Hlo] as %obj %err Hlo Hres
  (try wp_auto)
  iapply HΦ' $$ Hlo Hres

end proof

end pager
end EtcdGrove
end Perennial
