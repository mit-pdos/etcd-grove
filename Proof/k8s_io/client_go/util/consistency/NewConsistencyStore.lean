/-
Proof of `Spec/k8s_io/client_go/util/consistency/NewConsistencyStore.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.consistency.NewConsistencyStore
public import Spec.k8s_io.client_go.util.consistency.newConsistencyStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.consistency

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

theorem NewConsistencyStore.wp_proof
    (wp_new : newConsistencyStore.spec (GF := GF) (hG := hG)) :
    NewConsistencyStore.spec (GF := GF) (hG := hG) := by
  intro sm dq S G T
  wp_start as ⟨Hsm, #Hget, #Hexcl⟩
  wp_auto
  wp_apply (wp_new sm dq S G T) $$ [$Hsm $Hget $Hexcl] as %c ⟨%γ, H⟩
  iapply HΦ $$ H

end proof

end consistency
end EtcdGrove
end Perennial
