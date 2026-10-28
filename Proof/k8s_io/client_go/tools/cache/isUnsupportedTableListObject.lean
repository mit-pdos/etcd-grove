/-
Proof of `Spec/k8s_io/client_go/tools/cache/isUnsupportedTableListObject.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.isUnsupportedTableListObject

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache apimodel

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem isUnsupportedTableListObject.wp_proof :
    isUnsupportedTableListObject.spec (GF := GF) (hG := hG) := by
  intro res q
  wp_start
  cases res <;> simp only [resListTy] <;> wp_auto <;> (iapply HΦ; itrivial)

end proof

end cache
end EtcdGrove
end Perennial
