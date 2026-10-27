/-
Proof of `Spec/k8s_io/client_go/tools/cache/InformerNameAndResource__Reserved.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.InformerNameAndResource__Reserved

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem InformerNameAndResource.Reserved.wp_proof :
    InformerNameAndResource.Reserved.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start as %hn
  wp_auto
  simp only [hn, _root_.decide_true]
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end cache
end EtcdGrove
end Perennial
