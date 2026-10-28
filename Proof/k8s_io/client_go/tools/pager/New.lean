/-
Proof of `Spec/k8s_io/client_go/tools/pager/New.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.pager.New

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

theorem New.wp_proof : New.spec (GF := GF) (hG := hG) := by
  intro fn
  wp_start
  wp_auto
  wp_apply wp_alloc as %l Hl
  (try wp_auto)
  iapply HΦ
  iexact Hl

end proof

end pager
end EtcdGrove
end Perennial
