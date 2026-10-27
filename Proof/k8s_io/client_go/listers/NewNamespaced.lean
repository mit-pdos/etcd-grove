/-
Proof of `Spec/k8s_io/client_go/listers/NewNamespaced.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.listers.NewNamespaced

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace listers

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.listers

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.Assumptions]

theorem NewNamespaced.wp_proof : NewNamespaced.spec (GF := GF) (hG := hG) := by
  intro X p ns
  wp_start
  (try wp_auto)
  iapply HΦ
  all_goals (try itrivial)

end proof

end listers
end EtcdGrove
end Perennial
