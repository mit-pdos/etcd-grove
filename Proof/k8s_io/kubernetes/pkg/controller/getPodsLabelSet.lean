/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/getPodsLabelSet.lean`. Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.getPodsLabelSet
public import Proof.k8s_io.kubernetes.pkg.controller.PodLens2

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel k8s_io.kubernetes.pkg.controller

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]

theorem getPodsLabelSet.wp_proof : getPodsLabelSet.spec (GF := GF) (hG := hG) := by
  intro tp dq t
  wp_start as Ht
  icases tmplAt_fields tp dq t $$ Ht with ⟨%vm, %vs, Hm, Hmd, Hs, Hsd, Hback⟩
  wp_auto
  rw [go.make1_underlying, (go.is_underlying :
    underlying k8s_io.apimachinery.pkg.labels.Set'.ty = _)]
  wp_apply (wp_map_make1 (K := GoString) (V := GoString)) as %c Hc
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
