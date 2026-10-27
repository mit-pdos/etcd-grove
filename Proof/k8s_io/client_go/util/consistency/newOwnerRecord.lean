/-
Proof of `Spec/k8s_io/client_go/util/consistency/newOwnerRecord.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.consistency.newOwnerRecord

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

theorem newOwnerRecord.wp_proof : newOwnerRecord.spec (GF := GF) (hG := hG) := by
  intro uid
  wp_start
  wp_auto
  wp_apply wp_map_make1 (K := GR) (V := GoString)
    k8s_io.apimachinery.pkg.runtime.schema.GroupResource.ty go.string as %vm Hvm
  wp_alloc r as Hr
  wp_auto
  ihave %Hnn := typedPointsto_not_null $$ Hr
  iStructNamed Hr
  iapply HΦ
  iexists vm
  iframe
  ipureintro; exact Hnn

end proof

end consistency
end EtcdGrove
end Perennial
