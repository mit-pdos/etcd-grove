module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.identity__TransformToStorage


@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem identity.TransformToStorage.wp_proof  :
    identity.TransformToStorage.spec (GF := GF) (hG := hG) := by
  intro ctx sl dctx
  wp_start
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end k8setcd3
end EtcdGrove
end Perennial
