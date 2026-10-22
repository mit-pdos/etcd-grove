module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.notFound
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.storeKey

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem notFound.wp_proof (wp_storeKey : storeKey.spec (GF := GF) (hG := hG)) :
    notFound.spec (GF := GF) (hG := hG) := by
  intro s key
  wp_start as -
  wp_auto
  wp_apply wp_storeKey
  simp only [notFoundL, mkeyL]
  iapply HΦ
  (try ipureintro; trivial)

end proof

end k8setcd3
end EtcdGrove
end Perennial
