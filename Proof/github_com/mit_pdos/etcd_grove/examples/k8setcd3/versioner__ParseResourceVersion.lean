module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner__ParseResourceVersion
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.parseRV

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

theorem versioner.ParseResourceVersion.wp_proof (wp_parseRV : parseRV.spec (GF := GF) (hG := hG)) :
    versioner.ParseResourceVersion.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  (try wp_auto)
  wp_apply wp_parseRV as %n %err Hr
  iapply HΦ
  iexact Hr

end proof

end k8setcd3
end EtcdGrove
end Perennial
