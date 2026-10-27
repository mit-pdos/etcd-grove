module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.encodeV0
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.encodeWith

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem encodeV0.wp_proof (wp_encodeWith : encodeWith.spec (GF := GF) (hG := hG)) :
    encodeV0.spec (GF := GF) (hG := hG) := by
  intro name val
  wp_start
  wp_auto
  wp_apply wp_encodeWith as %sl Hsl
  iapply HΦ
  iexact Hsl

end proof

end k8setcd3
end EtcdGrove
end Perennial
