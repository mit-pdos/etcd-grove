module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.encodeObj
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.encodeWith

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

theorem encodeObj.wp_proof (wp_encodeWith : encodeWith.spec (GF := GF) (hG := hG)) :
    encodeObj.spec (GF := GF) (hG := hG) := by
  intro p dq name val rv
  wp_start as Hp
  icases (typedPointsto_not_null_dup _ _ _) $$ Hp with ⟨Hp, %Hpn⟩
  iStructNamed Hp
  (try wp_auto)
  wp_apply wp_encodeWith as %sl Hsl
  iapply HΦ
  iframe Hsl
  iapply typedPointsto_combine p _ dq Hpn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end k8setcd3
end EtcdGrove
end Perennial
