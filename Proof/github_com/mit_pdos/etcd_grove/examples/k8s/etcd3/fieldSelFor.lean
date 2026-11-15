module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.fieldSelFor

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem fieldSelFor.wp_proof :
    fieldSelFor.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start as -
  wp_auto
  wp_if_destruct
  · rw [show fieldSelForL x = _ from if_pos Hif]
    iapply HΦ; itrivial
  have h1 := Hif
  wp_if_destruct
  · rw [show fieldSelForL x = _ by rw [fieldSelForL, if_neg h1, if_pos Hif]]
    iapply HΦ; itrivial
  have h2 := Hif
  wp_if_destruct
  · rw [show fieldSelForL x = _ by rw [fieldSelForL, if_neg h1, if_neg h2, if_pos Hif]]
    iapply HΦ; itrivial
  have h3 := Hif
  wp_if_destruct
  · rw [show fieldSelForL x = _ by rw [fieldSelForL, if_neg h1, if_neg h2, if_neg h3, if_pos Hif]]
    iapply HΦ; itrivial
  have h4 := Hif
  wp_if_destruct
  · rw [show fieldSelForL x = _ by
      rw [fieldSelForL, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos Hif]]
    iapply HΦ; itrivial
  · rw [show fieldSelForL x = zero_val fieldSel by
      rw [fieldSelForL, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg Hif]; rfl]
    iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
