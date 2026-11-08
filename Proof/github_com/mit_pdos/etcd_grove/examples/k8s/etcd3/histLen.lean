module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histLen

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

theorem histLen.wp_proof :
    histLen.spec (GF := GF) (hG := hG) := by
  intro h hs
  wp_start as #Hh
  rcases List.eq_nil_or_concat hs with rfl | ⟨hs', s, he⟩
  · icases (histOwn_nil h).1 $$ Hh with %Hn
    subst Hn
    wp_auto
    iapply HΦ; itrivial
  · rw [List.concat_eq_append] at he; subst he
    icases (histOwn_snoc h hs' s).1 $$ Hh with ⟨%hn, #Hp, #Hs, %Hn, #Hr⟩
    icases (typedPointsto_not_null _ _ _) $$ Hp with %Hnn
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    iStructNamed Hp
    wp_auto
    rw [Hn, List.length_append, List.length_singleton]
    iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
