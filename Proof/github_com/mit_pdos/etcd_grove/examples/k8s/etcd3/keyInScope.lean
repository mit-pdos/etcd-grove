module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.keyInScope
public import Spec.strings.TrimSuffix

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

theorem keyInScope.wp_proof
    (wp_Trim : strings.TrimSuffix.spec (GF := GF) (hG := hG)) :
    keyInScope.spec (GF := GF) (hG := hG) := by
  intro key r k
  wp_start as -
  wp_auto
  cases r
  · (try wp_auto)
    rw [show keyInScopeL key false k = decide (k = key) from rfl]
    iapply HΦ; itrivial
  · (try wp_auto)
    wp_apply wp_Trim
    (try wp_auto)
    wp_apply _root_.Perennial.strings.wp_HasPrefix
    (try wp_auto)
    rw [show keyInScopeL key true k = _ from if_pos rfl, trimSufL]
    iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
