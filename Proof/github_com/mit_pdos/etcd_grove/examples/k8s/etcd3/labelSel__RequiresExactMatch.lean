module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.labelSel__RequiresExactMatch

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

theorem labelSel.RequiresExactMatch.wp_proof :
    labelSel.RequiresExactMatch.spec (GF := GF) (hG := hG) := by
  intro s l
  wp_start
  wp_auto
  cases ha : s.all'
  · (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      isimp at HΦ
      iapply HΦ; itrivial
    · (try wp_auto)
      isimp [Hif] at HΦ
      iapply HΦ; itrivial
  · (try wp_auto)
    isimp at HΦ
    iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
