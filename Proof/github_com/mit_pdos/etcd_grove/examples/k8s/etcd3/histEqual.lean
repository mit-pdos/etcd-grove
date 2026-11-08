module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histLen
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeEqual

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

theorem histEqual.wp_proof
    (wp_histLen : histLen.spec (GF := GF) (hG := hG))
    (wp_storeEqual : storeEqual.spec (GF := GF) (hG := hG)) :
    histEqual.spec (GF := GF) (hG := hG) := by
  intro a b ha hb
  wp_start as ⟨#Ha, #Hb, %Hl⟩
  wp_auto
  sorry

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
