module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.appendHist
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

theorem appendHist.wp_proof
    (wp_histLen : histLen.spec (GF := GF) (hG := hG)) :
    appendHist.spec (GF := GF) (hG := hG) := by
  intro h hs s g
  wp_start as ⟨#Hh, #Hs⟩
  wp_auto
  wp_apply wp_histLen $$ [$Hh]
  iapply wp_fupd
  wp_auto
  rename_i hp
  ipersist «$r0»
  imodintro
  iapply HΦ
  iapply (histOwn_snoc hp hs g).2
  iexists _
  iframe
  ipureintro
  simp only
  word

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
