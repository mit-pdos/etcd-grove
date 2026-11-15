module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.workloadApps

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem workloadApps.wp_proof : workloadApps.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal (l := wapD)
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hs, Hc⟩
  wp_auto
  iapply HΦ
  iframe

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
