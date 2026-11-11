/- Lean-first (no Rocq counterpart). Proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/versioner__UpdateList.lean`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__UpdateList

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem versioner.UpdateList.wp_proof : versioner.UpdateList.spec (GF := GF) (hG := hG) := by
  intro pl os rv rv' cont cont' rem remV rem0
  wp_start as ⟨Hl, Hrem⟩
  unfold ListSpec.listAtItems driverListSpec metaAtD at *
  icases Hl with ⟨%Hpl, %s, Hit, Hits, Hrv, Hcont, %r, Hr, -⟩
  wp_auto
  iapply HΦ
  try unfold ListSpec.listAtItems driverListSpec metaAtD
  simp only
  iframe
  ipureintro; exact Hpl

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
