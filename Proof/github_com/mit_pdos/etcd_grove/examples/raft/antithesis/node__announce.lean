/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__announce.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__announce
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__emit
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem node.announce.wp_proof (wp_emit : node.emit.spec (GF := GF) (hG := hG)) :
    node.announce.spec (GF := GF) (hG := hG) := by
  intro c γ n j p ev Q
  wp_start as ⟨#Hc, #Hn, Hok, Hev, Hrep⟩
  wp_auto
  wp_apply wp_emit c γ n j p ev Q $$ [$Hpkg $Hc $Hn $Hok $Hev $Hrep] as ⟨Hok, HQ⟩
  iunfold emitOk at Hok
  icases Hok with ⟨Hdead, Hfuse⟩
  try wp_auto
  iapply HΦ
  iframe
  iunfold emitOk
  iframe

end proof

end AntHarness
end EtcdGrove
end Perennial
