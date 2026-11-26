/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__saveDisk.lean`: the node is
not dead (`emitOk`), so the write goes to its disk (`disk.save`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__saveDisk
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.disk__save

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
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem node.saveDisk.wp_proof (wp_save : disk.save.spec (GF := GF) (hG := hG)) :
    node.saveDisk.spec (GF := GF) (hG := hG) := by
  intro c γ n j d w hp oh sl els es hok
  wp_start as ⟨#Hc, #Hn, #Hd, Hok, Hdisk, Hhs, #Hsl, #Hents⟩
  iunfold emitOk at Hok
  icases Hok with ⟨Hdead, Hfuse⟩
  wp_auto
  wp_apply wp_save d w hp oh sl els es hok $$ [$Hpkg $Hdisk $Hhs $Hsl $Hents] as Hdisk
  try wp_auto
  iapply HΦ
  iframe Hdisk
  iunfold emitOk
  iframe

end proof

end AntHarness
end EtcdGrove
end Perennial
