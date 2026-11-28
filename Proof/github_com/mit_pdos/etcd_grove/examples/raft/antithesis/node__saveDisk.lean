/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__saveDisk.lean`: the node is
not dead (`emitOk`), so the write goes to its disk (`disk.save`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__saveDisk
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.disk__save
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.SpecsB2
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessReportB2

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

/-- **`node.saveDisk.specB2`** (#33 parity B2; staged beside B1's `wp_proof`): the write when alive,
nothing when dead. -/
theorem node.saveDisk.wp_proofB2 (wp_save : disk.save.spec (GF := GF) (hG := hG)) :
    node.saveDisk.specB2 (GF := GF) (hG := hG) := by
  intro c γ n j d w hp oh sl els es dead fuse hok
  wp_start as ⟨#Hc, #Hn, #Hd, Hk, Hdisk, Hhs, #Hsl, #Hents⟩
  iunfold killOwn at Hk
  icases Hk with ⟨Hdead, Hfuse⟩
  cases dead
  · wp_auto
    wp_apply wp_save d w hp oh sl els es hok $$ [$Hpkg $Hdisk $Hhs $Hsl $Hents] as Hdisk
    try wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hdisk
    iunfold killOwn
    iframe
  · wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    iframe Hdisk
    iunfold killOwn
    iframe

end proof

end AntHarness
end EtcdGrove
end Perennial
