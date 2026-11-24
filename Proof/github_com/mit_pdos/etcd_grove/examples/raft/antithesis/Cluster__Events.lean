/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__Events.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__Events
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Recorder__Events

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]


theorem Cluster.Events.wp_proof (wp_Events : Recorder.Events.spec (GF := GF) (hG := hG)) :
    Cluster.Events.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as Hrun
  iunfold runOver at Hrun
  icases Hrun with ⟨%r, %γr, %evs, #Hr, #Hrec, Hdone, #HN, %Hacc⟩
  wp_auto
  wp_apply wp_Events γr r evs $$ [$Hpkg $Hrec $Hdone] as %sl ⟨#Hsl, -⟩
  try wp_auto
  iapply HΦ
  iexists evs
  iframe Hsl
  ipureintro; exact Hacc

end proof

end AntHarness
end EtcdGrove
end Perennial
