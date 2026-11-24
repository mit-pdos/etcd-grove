/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__isolate.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__isolate
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

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

variable [sync_sem : sync.Assumptions]

theorem Cluster.isolate.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    Cluster.isolate.spec (GF := GF) (hG := hG) := by
  intro c ns N id
  wp_start as #Hc
  iunfold clusterRO at Hc
  icases Hc with ⟨%nsl, #Hn, #Hns, #HN, #Hm⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Lock $$ [$Hsync $Hm] as ⟨Hlocked, Hinv⟩
  icases Hinv with ⟨%x, Hx⟩
  wp_auto
  wp_apply wp_Unlock _ iprop(∃ x : w64, c.[H.Cluster, go!"isolated"] ↦ x) $$ [$Hsync $Hm $Hlocked Hx]
  · iexists id; iframe
  try wp_auto
  iapply HΦ
  ipureintro; trivial

end proof

end AntHarness
end EtcdGrove
end Perennial
