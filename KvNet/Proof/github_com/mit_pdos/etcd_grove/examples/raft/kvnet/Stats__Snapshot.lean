/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/Stats__Snapshot.lean`. Lean-first (no Rocq
counterpart): the counters' array loaded under the mutex.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats__Snapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem Stats.Snapshot.wp_proof : Stats.Snapshot.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as #Hs
  unfold isStats
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hs] as ⟨Hlocked, HL⟩
  unfold statsInv
  icases HL with ⟨%a, Ha⟩
  ihave %Hlen := array_len _ _ _ _ $$ Ha
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hs $Hlocked Ha]
  · inext; iexists _; iexact Ha
  try wp_auto
  iapply HΦ
  ipureintro; omega

end proof

end raft_kvnet
end EtcdGrove
end Perennial
