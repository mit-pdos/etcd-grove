/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.raft__pastElectionTimeout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raft.pastElectionTimeout.wp_proof :
    raft.pastElectionTimeout.spec (GF := GF) (hG := hG) := by
  intro c r id s
  wp_start as Hphys
  wp_auto
  wp_apply raft.wp_load_electionElapsedC $$ Hphys as %v1 Hphys
  wp_apply raft.wp_load_randomizedElectionTimeoutC $$ Hphys as %v2 Hphys
  iapply HΦ $$ Hphys

end proof

end EtcdGrove
end Perennial
