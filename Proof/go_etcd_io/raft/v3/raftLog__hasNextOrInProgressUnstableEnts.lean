/- Port of election_proof/proof_raftLog__hasNextOrInProgressUnstableEnts.v (857d09190). -/
module

public import Spec.go_etcd_io.raft.v3.raftLog__hasNextOrInProgressUnstableEnts

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

theorem raftLog.hasNextOrInProgressUnstableEnts.wp_proof :
    raftLog.hasNextOrInProgressUnstableEnts.spec (GF := GF) (hG := hG) := by
  intro hw l ls
  wp_start as H
  iNamed H
  iNamed Hlog
  ihave %Hlen := entsPts_len _ _ _ $$ Huents
  wp_auto
  iapply HΦ
  isplitl
  · reseal_raftLog
  ipureintro
  cases Hu : ls.uents with
  | nil =>
    rw [Hu, List.length_nil] at Hlen
    rw [decide_eq_false (by word), decide_eq_false (by simp)]
  | cons e es =>
    rw [Hu, List.length_cons] at Hlen
    rw [decide_eq_true (by word), decide_eq_true (by simp)]

end proof

end EtcdGrove
end Perennial
