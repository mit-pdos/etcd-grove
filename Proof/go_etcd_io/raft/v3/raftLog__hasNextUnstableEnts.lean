/- Port of election_proof/proof_raftLog__hasNextUnstableEnts.v (857d09190). -/
module

public import Spec.go_etcd_io.raft.v3.raftLog__hasNextUnstableEnts
public import Spec.go_etcd_io.raft.v3.raftLog__nextUnstableEnts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftLog.hasNextUnstableEnts.wp_proof
    (wp_raftLog_nextUnstableEnts : raftLog.nextUnstableEnts.spec (GF := GF) (hG := hG)) :
    raftLog.hasNextUnstableEnts.spec (GF := GF) (hG := hG) := by
  intro l ls
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_raftLog_nextUnstableEnts l ls $$ [Hlog] as %s ⟨Hlog, #Hs⟩
  · iexact Hlog
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  iapply HΦ
  iframe Hlog
  ipureintro
  cases He : nextUnstable ls with
  | nil =>
    rw [He] at Hlen
    simp only [List.length_nil] at Hlen
    rw [decide_eq_false (by word), decide_eq_false (by simp)]
  | cons e es =>
    rw [He] at Hlen
    simp only [List.length_cons] at Hlen
    rw [decide_eq_true (by word), decide_eq_true (by simp)]

end proof

end EtcdGrove
end Perennial
