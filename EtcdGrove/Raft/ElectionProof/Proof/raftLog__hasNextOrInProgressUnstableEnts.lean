/- Port of election_proof/proof_raftLog__hasNextOrInProgressUnstableEnts.v (857d09190). -/
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__hasNextOrInProgressUnstableEnts

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftLog.hasNextOrInProgressUnstableEnts.wp_proof :
    raftLog.hasNextOrInProgressUnstableEnts.spec (GF := GF) (hG := hG) := by
  intro l ls
  obtain ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ := ls
  wp_start as H
  iNamed H
  icases (ownRaftLog_unfold l prev sents uents lcm lap snap lip lapg lpend lasz lamx).1 $$ Hlog
    with ⟨%lv, Hl, %Hcm, %Hap, %Hapg, %Hip, %Hasz, %Hamx, Hcore⟩
  unfold ownRaftLogCore
  icases Hcore with ⟨%sprev, %stored, %ss, Hcore⟩
  iNamed Hcore
  ihave %Hlen := ownSlice_len $$ Huents
  wp_auto
  iapply HΦ
  isplitl
  · reseal_raftLog
  ipureintro
  cases uents with
  | nil =>
    simp only [List.length_nil] at Hlen
    rw [decide_eq_false (by word), decide_eq_false (by simp)]
  | cons e es =>
    simp only [List.length_cons] at Hlen
    rw [decide_eq_true (by word), decide_eq_true (by simp)]

end proof

end EtcdGrove
end Perennial
