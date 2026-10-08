/- Port of election_proof/proof_raftLog__nextUnstableEnts.v (857d09190). -/
import EtcdGrove.Raft.Spec.raftLog__nextUnstableEnts
import EtcdGrove.Raft.Spec.unstable__nextEntries

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

theorem raftLog.nextUnstableEnts.wp_proof
    (wp_unstable_nextEntries : unstable.nextEntries.spec (GF := GF) (hG := hG)) :
    raftLog.nextUnstableEnts.spec (GF := GF) (hG := hG) := by
  intro l ls
  obtain ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ := ls
  wp_start as H
  iNamed H
  icases (ownRaftLog_unfold l prev sents uents lcm lap snap lip lapg lpend lasz lamx).1 $$ Hlog
    with ⟨%lv, Hl, %Hcm, %Hap, %Hapg, %Hip, %Hasz, %Hamx, Hcore⟩
  unfold ownRaftLogCore
  icases Hcore with ⟨%sprev, %stored, %ss, Hcore⟩
  iNamed Hcore
  wp_auto
  icases raftLog_split_unstable l lv $$ Hl with ⟨Huf, Hlback⟩
  wp_apply wp_unstable_nextEntries _
      ⟨uents, lv.unstable'.offset', lv.unstable'.offsetInProgress', snap⟩ Hipb
      $$ [Huf Huents Huents_cap] as %s ⟨Hun, #Hs⟩
  · close_unstable_log
  reopen_unstable
  iapply HΦ
  isplitl
  · reseal_raftLog
  simp only [nextUnstable, logOffset]
  rw [← Hip, ← Hoffset]
  iexact Hs

end proof

end EtcdGrove
end Perennial
