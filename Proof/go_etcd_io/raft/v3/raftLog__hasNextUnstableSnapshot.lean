/- Port of election_proof/proof_raftLog__hasNextUnstableSnapshot.v (857d09190). -/
module

public import Spec.go_etcd_io.raft.v3.raftLog__hasNextUnstableSnapshot
public import Spec.go_etcd_io.raft.v3.unstable__nextSnapshot

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

theorem raftLog.hasNextUnstableSnapshot.wp_proof
    (wp_unstable_nextSnapshot : unstable.nextSnapshot.spec (GF := GF) (hG := hG)) :
    raftLog.hasNextUnstableSnapshot.spec (GF := GF) (hG := hG) := by
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
  wp_apply wp_unstable_nextSnapshot _
      ⟨uents, lv.unstable'.offset', lv.unstable'.offsetInProgress', snap⟩
      $$ [Huf Huents Huents_cap] as %p ⟨Hun, %Hp⟩
  · close_unstable_log
  reopen_unstable
  iapply HΦ
  isplitl
  · reseal_raftLog
  ipureintro
  intro Hs
  rw [Hp Hs]
  simp

end proof

end EtcdGrove
end Perennial
