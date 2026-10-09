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
  wp_start as H
  iNamed H
  iNamed Hlog
  wp_auto
  lend_unstable
  wp_apply wp_unstable_nextSnapshot _ (unstableOf lv ls) $$ [$Hun] as %p ⟨Hun, %Hp⟩
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
