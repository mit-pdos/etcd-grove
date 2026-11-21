/- The regular acknowledgements needed by one half of a witness configuration. -/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.witnessIndex
public import RaftWitness.Spec.go_etcd_io.raft.v3.quorum.MajorityConfig__CommittedIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem tracker.witnessIndex.wp_proof
    (wp_oltq : quorum.MajorityConfig.OneLessThanQuorum.spec (GF := GF) (hG := hG))
    (wp_commit : quorum.MajorityConfig.CommittedIndex.spec (GF := GF) (hG := hG)) :
    tracker.witnessIndex.spec (GF := GF) (hG := hG) := by
  intro s m l P acked selected
  wp_start as ⟨%Hsz, Hv, #Hi, HP⟩
  ihave Hv := ownIdsetQ_toMaj _ _ $$ Hv
  cases selected
  · wp_auto
    wp_apply wp_commit s _ m l P acked $$ [$voters $Hv $Hi $HP] as %N ⟨-, Hv, HP, -, %HN⟩
    · ipureintro; exact Hsz
    iapply HΦ
    ihave Hv := ownIdsetQ_ofMaj _ _ $$ Hv
    iframe Hv HP
    ipureintro; exact CountGe.of_committed HN
  · wp_auto
    wp_apply wp_oltq s _ m l P acked $$ [$voters $Hv $Hi $HP] as %N ⟨-, Hv, HP, -, %H2, %H3⟩
    · ipureintro; exact Hsz
    iapply HΦ
    ihave Hv := ownIdsetQ_ofMaj _ _ $$ Hv
    iframe Hv HP
    ipureintro; exact CountGe.of_oltq H2 H3

end proof

end EtcdGrove
end Perennial
