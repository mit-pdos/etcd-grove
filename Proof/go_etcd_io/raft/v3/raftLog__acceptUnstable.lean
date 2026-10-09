/- Port of election_proof/proof_raftLog__acceptUnstable.v (857d09190). -/
module

public import Spec.go_etcd_io.raft.v3.raftLog__acceptUnstable
public import Spec.go_etcd_io.raft.v3.unstable__acceptInProgress

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

theorem raftLog.acceptUnstable.wp_proof
    (wp_unstable_acceptInProgress : unstable.acceptInProgress.spec (GF := GF) (hG := hG)) :
    raftLog.acceptUnstable.spec (GF := GF) (hG := hG) := by
  intro l ls Hpend
  obtain ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ := ls
  simp only at Hpend
  subst lpend
  wp_start as H
  iNamed H
  icases (ownRaftLog_unfold l prev sents uents lcm lap snap lip lapg [] lasz lamx).1 $$ Hlog
    with ⟨%lv, Hl, %Hcm, %Hap, %Hapg, %Hip, %Hasz, %Hamx, Hcore⟩
  unfold ownRaftLogCore
  icases Hcore with ⟨%sprev, %stored, %ss, Hcore⟩
  iNamed Hcore
  wp_auto
  icases raftLog_split_unstable l lv $$ Hl with ⟨Huf, Hlback⟩
  have Hcontig : ∀ (k : Nat) (e : raftpb.Entry), uents[k]? = some e →
      uint.Z e.Index' = uint.Z lv.unstable'.offset' + (k : Int) := by
    intro k e Hk
    have Hk' : (sents ++ uents)[sents.length + k]? = some e := by
      rw [List.getElem?_append_right (by omega)]
      simpa using Hk
    have := Hidx _ _ Hk'
    push_cast at this
    omega
  have Hnw' : uint.Z lv.unstable'.offset' + (uents.length : Int) < 2^64 := by omega
  wp_apply wp_unstable_acceptInProgress _ _ _ Hcontig Hnw' $$ [Huf Huents Huents_cap]
    as %uv' ⟨Hun, %Huv'⟩
  · unfold ownUnstable
    simp only [named]
    iframe # ∗
  obtain ⟨Hent', Hoff', Hsnap', Hlg', Hip0, Hip1⟩ := Huv'
  unfold ownUnstable
  icases Hun with ⟨Hu, Huents_cap, Huents⟩
  ihave Hl := Hlback $$ Hu
  iapply HΦ
  rw [← Hlg'] at *
  rw [← Hsnap'] at *
  rw [← Hent'] at *
  -- the new `offsetInProgress` is the end of the log
  have Hend : uint.Z uv'.offsetInProgress'
      = uint.Z lv.unstable'.offset' + (uents.length : Int) := by
    by_cases He : uents = []
    · rw [Hip0 He]; subst uents; simp only [List.length_nil] at Hipb ⊢; omega
    · exact Hip1 He
  simp only [logAcceptUnstable]
  reseal_raftLog
  · dsimp only; rw [Hoff']; exact Hoffset
  · dsimp only
    simp only [logEnd, logLast]
    word
  · dsimp only; rw [Hoff']; omega
  · dsimp only
    rw [Hoff']
    intro Hs
    subst Hs
    obtain ⟨Hsp, -, -⟩ := Hstore
    have Hp := Hpersist rfl
    rw [show uint.Z uv'.offsetInProgress' - uint.Z lv.unstable'.offset' = (uents.length : Int)
      by omega]
    simp only [nextUnstable, logOffset]
    rw [← Hip, ← Hoffset]
    exact persist_accept prev sprev stored sents uents _ Hidx Hsp (by omega) Hp

end proof

end EtcdGrove
end Perennial
