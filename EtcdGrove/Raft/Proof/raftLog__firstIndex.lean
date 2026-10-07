/-
Port of election_proof/proof_raftLog__firstIndex.v.
-/
import EtcdGrove.Raft.Spec.raftLog__firstIndex
import EtcdGrove.Raft.Spec.unstable__maybeFirstIndex

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

/-- Two exits: a pending snapshot answers from `unstable.maybeFirstIndex`
(`prev` is the snapshot's id, `LogStoreOk`); otherwise
`Storage.FirstIndex`, whose boundary is `prev`. -/
theorem raftLog.firstIndex.wp_proof
    (wp_unstable_maybeFirstIndex : unstable.maybeFirstIndex.spec (GF := GF) (hG := hG)) :
    raftLog.firstIndex.spec (GF := GF) (hG := hG) := by
  intro l ls
  obtain ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ := ls
  wp_start as H
  iNamed H
  icases (ownRaftLog_unfold l prev sents uents lcm lap snap lip lapg lpend lasz lamx).1 $$ Hlog with ⟨%lv, Hl, %Hcm, %Hap, %Hapg, %Hip, %Hasz, %Hamx, Hcore⟩
  unfold ownRaftLogCore
  iNamed Hcore
  wp_auto
  ihave #Hsto : isStorageWith (ownStorage lv.storage') lv.storage' $$ [HisStorage]
  · unfold isStorage; iexact HisStorage
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  split_unstable l lv
  wp_apply wp_unstable_maybeFirstIndex _ _ uents snap $$ [Huf Huents Huents_cap]
    as %fi %ok ⟨Hun, %Hok⟩
  · unfold ownUnstable
    simp only [named]
    iframe # ∗
  unfold ownUnstable
  icases Hun with ⟨Huf, Huents_cap, Huents⟩
  ihave Hl := Hlback $$ Huf
  obtain ⟨rfl, Hfi⟩ := Hok
  cases snap with
  | some sid =>
    rw [decide_eq_true (by simp)]
    wp_auto
    iapply HΦ
    have Hsid : prev = sid := Hstore.1
    isplitl
    · reseal_raftLog
    ipureintro
    obtain ⟨-, -, -, Hlt⟩ := Hstore
    rw [Hfi sid rfl, Hsid]
    have := word.unsigned_range sid.index'
    word
  | none =>
    rw [decide_eq_false (by simp)]
    wp_auto
    rw [Hstok]
    wp_auto
    have Hsp : sprev = prev := Hstore.1
    wp_apply HFirstIndex $$ HStorage as %fi2 ⟨%Hfi2, HStorage⟩
    rw [← Hstok]
    iapply HΦ
    isplitl
    · reseal_raftLog
    ipureintro
    rw [Hsp] at Hfi2
    exact Hfi2

end proof

end EtcdGrove
end Perennial
