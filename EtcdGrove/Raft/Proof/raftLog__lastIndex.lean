/-
Port of election_proof/proof_raftLog__lastIndex.v.
-/
import EtcdGrove.Raft.Spec.raftLog__lastIndex
import EtcdGrove.Raft.Spec.unstable__maybeLastIndex

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

/-- Three exits: a non-empty unstable suffix; an empty one with a pending snapshot,
whose index is `prev`'s (`LogStoreOk`); an empty one without, where
`Storage.LastIndex` is `prev.index + |stored|` and `stored = sents`. -/
theorem raftLog.lastIndex.wp_proof
    (wp_unstable_maybeLastIndex : unstable.maybeLastIndex.spec (GF := GF) (hG := hG)) :
    raftLog.lastIndex.spec (GF := GF) (hG := hG) := by
  intro l ls
  obtain ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ := ls
  wp_start as H
  iNamed H
  icases (ownRaftLog_unfold l prev sents uents lcm lap snap lip lapg lpend lasz lamx).1 $$ Hlog with ⟨%lv, Hl, %Hcm, %Hap, %Hapg, %Hip, %Hasz, %Hamx, Hcore⟩
  unfold ownRaftLogCore
  iNamed Hcore
  wp_auto
  have Hnw : uint.Z lv.unstable'.offset' + (uents.length : Int) < 2^64 := by omega
  ihave #Hsto : isStorageWith (ownStorage lv.storage') lv.storage' $$ [HisStorage]
  · unfold isStorage; iexact HisStorage
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  split_unstable l lv
  wp_apply wp_unstable_maybeLastIndex _ _ uents snap Hnw $$ [Huf Huents Huents_cap]
    as %li %ok ⟨Hun, %Hok1, %Hok2⟩
  · unfold ownUnstable
    simp only [named]
    iframe # ∗
  unfold ownUnstable
  icases Hun with ⟨Huf, Huents_cap, Huents⟩
  ihave Hl := Hlback $$ Huf
  by_cases He : uents = []
  · obtain ⟨rfl, Hli⟩ := Hok1 He
    subst He
    cases snap with
    | some sid =>
      -- the pending snapshot's index
      rw [decide_eq_true (by simp)]
      wp_auto
      iapply HΦ
      obtain ⟨Hsid, Hse, -⟩ := id Hstore
      isplitl
      · reseal_raftLog
      ipureintro
      subst Hsid Hse
      rw [Hli _ rfl]
      simp
    | none =>
      rw [decide_eq_false (by simp)]
      wp_auto
      rw [Hstok]
      wp_auto
      obtain ⟨Hsp, -, Hstored_eq⟩ := id Hstore
      wp_apply HLastIndex $$ HStorage as %li2 ⟨%Hli2, HStorage⟩
      rw [← Hstok]
      iapply HΦ
      isplitl
      · reseal_raftLog
      ipureintro
      dsimp only at Hli2
      rw [Hsp, ← Hstored_eq rfl] at Hli2
      simp only [List.length_nil]
      omega
  · obtain ⟨rfl, Hli⟩ := Hok2 He
    wp_auto
    iapply HΦ
    isplitl
    · reseal_raftLog
    ipureintro
    dsimp only
    omega

end proof

end EtcdGrove
end Perennial
