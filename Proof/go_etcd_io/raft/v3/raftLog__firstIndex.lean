/-
Port of election_proof/proof_raftLog__firstIndex.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raftLog__firstIndex
public import Spec.go_etcd_io.raft.v3.unstable__maybeFirstIndex

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

/-- Two exits: a pending snapshot answers from `unstable.maybeFirstIndex`
(`prev` is the snapshot's id, `LogStoreOk`); otherwise
`Storage.FirstIndex`, whose boundary is `prev`. -/
theorem raftLog.firstIndex.wp_proof
    (wp_unstable_maybeFirstIndex : unstable.maybeFirstIndex.spec (GF := GF) (hG := hG)) :
    raftLog.firstIndex.spec (GF := GF) (hG := hG) := by
  intro l ls
  wp_start as H
  iNamed H
  iNamed Hlog
  wp_auto
  ihave #Hsto : isStorageWith (ownStorage lv.storage') (appendTok lv.storage')
      (appendedTok lv.storage') (storCut lv.storage') (storFloor lv.storage') (storCert lv.storage') lv.storage' $$ [HisStorage]
  · unfold isStorage; iexact HisStorage
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  lend_unstable
  wp_apply wp_unstable_maybeFirstIndex _ (unstableOf lv ls) $$ [$Hun] as %fi %ok ⟨Hun, %Hok⟩
  reopen_unstable
  obtain ⟨rfl, Hfi⟩ := Hok
  cases Hs : ls.snap with
  | some sid =>
    rw [decide_eq_true (by simp [Hs])]
    wp_auto
    iapply HΦ
    obtain ⟨Hsid, -, -, Hlt⟩ : LogStoreOk (some sid) σ ls.prev ls.sents ls.uents := Hs ▸ Hstore
    isplitl
    · reseal_raftLog
    have Hfe : uint.Z fi = uint.Z ls.prev.index' + 1 := by
      rw [Hfi sid Hs, Hsid]
      have := word.unsigned_range sid.index'
      word
    isplitr
    · ipureintro; omega
    ileft; ipureintro; exact Hfe
  | none =>
    rw [decide_eq_false (by simp [Hs])]
    wp_auto
    rw [Hstok]
    wp_auto
    obtain ⟨Hsp, -, -⟩ : LogStoreOk none σ ls.prev ls.sents ls.uents := Hs ▸ Hstore
    wp_apply HFirstIndex $$ HStorage as %fi2 ⟨%Hfi2, #Hcut, HStorage⟩
    rw [← Hstok]
    iapply HΦ
    isplitl [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
    rw [Hsp, Hfl.1] at Hfi2
    isplitr
    · ipureintro; exact Hfi2
    rw [Hsp, ← Hstor]
    iexact Hcut

end proof

end EtcdGrove
end Perennial
