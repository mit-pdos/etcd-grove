/-
Port of election_proof/proof_raftLog__lastIndex.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.unstable__maybeLastIndex

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

/-- Three exits: a non-empty unstable suffix; an empty one with a pending snapshot,
whose index is `prev`'s (`LogStoreOk`); an empty one without, where
`Storage.LastIndex` is `prev.index + |stored|` and `stored = sents`. -/
theorem raftLog.lastIndex.wp_proof
    (wp_unstable_maybeLastIndex : unstable.maybeLastIndex.spec (GF := GF) (hG := hG)) :
    raftLog.lastIndex.spec (GF := GF) (hG := hG) := by
  intro l ls
  wp_start as H
  iNamed H
  iNamed Hlog
  wp_auto
  have Hnw : uint.Z lv.unstable'.offset' + (ls.uents.length : Int) < 2^64 := by omega
  ihave #Hsto : isStorageWith (ownStorage lv.storage') (appendTok lv.storage')
      (appendedTok lv.storage') lv.storage' $$ [HisStorage]
  · unfold isStorage; iexact HisStorage
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  lend_unstable
  wp_apply wp_unstable_maybeLastIndex _ (unstableOf lv ls) Hnw $$ [$Hun]
    as %li %ok ⟨Hun, %Hok1, %Hok2⟩
  reopen_unstable
  by_cases He : ls.uents = []
  · obtain ⟨rfl, Hli⟩ := Hok1 He
    cases Hs : ls.snap with
    | some sid =>
      -- the pending snapshot's index
      rw [decide_eq_true (by simp [Hs])]
      wp_auto
      iapply HΦ
      obtain ⟨Hsid, Hse, -⟩ : LogStoreOk (some sid) σ ls.prev ls.sents ls.uents := Hs ▸ Hstore
      isplitl
      · reseal_raftLog
      ipureintro
      rw [Hli _ Hs, Hsid, Hse, He]
      simp
    | none =>
      rw [decide_eq_false (by simp [Hs])]
      wp_auto
      rw [Hstok]
      wp_auto
      obtain ⟨Hsp, -, Hstored_eq⟩ : LogStoreOk none σ ls.prev ls.sents ls.uents := Hs ▸ Hstore
      have Hpnil : σ.pend = [] := by
        rw [Hpend.1]; exact (Hpersist Hs).2.2.1 He
      wp_apply HLastIndex $$ [$HStorage] as %li2 ⟨%Hli2, HStorage⟩
      · ipureintro; exact Hpnil
      rw [← Hstok]
      iapply HΦ
      isplitl
      · reseal_raftLog
      ipureintro
      rw [Hsp, ← Hstored_eq He] at Hli2
      rw [He, List.length_nil]
      omega
  · obtain ⟨rfl, Hli⟩ := Hok2 He
    wp_auto
    iapply HΦ
    isplitl
    · reseal_raftLog
    ipureintro
    word

end proof

end EtcdGrove
end Perennial
