/-
Port of election_proof/proof_raftLog__snapshot.v.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftLog__snapshot
public import RaftWitness.Spec.google_golang_org.protobuf.proto.CloneSnapshot

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
/-- Two exits: a pending snapshot is cloned (`proto.Clone`, `log.go:295`, the trust boundary)
from the log's read-only copy: `pendKsn`'s, whose id is the pending `sid` -- it is the log's base
(`LogStoreOk`) and one the node may send; otherwise `Storage.Snapshot`, which returns a fresh
clone of the storage's `ss` (`HSnapshot`), related to the log by `StoredSnapOk`. -/
theorem raftLog.snapshot.wp_proof
    (wp_proto_CloneSnapshot : proto.CloneSnapshot.spec (GF := GF) (hG := hG)) :
    raftLog.snapshot.spec (GF := GF) (hG := hG) := by
  intro l ls esu
  wp_start as H
  iNamed H
  iNamed Hlog
  ihave #Hsto : isStorageWith (ownStorage lv.storage') (appendTok lv.storage')
      (appendedTok lv.storage') (storCut lv.storage') (storFloor lv.storage') lv.storage' $$ [HisStorage]
  · unfold isStorage; iexact HisStorage
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  wp_auto
  cases Hsn : ls.snap with
  | some sid =>
    -- the pending snapshot, read through `l.unstable.snapshot`
    ihave #Hp2 := Hpksn
    iunfold pendKsn at Hp2
    icases Hp2 $$ %sid %rfl with ⟨%sv, #Hsv, %Hsid, %Hk⟩
    ihave %Hnn := (show ownSnapM (GF := GF) lv.unstable'.snapshot' DFrac.discard sv ⊢
      ⌜lv.unstable'.snapshot' ≠ null⌝ by iintro H; iNamed H; ipureintro; exact Hnn) $$ Hsv
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_proto_CloneSnapshot.1 lv.unstable'.snapshot' DFrac.discard sv $$ [$Hsv]
      as %p' ⟨-, Hc⟩
    iapply HΦ
    isplitl [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
    iright
    isplitr
    · ipureintro; rfl
    iexists sv
    iframe Hc
    ipureintro
    obtain ⟨Hp, -, Hsid0⟩ : LogStoreOk (some sid) σ ls.prev ls.sents ls.uents := Hsn ▸ Hstore
    subst Hp
    rw [← Hsid] at Hsid0 Happlied ⊢
    simp only [snapId] at Hsid0 Happlied ⊢
    refine ⟨?_, Happlied.1, plogTermAt_base _ _, .inl Hk⟩
    intro Hz; rw [Hz] at Hsid0; simp at Hsid0
  | none =>
    -- `l.unstable.snapshot` is `null`: the `Storage`'s
    ihave %Hnosnap := (ownSnap_None _).1 $$ Husnap
    rw [decide_eq_true Hnosnap]
    wp_auto
    -- (D19i part 1) what raft knows of the compaction: its own boundary, or the application's
    ihave Hn : (∃ n : Int, (⌜n ≤ 0⌝ ∨ storCut (GF := GF) lv.storage' n) ∗
        ⌜uint.Z ls.prev.index' ≠ 0 ∨ 1 ≤ n⌝) $$ []
    · icases Hcompact with (%Hc | #Hc)
      · iexists 0
        isplitr
        · ileft; ipureintro; exact Int.le_refl _
        ipureintro; left; exact Hc
      · iunfold storPast at Hc
        icases Hc with ⟨%n, %Hn, #Hc⟩
        iexists n
        isplitr
        · iright; rw [Hstor]; iexact Hc
        ipureintro; right; exact Hn
    icases Hn with ⟨%n, #Hncut, %Hnpre⟩
    rw [Hstok]
    wp_auto
    wp_apply HSnapshot $$ %σ %esu %n [$HStorage $Hesu $Hncut] as %snap %err ⟨HStorage, Herr⟩
    rw [← Hstok]
    iapply HΦ
    isplitl [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
    icases Herr with (%Herr | ⟨%Herr, Hv⟩)
    · ileft; ipureintro; exact Herr
    iright
    icases Hv with ⟨%sv, Hv, %Hsv⟩
    obtain ⟨Hnz', Hwhich⟩ := Hsv
    obtain ⟨Hp, Hstored, -⟩ : LogStoreOk none σ ls.prev ls.sents ls.uents := Hsn ▸ Hstore
    -- (stage R8a) the storage is compacted -- its boundary is the log's, or (D19i part 1) the
    -- application compacted it -- so `HSnapshot`'s snapshot is non-empty
    have Hnz : sv.Metadata'.Index' ≠ W64 0 := by
      apply Hnz'
      rcases Hnpre with Hc | Hc
      · left; rw [Hp]; intro Hz; apply Hc; rw [Hz]; rfl
      · right; exact Hc
    isplitr
    · ipureintro; exact Herr
    iexists sv
    iframe Hv
    ipureintro
    rcases Hwhich with ⟨Hid, Hal, Hcs⟩ | ⟨Hgt, Hge, Hle, Ht⟩
    · have Hss : σ.ss.index' ≠ W64 0 := by
        rw [← Hid]; simp only [snapId]; exact Hnz
      have Hk := Hsksn Hss
      rw [← Hid, ← Hal, ← Hcs] at Hk
      rcases Hssnap Hsn with Hz | ⟨Hle, Ht⟩
      · exfalso; apply Hnz; rw [← Hid] at Hz; simp only [snapId] at Hz; word
      · rw [← Hid] at Hle Ht; simp only [snapId] at Hle Ht
        exact ⟨Hnz, Hle, Ht, .inl Hk⟩
    · -- (D19i part 1) the application's snapshot, at or below the floor: committed, and an
      -- entry of the log (`termAt_log_below`)
      obtain ⟨HflE, Hfla, Hflip, Hab⟩ := Hfl
      rw [HflE] at Hle
      have Hip := Hflip Hsn
      have Hpers := Hpersist Hsn
      rw [← Hpend.1] at Hpers
      refine ⟨Hnz, by omega, ?_, .inr Hle⟩
      have HpZ : uint.Z σ.prev.index' = uint.Z ls.prev.index' := by rw [Hp]
      rw [← Hp]
      refine termAt_log_below σ ls.sents ls.uents _ σ.pend ls.stored _ _ Hpers
        ⟨by omega, by omega⟩ Hge (by omega) (fun e0 He0 => ?_) Ht
      have := Hab e0 He0
      rw [HflE] at this
      omega

end proof

end EtcdGrove
end Perennial
