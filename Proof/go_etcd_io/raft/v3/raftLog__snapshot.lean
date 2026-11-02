/-
Port of election_proof/proof_raftLog__snapshot.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raftLog__snapshot
public import Spec.google_golang_org.protobuf.proto.CloneSnapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  ihave #Hsto : isStorageWith (ownStorage ls.sn lv.storage') (storCut lv.storage') (svCert ls.sn) lv.storage' $$ [HisStorage]
  · unfold isStorageD; iexact HisStorage
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  wp_auto
  cases Hsn : ls.snap with
  | some sid =>
    -- the pending snapshot, read through `l.unstable.snapshot`
    ihave #Hp2 := Hpksn
    iunfold pendKsn at Hp2
    icases Hp2 $$ %sid %rfl with ⟨%sv, #Hsv, %Hsid, %Hk, -⟩
    ihave #Hsv := ownSnapS_M _ _ _ $$ Hsv
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
    obtain ⟨Hp, -, Hsid0⟩ : LogStoreOk (some sid) σ ls.prev ls.sents ls.uents := Hsn ▸ Hstore
    subst Hp
    rw [← Hsid] at Hsid0 Happlied ⊢
    simp only [snapId] at Hsid0 Happlied ⊢
    isplitr
    · ipureintro; intro Hz; rw [Hz] at Hsid0; simp at Hsid0
    ileft
    isplitr
    · ipureintro
      exact ⟨by simp, Hk, Happlied.1, plogTermAt_base _ _⟩
    iapply ksnCerts_mem _ _ _ Hk $$ Hkcert
  | none =>
    -- `l.unstable.snapshot` is `null`: the `Storage`'s
    ihave %Hnosnap := (ownSnap_None _).1 $$ Husnap
    rw [decide_eq_true Hnosnap]
    wp_auto
    take_storage Hsn
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
    icases Hv with ⟨%sv, Hv, %Hsv, Hvc⟩
    have Hnz' := Hsv.1
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
    isplitr
    · ipureintro; exact Hnz
    icases Hvc with (%Hz | ⟨#Hvc, %Hdt⟩)
    · exact absurd Hz Hnz
    iright
    iframe Hvc
    ipureintro
    -- (U8 v2) the term raft certified there: at or below `committed`, the log's
    obtain ⟨Hdc, Hdt', -⟩ := Hfr.2.2 _ _ Hdt
    have Hiv : W64 ((uint.nat sv.Metadata'.Index' : Nat) : Int) = sv.Metadata'.Index' := by
      apply uint_Z_inj.1; word
    have Hpi : uint.Z ls.prev.index' ≤ uint.Z sv.Metadata'.Index' := by rw [← Hp]; exact Hsv.2.1
    have Hc := uint_nat_eq sv.Metadata'.Index'
    refine ⟨rfl, Hpi, by omega, ?_⟩
    rw [← Hiv]; exact Hdt' (by omega)

end proof

end EtcdGrove
end Perennial
