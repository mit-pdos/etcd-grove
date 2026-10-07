/-
Port of election_proof/proof_raftLog__snapshot.v.
-/
import EtcdGrove.Raft.Spec.raftLog__snapshot

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
/-- Two exits: a pending snapshot is returned by value -- it is the log's base
(`LogStoreOk`), with `ownSnap`'s voters; otherwise `Storage.Snapshot`, which returns
the storage's `ss` (`HSnapshot`), related to the log by `StoredSnapOk`. -/
theorem raftLog.snapshot.wp_proof : raftLog.snapshot.spec (GF := GF) (hG := hG) := by
  intro l ls esu
  obtain ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ := ls
  wp_start as H
  iNamed H
  icases (ownRaftLog_unfold l prev sents uents lcm lap snap lip lapg lpend lasz lamx).1 $$ Hlog with ⟨%lv, Hl, %Hcm, %Hap, %Hapg, %Hip, %Hasz, %Hamx, Hcore⟩
  unfold ownRaftLogCore
  icases Hcore with ⟨%sprev, %stored, %ss, Hcore⟩
  iNamed Hcore
  ihave #Hsto : isStorageWith (ownStorage lv.storage') lv.storage' $$ [HisStorage]
  · unfold isStorage; iexact HisStorage
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  subst lcm
  wp_auto
  cases snap with
  | some sid =>
    -- the pending snapshot, read through `l.unstable.snapshot`
    ihave Hus := (ownSnap_Some _ sid).1 $$ Husnap
    icases Hus with ⟨%sv, #Hsv, %Hmeta, %voters, #Hvoters⟩
    ihave %Hnn := typedPointsto_not_null $$ Hsv
    rw [decide_eq_false Hnn]
    wp_auto
    iapply HΦ
    isplitl [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
    iright
    isplitr
    · ipureintro
      obtain ⟨Hi, Ht⟩ := Hmeta
      obtain ⟨Hp, -, Hsid⟩ := Hstore
      subst Hp
      simp only
      rw [Hi, Ht]
      refine ⟨trivial, ?_, Happlied.1, plogTermAt_base _ _⟩
      intro Hz; rw [Hz] at Hsid; simp at Hsid
    · iexists voters; iexact Hvoters
  | none =>
    -- `l.unstable.snapshot` is `null`: the `Storage`'s
    ihave %Hnosnap := (ownSnap_None _).1 $$ Husnap
    rw [decide_eq_true Hnosnap]
    wp_auto
    rw [Hstok]
    wp_auto
    wp_apply HSnapshot $$ [$HStorage $Hesu] as %snap %err ⟨HStorage, Herr⟩
    rw [← Hstok]
    iapply HΦ
    isplitl [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
    icases Herr with (%Herr | ⟨%Herr, Hv⟩)
    · ileft; ipureintro; exact Herr
    iright
    iframe Hv
    ipureintro
    obtain ⟨rfl, Hid, Hnz⟩ := Herr
    rcases Hssnap rfl with Hz | ⟨Hle, Ht⟩
    · exfalso; apply Hnz; rw [← Hid] at Hz; simp only [snapId] at Hz; word
    · rw [← Hid] at Hle Ht; simp only [snapId] at Hle Ht
      exact ⟨rfl, Hnz, Hle, Ht⟩

end proof

end EtcdGrove
end Perennial
