/- Lean-first (no Rocq counterpart, 2026-10-29, stage U7). -/
module

public import Spec.go_etcd_io.raft.v3.getProgressCopy
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__Visit
public import Spec.go_etcd_io.raft.v3.tracker.Inflights__Clone

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

/-- `Visit` with the invariant "the copy so far is owned, the progresses unchanged"; the closure
reads the progress, clones its `Inflights` and inserts the copy. -/
theorem getProgressCopy.wp_proof
    (wp_ProgressTracker_Visit : tracker.ProgressTracker.Visit.spec (GF := GF) (hG := hG))
    (wp_Inflights_Clone : tracker.Inflights.Clone.spec (GF := GF) (hG := hG)) :
    getProgressCopy.spec (GF := GF) (hG := hG) := by
  intro c V r id s
  wp_start as Hphys
  wp_auto
  wp_apply wp_map_make1 (K := w64) (V := tracker.Progress) as %mref Hm
  icases ownRaftPhysC_tracker_same (c := c) (V := V) r id s $$ Hphys with
    ⟨%tv, Htrkf, Htrk, Hback⟩
  wp_apply wp_ProgressTracker_Visit c _ tv ⟨s.votes, s.progress, s.prvals⟩ _
      (fun _ pvsx => iprop(⌜pvsx = s.prvals⌝ ∗ "m" ∷ m_ptr ↦ mref ∗ "Hm" ∷ progCopyOwn mref))
    $$ [$Htrkf $Htrk m Hm]
  · isplitl [m Hm]
    · try simp only [named]
      iframe m
      unfold progCopyOwn
      iexists ∅
      iframe Hm
      iapply BigSepM.bigSepM_empty.2
      itrivial
    -- the closure
    imodintro
    unfold visitClosureC
    iintro %i %pr %tv0 %pvs0 %p %D
    wp_start as ⟨%Hicfg, %Hpri, %Hpvi, %HmaxI, Htrkf, Hpr, Hback', HI⟩
    icases HI with ⟨%Hpvs0, m, Hm⟩
    subst Hpvs0
    iunfold ownProgress at Hpr
    iNamed Hpr
    wp_auto
    wp_apply wp_Inflights_Clone $$ [$Hinfl] as %l' ⟨Hinfl, Hinfl'⟩
    iunfold progCopyOwn at Hm
    icases Hm with ⟨%pm, Hm, Hpm⟩
    wp_apply wp_mapInsert $$ Hm as Hm
    ihave Htrk := Hback' $$ %p [Hpv Hinfl] %rfl
    · unfold ownProgress
      iexists pv
      iframe Hpv Hinfl
      ipureintro; exact Habs
    iapply HΦ
    iexists tv0, _
    iframe Htrkf Htrk
    simp only [named]
    iframe m
    isplitr
    · ipureintro; exact GMap.insert_id _ _ _ Hpvi
    unfold progCopyOwn
    iexists _
    iframe Hm
    iapply BigSepM.bigSepM_insert_elim $$ [Hinfl'] Hpm
    iexists p.infl
    iexact Hinfl'
  iintro ⟨%tvfin, %pvsfin, Htrkf, Htrk, %Heq, m, Hm⟩
  subst Heq
  ihave Hphys := Hback $$ Htrkf Htrk
  wp_auto
  iapply HΦ
  iframe Hm Hphys

end proof

end EtcdGrove
end Perennial
