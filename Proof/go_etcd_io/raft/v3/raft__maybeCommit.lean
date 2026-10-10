/-
Port of election_proof/proof_raft__maybeCommit.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__maybeCommit
public import Spec.go_etcd_io.raft.v3.traceCommit
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__Committed
public import Spec.go_etcd_io.raft.v3.raftLog__maybeCommit

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

omit ext ffi [FfiSemantics ext ffi] [GoGlobalContext] [FfiInterp ffi] in
/-- `ProgressTracker.Committed`'s quorum, stated over the voter set with
`pvsMatchAt` (`InvTracker.lean`), as the model's `ackedBy` states it,
over the `Match` map: a voter whose `Match` is at least a non-zero `N`
has a `Progress`, so it is in `prvalsMatch pvs`'s domain. (At `N = 0`
the two differ: `pvsMatchAt` counts a voter with no `Progress` as
`0`.) -/
private theorem isQuorumIndex_acked (cfg : GSet w64) (pvs : GMap w64 Progress) (N : w64)
    (Hpos : 0 < uint.Z N) (H : IsQuorumIndex cfg (pvsMatchAt pvs) N) :
    IsQuorum cfg (domSet (GMap.filter (fun _ x => decide (uint.Z N ≤ uint.Z x))
      (prvalsMatch pvs))) := by
  obtain ⟨-, Hq, -⟩ := H
  unfold IsQuorum at Hq ⊢
  have Hsub : GMap.filter (fun v _ => decide (uint.Z N ≤ uint.Z (pvsMatchAt pvs v))) cfg ∩ cfg ⊆
      domSet (GMap.filter (fun _ x => decide (uint.Z N ≤ uint.Z x)) (prvalsMatch pvs)) ∩ cfg := by
    rw [GMap.elem_of_subseteq]
    intro v Hv
    rw [GMap.elem_of_intersection] at Hv ⊢
    refine ⟨?_, Hv.2⟩
    have Hle : uint.Z N ≤ uint.Z (pvsMatchAt pvs v) := by
      have Hv1 := Hv.1
      rw [GMap.mem_iff, GMap.lookup_filter] at Hv1
      cases Hc : cfg !! v with
      | none => simp [Hc] at Hv1
      | some u =>
        simp only [Hc, Option.filter] at Hv1
        split at Hv1
        · exact of_decide_eq_true ‹_›
        · simp at Hv1
    rw [GMap.elem_of_dom]
    change uint.Z N ≤ uint.Z (((pvs !! v).map Progress.matched).getD (W64 0)) at Hle
    cases E : pvs !! v with
    | none =>
      rw [E] at Hle
      simp only [Option.map_none, Option.getD_none] at Hle
      exfalso
      have : uint.Z (W64 0) = 0 := rfl
      omega
    | some p =>
      refine ⟨p.matched, ?_⟩
      rw [E] at Hle
      simp only [Option.map_some, Option.getD_some] at Hle
      simp only [prvalsMatch, GMap.lookup_filter]
      change Option.filter _ ((pvs !! v).map Progress.matched) = _
      rw [E]
      simp only [Option.map_some, Option.filter]
      simp only [decide_eq_true Hle, ↓reduceIte]
  have := GMap.subseteq_size Hsub
  omega

/-- The body, with its `defer`: `wp_with_defer` allocates the defer
stack, the `traceCommit` closure is pushed onto it, and `return:`
runs it (`traceCommit.spec`) before the function returns.

`r.Term` is a field load; `r.trk.Committed()` runs on the tracker
taken out with `ownRaftPhys_tracker_same` (it gives the tracker
back unchanged); `r.raftLog.maybeCommit` on the log taken out with
`ownRaftPhys_log_at` and put back at what it returns. On `true`,
`raftLog.maybeCommit`'s condition gives the range and the term
(`PlogMatches` is `plogTermAt … = some`), and `Committed`'s
quorum index becomes `ackedBy`'s quorum by
`isQuorumIndex_acked`: `N` is past `committed`, so non-zero. -/
theorem raft.maybeCommit.wp_proof
    (wp_traceCommit : traceCommit.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_Committed : tracker.ProgressTracker.Committed.spec (GF := GF) (hG := hG))
    (wp_raftLog_maybeCommit : raftLog.maybeCommit.spec (GF := GF) (hG := hG)) :
    raft.maybeCommit.spec (GF := GF) (hG := hG) := by
  intro cfg r id s Hlead Hid
  wp_start as H
  iNamed H
  wp_apply wp_with_defer as %defer defer
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  icases ownRaftPhys_tracker_same cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  wp_apply wp_ProgressTracker_Committed $$ [$Htrkf $Htrk] as %N ⟨Htrkf, Htrk, %Hempty, %Hq⟩
  ihave Hphys := Hback $$ %tv Htrkf Htrk
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_at cfg r id s $$ Hphys with ⟨Hlog, %Hgh0, Hlogback⟩
  wp_apply wp_raftLog_maybeCommit $$ [$Hlog] as %b ⟨Hlog, %Hb⟩
  ihave Hphys := Hlogback $$ %_ Hlog
    %(by cases b <;> exact LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl)
  wp_apply wp_traceCommit
  iapply HΦ $$ %b %N
  cases b with
  | true =>
    isplitl [Hphys]
    · iapply ownRaftPhys_eq $$ Hphys
      rfl
    ipureintro
    intro _
    obtain ⟨-, Hlt, Hm⟩ := of_decide_eq_true Hb.symm
    unfold PlogMatches at Hm
    have Hne : cfg ≠ ∅ := by
      intro h; rw [h] at Hid; exact GMap.not_elem_of_empty _ Hid
    have Hq := Hq Hne
    refine ⟨Hlt, (plogTermAt_some_range _ _ _ _ Hm).2, Hm, ?_⟩
    simp only [toPState, ackedBy, Hlead, ↓reduceIte]
    exact isQuorumIndex_acked cfg s.prvals N (by word) Hq
  | false =>
    isplitl [Hphys]
    · iapply ownRaftPhys_eq $$ Hphys
      cases s; rfl
    ipureintro
    intro h; cases h

end proof

end EtcdGrove
end Perennial
