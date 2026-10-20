/-
Port of election_proof/proof_raft__maybeCommit.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__maybeCommit
public import Spec.go_etcd_io.raft.v3.traceCommit
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__Committed
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__OneLessThanQuorumInReplicationSet
public import Spec.go_etcd_io.raft.v3.raftLog__maybeCommit

public import Spec.go_etcd_io.raft.v3.raft__sendAppendToWitness
public import Spec.go_etcd_io.raft.v3.raftLog__subterm

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
private theorem isQuorumIndex_acked (c : GSet w64) (pvs : GMap w64 Progress) (N M : w64)
    (Hpos : 0 < uint.Z N) (HM : uint.Z N ≤ uint.Z M) (H : IsQuorumIndex c (pvsMatchAt pvs) M) :
    IsQuorum c (domSet (GMap.filter (fun _ x => decide (uint.Z N ≤ uint.Z x))
      (prvalsMatch pvs))) := by
  obtain ⟨-, Hq, -⟩ := H
  unfold IsQuorum at Hq ⊢
  have Hsub : GMap.filter (fun v _ => decide (uint.Z M ≤ uint.Z (pvsMatchAt pvs v))) c ∩ c ⊆
      domSet (GMap.filter (fun _ x => decide (uint.Z N ≤ uint.Z x)) (prvalsMatch pvs)) ∩ c := by
    rw [GMap.elem_of_subseteq]
    intro v Hv
    rw [GMap.elem_of_intersection] at Hv ⊢
    refine ⟨?_, Hv.2⟩
    have Hle : uint.Z N ≤ uint.Z (pvsMatchAt pvs v) := by
      refine Int.le_trans HM ?_
      have Hv1 := Hv.1
      rw [GMap.mem_iff, GMap.lookup_filter] at Hv1
      cases Hc : c !! v with
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
taken out with `ownRaftPhysC_tracker_same` (it gives the tracker
back unchanged); `r.raftLog.maybeCommit` on the log taken out with
`ownRaftPhysC_log_at` and put back at what it returns. On `true`,
`raftLog.maybeCommit`'s condition gives the range and the term
(`PlogMatches` is `plogTermAt … = some`), and `Committed`'s
quorum index becomes `ackedBy`'s quorum by
`isQuorumIndex_acked`: `N` is past `committed`, so non-zero. -/
theorem raft.maybeCommit.wp_proof
    (wp_traceCommit : traceCommit.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_Committed : tracker.ProgressTracker.Committed.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_OneLessThanQuorumInReplicationSet :
      tracker.ProgressTracker.OneLessThanQuorumInReplicationSet.spec (GF := GF) (hG := hG))
    (wp_raftLog_maybeCommit : raftLog.maybeCommit.spec (GF := GF) (hG := hG))
    (wp_raftLog_subterm : raftLog.subterm.spec (GF := GF) (hG := hG))
    (wp_raft_sendAppendToWitness : raft.sendAppendToWitness.spec (GF := GF) (hG := hG)) :
    raft.maybeCommit.spec (GF := GF) (hG := hG) := by
  intro c r id s Hlead
  wp_start as H
  iNamed H
  wp_apply wp_with_defer as %defer defer
  -- (2026-10-20, witness support) `OneLessThanQuorumInReplicationSet`, then to each witness it
  -- reports the entry at its index, if of the leader's term and subterm
  icases ownRaftPhysC_epOk c r id s $$ Hphys with ⟨%Hepok, Hphys⟩
  icases ownRaftPhysC_tracker_same c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  wp_apply (tracker.ProgressTracker.OneLessThanQuorumInReplicationSet.spec_c
    wp_ProgressTracker_OneLessThanQuorumInReplicationSet c _ tv _) $$ [$Htrkf $Htrk]
    as %mref ⟨Htrkf, Htrk, Hres⟩
  ihave Hphys := Hback $$ %tv Htrkf Htrk
  try wp_auto
  -- the loop, at the requests sent so far `ws`
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ ws : List Msg,
      ownRaftPhysCV c c.voters r id (sendMsgs s ws) ∗
      ⌜(∀ m ∈ ws, WAppSent c id s m) ∧ (c.wit = W64 0 → ws = [])⌝ ∗
      r_ptr ↦ r ∗ (∃ x : w64, w_ptr ↦ x) ∗ (∃ y : w64, wci_ptr ↦ y))))
    $$ [Hres Hphys r w wci]
  · icases Hres with (%Hnone | ⟨%Hns, %res, Hmap, %Hok⟩)
    · -- `nil`: nothing
      obtain ⟨-, rfl⟩ := Hnone
      wp_apply (wp_map_nil_for_range_val ⟨_, _, _⟩)
      isplitr; · ipureintro; rfl
      iexists []
      ihave Hphys : ownRaftPhysCV c c.voters r id (sendMsgs s []) $$ [Hphys]
      · iapply ownRaftPhysC_eq c r id _ _ ?_ $$ Hphys
        simp [sendMsgs]
      iframe Hphys r
      isplitr; · ipureintro; exact ⟨(fun _ h => nomatch h), fun _ => rfl⟩
      isplitl [w]; · iexists _; iexact w
      iexists _; iexact wci
    · -- each witness the tracker reports
      iapply wp_map_for_range (fun (_ : List w64) (_ : Int) => iprop(∃ ws : List Msg,
          ownRaftPhysCV c c.voters r id (sendMsgs s ws) ∗
          ⌜(∀ m ∈ ws, WAppSent c id s m) ∧ (c.wit = W64 0 → ws = [])⌝ ∗
          r_ptr ↦ r ∗ (∃ x : w64, w_ptr ↦ x) ∗ (∃ y : w64, wci_ptr ↦ y))) $$ Hmap
      iintro %keys -
      isplitl [Hphys r w wci]
      · iexists []
        ihave Hphys : ownRaftPhysCV c c.voters r id (sendMsgs s []) $$ [Hphys]
        · iapply ownRaftPhysC_eq c r id _ _ ?_ $$ Hphys
          simp [sendMsgs]
        iframe Hphys r
        isplitr; · ipureintro; exact ⟨(fun _ h => nomatch h), fun _ => rfl⟩
        isplitl [w]; · iexists _; iexact w
        iexists _; iexact wci
      isplitr
      · imodintro
        iintro %i %key %wci0 ⟨%Hkey, %Hv⟩ ⟨%ws, Hphys, %Hinv, r, ⟨%x, w⟩, ⟨%y, wci⟩⟩
        wp_auto
        by_cases hz : wci0 = W64 0
        · -- `continue`
          rw [decide_eq_true hz]
          wp_auto
          unfold forMapPostcondition
          ileft
          isplitr; · ipureintro; rfl
          iexists ws
          iframe Hphys r
          isplitr; · ipureintro; exact Hinv
          isplitl [w]; · iexists _; iexact w
          iexists _; iexact wci
        rw [decide_eq_false hz]
        wp_auto
        generalize Hs1 : sendMsgs s ws = s1
        have Hs1l : s1.logst = s.logst := by rw [← Hs1]; rfl
        have Hs1t : s1.term = s.term := by rw [← Hs1]; rfl
        have Hs1e : s1.ep = s.ep := by rw [← Hs1]; rfl
        -- `t, st, ok := r.raftLog.subterm(wci)`
        wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
        icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hlogback⟩
        wp_apply wp_raftLog_subterm _ _ wci0 $$ [$Hlog] as %t %st %ok ⟨Hlog, %Hsub⟩
        ihave Hphys := Hlogback $$ Hlog
        cases ok
        · -- not in the log: nothing sent
          wp_auto
          unfold forMapPostcondition
          iright; ileft
          isplitr; · ipureintro; rfl
          iexists ws
          rw [← Hs1] at *
          iframe Hphys r
          isplitr; · ipureintro; exact Hinv
          isplitl [w]; · iexists _; iexact w
          iexists _; iexact wci
        try wp_auto
        wp_apply raft.wp_load_TermC $$ Hphys as Hphys
        try wp_auto
        by_cases ht : t = s1.term
        rotate_left
        · rw [decide_eq_false ht]
          wp_auto
          unfold forMapPostcondition
          iright; ileft
          isplitr; · ipureintro; rfl
          iexists ws
          rw [← Hs1] at *
          iframe Hphys r
          isplitr; · ipureintro; exact Hinv
          isplitl [w]; · iexists _; iexact w
          iexists _; iexact wci
        rw [decide_eq_true ht]
        wp_auto
        wp_apply raft.wp_load_trk_EpochC' c r id _ $$ Hphys as %e ⟨Hphys, #He⟩
        iunfold ownEpochOk at He
        icases He with ⟨#He, -⟩
        icases ownEpoch_fields _ _ $$ He with ⟨#Hst, -, -⟩
        wp_auto
        by_cases hst : st = s1.ep.sub
        rotate_left
        · rw [decide_eq_false hst]
          wp_auto
          unfold forMapPostcondition
          iright; ileft
          isplitr; · ipureintro; rfl
          iexists ws
          rw [← Hs1] at *
          iframe Hphys r
          isplitr; · ipureintro; exact Hinv
          isplitl [w]; · iexists _; iexact w
          iexists _; iexact wci
        rw [decide_eq_true hst]
        wp_auto
        -- `r.sendAppendToWitness(w, uint64(wci), st)`: the configuration has a witness
        simp only at Hok Hns
        have Hcw : c.wit ≠ W64 0 := by
          have h := (Hok.1 key).1 (by rw [Hv]; rfl)
          have hw : s.ep.hasWit = true := by
            unfold EpochM.hasWit; apply decide_eq_true
            rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact Or.inl (of_decide_eq_true h1).1
            · exact Or.inr (of_decide_eq_true h1).1
          exact (EpochOkC.wf Hepok hw).1
        wp_apply wp_raft_sendAppendToWitness c r id s1 key wci0 st Hcw $$ [$Hphys]
          as %vs0 %vs1 ⟨%Hvs, Hphys⟩
        obtain ⟨e0, He0, He0t, He0s⟩ := Hsub rfl
        unfold forMapPostcondition
        iright; ileft
        isplitr; · ipureintro; rfl
        iexists ws ++ [wAbs (wappMsg id key s.term s.ep.sub wci0 vs0 vs1)]
        subst Hs1
        ihave Hphys : ownRaftPhysCV c c.voters r id
            (sendMsgs s (ws ++ [wAbs (wappMsg id key s.term s.ep.sub wci0 vs0 vs1)])) $$ [Hphys]
        · iapply ownRaftPhysC_eq c r id _ _ ?_ $$ Hphys
          subst hst
          simp [sendMsgs, List.append_assoc]
        iframe Hphys r
        isplitr
        · ipureintro
          refine ⟨fun m hm => ?_, fun h => absurd h Hcw⟩
          rcases List.mem_append.1 hm with hm | hm
          · exact Hinv.1 m hm
          · rw [List.mem_singleton] at hm
            subst hm
            refine ⟨key, wci0, e0, vs0, vs1, res, rfl, Hns, Hok, Hv, hz, He0, ?_, ?_, Hvs.1, Hvs.2⟩
            · rw [He0t, ht]; rfl
            · rw [He0s, hst]; rfl
        isplitl [w]; · iexists _; iexact w
        iexists _; iexact wci
      iintro ⟨%ws, Hphys, %Hinv, r, w, wci⟩ Hmap
      isplitr; · ipureintro; rfl
      iexists ws
      iframe Hphys r w wci
      ipureintro; exact Hinv
  iintro %v ⟨%Hv, %ws, Hphys, %Hinv, r, -, -⟩
  subst Hv
  -- then the commit, at the state with the requests queued
  generalize Hs1 : sendMsgs s ws = s1
  have Hlead1 : s1.role = .leader := by rw [← Hs1]; exact Hlead
  wp_pures; (try wp_auto)
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  icases ownRaftPhysC_tracker_same c r id s1 $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  wp_apply wp_ProgressTracker_Committed $$ [$Htrkf $Htrk] as %N ⟨Htrkf, Htrk, %Hq⟩
  ihave Hphys := Hback $$ %tv Htrkf Htrk
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_at c r id s1 $$ Hphys with ⟨Hlog, %Hgh0, Hlogback⟩
  wp_apply wp_raftLog_maybeCommit $$ [$Hlog] as %b ⟨Hlog, %Hb⟩
  ihave Hphys := Hlogback $$ %_ Hlog
    %(by
      cases b
      · exact LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl
      · exact LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl
          (hcm := Int.le_of_lt (of_decide_eq_true Hb.symm).2.1))
    %(by cases b <;> exact fun _ => logLast_le_of_fields rfl rfl rfl)
  wp_apply wp_traceCommit
  iapply HΦ $$ %b %N %ws
  subst Hs1
  cases b with
  | true =>
    isplitl [Hphys]
    · iapply ownRaftPhysC_eq $$ Hphys
      rfl
    ipureintro
    refine ⟨Hinv.1, Hinv.2, fun _ => ?_⟩
    obtain ⟨-, Hlt, Hm⟩ := of_decide_eq_true Hb.symm
    unfold PlogMatches at Hm
    simp only [sendMsgs] at Hlt Hm Hq
    refine ⟨Hlt, (plogTermAt_some_range _ _ _ _ Hm).2, Hm, ?_⟩
    simp only [toPState, ackedBy, Hlead, ↓reduceIte]
    have Hpos : 0 < uint.Z N := by word
    obtain ⟨N0, N1, H0, H1, HN⟩ := Hq
    have Hle0 : uint.Z N ≤ uint.Z N0 := by rw [HN]; split <;> omega
    have Hle1 : uint.Z N ≤ uint.Z N1 := by rw [HN]; split <;> omega
    refine ⟨?_, ?_⟩
    · by_cases he : c.incoming = ∅
      · exact Or.inl he
      · exact Or.inr (isQuorumIndex_acked _ s.prvals N N0 Hpos Hle0 (H0.2 he))
    · by_cases he : c.outgoing = ∅
      · exact Or.inl he
      · exact Or.inr (isQuorumIndex_acked _ s.prvals N N1 Hpos Hle1 (H1.2 he))
  | false =>
    isplitl [Hphys]
    · iapply ownRaftPhysC_eq $$ Hphys
      cases s; rfl
    ipureintro
    exact ⟨Hinv.1, Hinv.2, fun h => by cases h⟩

end proof

end EtcdGrove
end Perennial
