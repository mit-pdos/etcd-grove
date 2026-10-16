/-
Port of election_proof/proof_raft__becomeLeader.v.

Lean notes: the Go code stores the generated constant `go_etcd_io.raft.v3.StateLeader`
(`#(W64 2)`), which `wp_apply` does not unify with `#(stateW64 .leader)`;
`wp_store_state_leader` is `raft.wp_store_stateC` at that value.

raft v3.7 (stage R4): the empty entry is `&pb.Entry{Data: nil}`, a fresh struct made an owned
entry (`entOwn_of_struct`) and frozen (`entOwn_freeze`), its one-element slice handed to
`appendEntry` as `entsPts` (at `1`; `appendEntry` clones it and gives it back).
-/
module

public import Spec.go_etcd_io.raft.v3.raft__becomeLeader
public import Spec.go_etcd_io.raft.v3.raft__reset
public import Spec.go_etcd_io.raft.v3.traceBecomeLeader
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.raft__appendEntry
public import Spec.go_etcd_io.raft.v3.tracker.Progress__BecomeReplicate
public import Proof.go_etcd_io.raft.v3.LemmasSendR

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

/-- `raft.wp_store_stateC` at the value the Go code stores. -/
private theorem wp_store_state_leader (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (Hcfg : id ∈ c.voters) (Hpr : ∀ v p, s.prvals !! v = some p → PrOk s.logst p) :
    {{ ownRaftPhysCV (GF := GF) c c.voters r id s }}
      (App (Val (GoInstruction (GoStore StateType.ty)))
        (Val (PairV #(r.[raft, go!"state"]) go_etcd_io.raft.v3.StateLeader)))
    {{ RET #(); ownRaftPhysCV c c.voters r id { s with role := .leader } }} :=
  raft.wp_store_stateC c r id s .leader (fun _ => Hcfg) (Hpr := fun _ => Hpr)

theorem raft.becomeLeader.wp_proof
    (wp_raft_reset : raft.reset.spec (GF := GF) (hG := hG))
    (wp_traceBecomeLeader : traceBecomeLeader.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raft_appendEntry : raft.appendEntry.spec (GF := GF) (hG := hG))
    (wp_Progress_BecomeReplicate : tracker.Progress.BecomeReplicate.spec (GF := GF) (hG := hG)) :
    raft.becomeLeader.spec (GF := GF) (hG := hG) := by
  intro c r id s Hrole Hnz
  wp_start as Hphys
  -- the node is a voter (`ownRaftPhysC`'s `Hvoter`: it is not a follower), so tracked
  icases ownRaftPhysC_voter c r id s $$ Hphys with ⟨%Hv, Hphys⟩
  have Hcfg : id ∈ c.voters := Hv Hrole
  -- (stage R8a) `lastIndex() + 1` does not wrap: `reset`'s values are within the log
  icases ownRaftPhysC_prvals_ok c r id s $$ Hphys with ⟨-, %Hnw, Hphys⟩
  wp_auto
  -- `becomeLeader` panics on a follower; by assumption we are not one.
  have Hnf : stateW64 s.role ≠ W64 0 := by
    cases h : s.role <;> simp_all [stateW64, StateCandidate, StateLeader, StatePreCandidate]
  wp_apply raft.wp_load_stateC $$ Hphys as Hphys
  rw [decide_eq_false Hnf]
  wp_auto
  -- `r.step := stepLeader`, then `reset` at the unchanged term, so the vote survives
  wp_apply raft.wp_store_stepC $$ Hphys as Hphys
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_apply wp_raft_reset c r id { s with stepfn := functions stepLeader [] } s.term
    (Int.le_refl _) $$ [$Hphys] as %pvs ⟨Hphys, %Hmr, %Hrp⟩
  -- `r.tick`, `r.lead := r.id`, `r.state := StateLeader`
  wp_apply raft.wp_store_tickC (Hf := .inr rfl) $$ Hphys as Hphys
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  wp_apply raft.wp_store_leadC $$ Hphys as Hphys
  -- the state, named, so that the progress premise is stated at it
  ihave Hphys : ownRaftPhysCV c c.voters r id
      { resetTo { s with stepfn := functions stepLeader [] } s.term with
          prvals := pvs, ticking := true, lead := id } $$ [Hphys]
  · iapply ownRaftPhysC_eq c r id _ _ (by rfl) $$ Hphys
  wp_apply wp_store_state_leader c r id
      { resetTo { s with stepfn := functions stepLeader [] } s.term with
          prvals := pvs, ticking := true, lead := id }
      Hcfg (fun v p hv => (Hrp v p hv).prOk Hnw) $$ Hphys as Hphys
  -- the state is now `becomeLeaderPre` up to the order of the record updates
  ihave Hphys : ownRaftPhysCV c c.voters r id { becomeLeaderPre id s with prvals := pvs } $$ [Hphys]
  · iapply ownRaftPhysC_eq c r id _ _ ?_ $$ Hphys
    rfl
  generalize hs1 : ({ becomeLeaderPre id s with prvals := pvs } : NState) = s1
  -- the leader's own `Progress` is marked replicating and recently active; the map
  -- lookup is on the tracker object
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  icases ownRaftPhysC_prvals_ok c r id s1 $$ Hphys with ⟨%Hok1, %Hnw1, Hphys⟩
  icases ownRaftPhysC_tracker_prvals c r id _ $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  wp_auto
  wp_apply wp_trackerC_progress_lookup c tv _ id ((GMap.elem_of_subseteq _ _).1 (voters_sub_ids c) _ Hcfg) $$ [$Htrk]
    as %pr ⟨-, %p0, %Hpv0, Hpr, Hprback⟩
  wp_apply wp_Progress_BecomeReplicate $$ [$Hpr] as Hpr
  -- `ownProgress` owns the whole `Progress` value, so the `RecentActive` assignment steps
  -- through `Hpv` with the generated `AccessStrict` instances and leaves `Inflights'`
  -- alone.
  iNamed Hpr
  wp_auto
  ihave Hpr : ownProgress pr (progressBecomeReplicate p0)
      $$ [Hpv Hinfl]
  · iapply ownProgress_intro pr _ _ $$ Hpv [Hinfl]
    · iexact Hinfl
    ipureintro
    obtain ⟨h1, h2, h3, h4, h5, h8, h9⟩ := (progressAbs_Some _ _ _).1 Habs
    exact (progressAbs_Some _ _ _).2 ⟨h1, h2, h3, h4, h5, h8, h9⟩
  ihave Htrk := Hprback $$ %_ Hpr %rfl
  ihave Hphys := Hback $$ %_ %_ Htrkf Htrk
    %(PrvalsOk.insert (pvs := s1.prvals) Hok1 (fun Hl => (Hok1.lookup Hl Hpv0).becomeReplicate Hnw1))
  -- `r.pendingConfIndex = r.raftLog.lastIndex()`
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hback⟩
  wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
  ihave Hphys := Hback $$ Hlog
  wp_apply raft.wp_store_pendingConfIndexC $$ Hphys as Hphys
  have Hli' : li = logLast s.logst := by
    subst hs1
    unfold logLast
    simp only [becomeLeaderPre, resetTo, resetTo0] at Hli
    word
  subst Hli'
  wp_apply wp_traceBecomeLeader
  -- (stage R4) `emptyEnt := &pb.Entry{Data: nil}`: a fresh entry, frozen read-only
  ihave Hnilb : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod ownSlice_persist $$ Hnilb with #Hnilb
  imod entOwn_of_struct «$r0_ptr»
      { state' := zeroValDef, Term' := null, Index' := null, Type' := null, Data' := slice.nil,
        unknownFields' := slice.nil, sizeCache' := 0 } (zero_val EntryM) ⊤ rfl $$ [«$r0»] with He
  · iframe «$r0» Hnilb
    msg_nulls
  imod entOwn_freeze $$ He with #He
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %es ⟨Hes, -⟩
  ihave Hes : entsPts _ (DFrac.own 1) [zero_val EntryM] $$ [Hes]
  · iunfold entsPts
    iexists [«$r0_ptr»]
    iframe Hes
    iapply BigSepL2.bigSepL2_singleton.2; iexact He
  wp_auto
  -- `appendEntry` writes `Term`/`Index` into every element of the slice, so it needs
  -- `Hes`. It returns a bool, and its postcondition says an all-empty batch is never
  -- dropped; the entry's `Data` is nil, so `accepted = true` and the `Panic` on the
  -- `false` branch below is dead code. It also queues a self-addressed `MsgAppResp`, the
  -- self-acknowledgement: the state is `becomeLeader`. One entry is not `2^61`.
  wp_apply wp_raft_appendEntry c r id _ _ [zero_val EntryM] (DFrac.own 1)
      (by simp) (by subst hs1; exact Hnz)
      $$ [$Hphys $Hes]
    as %accepted ⟨%Hacc, Hes, Hphys⟩
  -- empty payload, so accepted; the `false` branch is gone before any `WP` is stepped on it
  have Hacc' : accepted = true := Hacc (by intro e He; simp at He; subst He; rfl)
  subst Hacc'
  simp only [↓reduceIte]
  wp_auto
  -- `appendEntry` appended the stamped empty entry: that is `becomeLeader` (`Defs.lean`)
  ihave Hphys : ownRaftPhysCV c c.voters r id
      { becomeLeader id s with
        prvals := <[id := progressBecomeReplicate p0]> pvs }
      $$ [Hphys]
  · iapply ownRaftPhysC_eq c r id _ _ ?_ $$ Hphys
    subst hs1
    rfl
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_raft_logC
  iapply HΦ
  iframe
  ipureintro
  subst hs1
  dsimp only at Hpv0 ⊢
  rw [prvalsMatch_insert_same _ _ p0 (progressBecomeReplicate p0)
    Hpv0 rfl]
  exact Hmr

end proof

end EtcdGrove
end Perennial
