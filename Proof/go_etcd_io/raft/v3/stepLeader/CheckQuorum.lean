/-
`stepLeader`'s `MsgCheckQuorum` arm (2026-10-17, `CheckQuorum` on; Lean-first, no Rocq
counterpart):

    case pb.MsgCheckQuorum:
      if !r.trk.QuorumActive() {
        r.logger.Warningf("%x stepped down to follower since quorum is not active", r.id)
        r.becomeFollower(r.Term, None)
      }
      r.trk.Visit(func(id uint64, pr *tracker.Progress) {
        if id != r.id {
          pr.RecentActive = false
        }
      })
      return nil

`QuorumActive`'s answer is not tied to the abstract state (`RecentActive` is in no `Progress`
record), so both arms are covered: the leader stays, or steps down at its term (the model's
`Step.stepDown`). The `Visit` closure writes `RecentActive` only, which leaves every record as
it was: the closure's invariant is that the `Progress` values are the state's.
-/
module

public import Proof.go_etcd_io.raft.v3.stepLeader.Rest
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__QuorumActive
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__Visit
public import Spec.go_etcd_io.raft.v3.raft__becomeFollower

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

variable (c : CfgM)

set_option maxHeartbeats 1600000 in
/-- **`MsgCheckQuorum`** -/
theorem wp_stepLeader_checkQuorum
    (wp_QuorumActive : tracker.ProgressTracker.QuorumActive.spec (GF := GF) (hG := hG))
    (wp_Visit : tracker.ProgressTracker.Visit.spec (GF := GF) (hG := hG))
    (wp_becomeFollower : raft.becomeFollower.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM) (ents : List EntryM)
    (ctx : List w8) (sn : Option SnapshotM) (rs : List Loc) (dq dqe : DFrac) (cap : Bool)
    (Hty : m.Type' = MsgCheckQuorum) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgPtsC ml dq dqe cap ⟨m, ents, sn, ctx, rs⟩ }}
      (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        ownRaftPhysCV c c.voters r id s' ∗ ⌜err = interface.nil⌝ ∗
        ⌜LeaderNonpropResultC c id s m ents ctx s'⌝ }} := by
  wp_start as ⟨Hphys, Hm⟩
  wp_auto
  wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hm] as Hm
  simp only [Hty, MsgCheckQuorum]
  wp_auto
  -- `r.trk.QuorumActive()`
  icases ownRaftPhysC_tracker_same c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  wp_apply wp_QuorumActive c _ tv _ $$ [$Htrkf $Htrk] as %b %tv' %act ⟨Htrkf, Htrk, -, -⟩
  ihave Hphys := Hback $$ Htrkf Htrk
  -- the `if !QuorumActive()`, joined at the state it leaves: `s`, or the step-down's
  wp_join iprop(∃ (s1 : NState),
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s1 ∗
      "%Hs1" ∷ ⌜s1 = s ∨ ∃ pvs : GMap w64 Progress,
                 s1 = { becomeFollower s s.term (W64 0) with prvals := pvs }⌝ ∗
      "r" ∷ r_ptr ↦ r) at next
    with [Hphys r] as HR
  · cases b
    · wp_auto
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      wp_raft_logC
      wp_apply raft.wp_load_TermC $$ Hphys as Hphys
      wp_apply wp_becomeFollower c r id s s.term (W64 0) (Int.le_refl _) $$ [$Hphys]
        as %pvs Hphys
      wp_join_done
      iexists _
      iframe Hphys r
      ipureintro
      exact .inr ⟨pvs, rfl⟩
    · wp_auto
      wp_join_done
      iexists s
      iframe Hphys r
      ipureintro
      exact .inl rfl
  iNamed HR
  try wp_auto
  -- `r.trk.Visit(...)`: the closure clears `RecentActive`, which no record holds
  icases ownRaftPhysC_shared c r id s1 $$ Hphys with ⟨%lok, #Hfid, -, -, Hphys⟩
  icases ownRaftPhysC_tracker_same c r id s1 $$ Hphys with ⟨%tv1, Htrkf, Htrk, Hback⟩
  wp_apply wp_Visit c _ tv1 ⟨s1.votes, s1.progress, s1.prvals⟩ _
      (fun _ pvsx => iprop(r_ptr ↦ r ∗ ⌜pvsx = s1.prvals⌝))
    $$ [$Htrkf $Htrk $r]
    as ⟨%tvfin, %pvsfin, Htrkf, Htrk, r, %Hpvs⟩
  · isplitr
    · ipureintro; rfl
    imodintro
    unfold visitClosureC
    iintro %i %pr %tv0 %pvs0 %p %D
    wp_start as ⟨%Hicfg, %Hpri, %Hpvi, %HmaxI, Htrkf, Hpr, Hprback, r, %Hpvs0⟩
    wp_auto
    wp_if_destruct
    · -- the leader itself: nothing
      ihave Htrk := Hprback $$ %p Hpr %(And.intro rfl rfl)
      rw [GMap.insert_id _ _ _ Hpvi]
      iapply HΦ
      iexists tv0, pvs0
      iframe Htrkf Htrk r
      ipureintro; exact Hpvs0
    · -- another peer: `pr.RecentActive = false`
      iunfold ownProgress at Hpr
      icases Hpr with ⟨%pv, Hpr⟩
      iNamed Hpr
      wp_auto
      ihave Htrk := Hprback $$ %p [Hpv Hinfl] %(And.intro rfl rfl)
      · iapply ownProgress_intro pr _ p $$ Hpv Hinfl
        ipureintro
        exact Habs
      rw [GMap.insert_id _ _ _ Hpvi]
      iapply HΦ
      iexists tv0, pvs0
      iframe Htrkf Htrk r
      ipureintro; exact Hpvs0
  subst Hpvs
  ihave Hphys := Hback $$ Htrkf Htrk
  iapply HΦ
  iframe Hphys
  ipureintro
  refine ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Hty, ?_⟩)))))⟩
  rcases Hs1 with rfl | ⟨pvs, rfl⟩
  · exact ⟨_, .inl ⟨rfl, rfl⟩⟩
  · exact ⟨pvs, .inr rfl⟩

end proof

end EtcdGrove
end Perennial
