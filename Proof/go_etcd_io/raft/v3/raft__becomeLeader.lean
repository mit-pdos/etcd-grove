/-
Port of election_proof/proof_raft__becomeLeader.v.

Lean notes: the Go code stores the generated constant `go_etcd_io.raft.v3.StateLeader`
(`#(W64 2)`), which `wp_apply` does not unify with `#(stateW64 .leader)`;
`wp_store_state_leader` is `raft.wp_store_state` at that value.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__becomeLeader
public import Spec.go_etcd_io.raft.v3.raft__reset
public import Spec.go_etcd_io.raft.v3.traceBecomeLeader
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.raft__appendEntry
public import Spec.go_etcd_io.raft.v3.tracker.Progress__BecomeReplicate

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

/-- `raft.wp_store_state` at the value the Go code stores. -/
private theorem wp_store_state_leader (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) :
    {{ ownRaftPhys (GF := GF) cfg r id s }}
      (App (Val (GoInstruction (GoStore StateType.ty)))
        (Val (PairV #(r.[raft, go!"state"]) go_etcd_io.raft.v3.StateLeader)))
    {{ RET #(); ownRaftPhys cfg r id { s with role := .leader } }} :=
  raft.wp_store_state (cfg := cfg) r id s .leader

theorem raft.becomeLeader.wp_proof
    (wp_raft_reset : raft.reset.spec (GF := GF) (hG := hG))
    (wp_traceBecomeLeader : traceBecomeLeader.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raft_appendEntry : raft.appendEntry.spec (GF := GF) (hG := hG))
    (wp_Progress_BecomeReplicate : tracker.Progress.BecomeReplicate.spec (GF := GF) (hG := hG)) :
    raft.becomeLeader.spec (GF := GF) (hG := hG) := by
  intro cfg r id s Hrole Hcfg
  wp_start as Hphys
  wp_auto
  -- `becomeLeader` panics on a follower; by assumption we are not one.
  have Hnf : stateW64 s.role ≠ W64 0 := by
    cases h : s.role <;> simp_all [stateW64, StateCandidate, StateLeader, StatePreCandidate]
  wp_apply raft.wp_load_state $$ Hphys as Hphys
  rw [decide_eq_false Hnf]
  wp_auto
  -- `r.step := stepLeader`, then `reset` at the unchanged term, so the vote survives
  wp_apply raft.wp_store_step $$ Hphys as Hphys
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_apply wp_raft_reset $$ [$Hphys] as %pvs ⟨Hphys, %Hmr⟩
  -- `r.tick`, `r.lead := r.id`, `r.state := StateLeader`
  wp_apply raft.wp_store_tick (Hf := .inr rfl) $$ Hphys as Hphys
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  wp_apply raft.wp_store_lead $$ Hphys as Hphys
  wp_apply wp_store_state_leader $$ Hphys as Hphys
  -- the state is now `becomeLeaderPre` up to the order of the record updates
  ihave Hphys : ownRaftPhys cfg r id { becomeLeaderPre id s with prvals := pvs } $$ [Hphys]
  · iapply ownRaftPhys_eq cfg r id _ _ ?_ $$ Hphys
    rfl
  generalize hs1 : ({ becomeLeaderPre id s with prvals := pvs } : NState) = s1
  -- the leader's own `Progress` is marked replicating and recently active; the map
  -- lookup is on the tracker object
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  icases ownRaftPhys_tracker_prvals cfg r id _ $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  wp_auto
  wp_apply wp_tracker_progress_lookup cfg tv _ id Hcfg $$ [$Htrk]
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
    obtain ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩ := (progressAbs_Some _ _ _).1 Habs
    exact (progressAbs_Some _ _ _).2 ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩
  ihave Htrk := Hprback $$ %_ Hpr
  ihave Hphys := Hback $$ %_ %_ Htrkf Htrk
  -- `r.pendingConfIndex = r.raftLog.lastIndex()`
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
  wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, -⟩
  ihave Hphys := Hback $$ Hlog
  wp_apply raft.wp_store_pendingConfIndex $$ Hphys as Hphys
  wp_apply wp_traceBecomeLeader
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %es ⟨Hes, -⟩
  wp_auto
  -- `appendEntry` writes `Term`/`Index` into every element of the slice, so it needs
  -- `Hes`. It returns a bool, and its postcondition says an all-empty batch is never
  -- dropped; the entry's `Data` is nil, so `accepted = true` and the `Panic` on the
  -- `false` branch below is dead code. It also queues a self-addressed `MsgAppResp`, the
  -- self-acknowledgement: the state is `becomeLeader`. `Type` is the zero value
  -- `EntryNormal`, which is what keeps the log's `HnoConfChange` true; and one entry is
  -- not `2^61`.
  wp_apply wp_raft_appendEntry cfg r id _ _ [zero_val raftpb.Entry]
      (by intro e He; simp at He; subst He; rfl) (by simp) $$ [$Hphys $Hes]
    as %accepted ⟨%Hacc, Hes, Hphys⟩
  -- empty payload, so accepted; the `false` branch is gone before any `WP` is stepped on it
  have Hacc' : accepted = true := Hacc (by intro e He; simp at He; subst He; rfl)
  subst Hacc'
  simp only [↓reduceIte]
  wp_auto
  -- `appendEntry` appended the stamped empty entry: that is `becomeLeader` (`Defs.lean`)
  ihave Hphys : ownRaftPhys cfg r id
      { becomeLeader id s with
        prvals := <[id := progressBecomeReplicate p0]> pvs }
      $$ [Hphys]
  · iapply ownRaftPhys_eq cfg r id _ _ ?_ $$ Hphys
    subst hs1
    rfl
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_raft_log
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
