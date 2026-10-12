/-
Port of election_proof/proof_raft__bcastHeartbeatWithCtx.v.

Lean notes: the Rocq helper `wp_bcast_hb` is inlined in the theorem (it was the whole
proof). The Rocq `Local Lemma heartbeat_ok_intro` is a private theorem.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__bcastHeartbeatWithCtx
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__Visit
public import Spec.go_etcd_io.raft.v3.raft__sendHeartbeat

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
/-- The heartbeat `sendHeartbeat` sends is `HeartbeatOk` at the protocol reading of a
leader's state, given its two bounds against that state's `committed` and `Match`. -/
private theorem heartbeatOk_intro (id : w64) (s : NState) (to c : w64) (cl : List w8)
    (Hl : s.role = .leader) (Hto : to ≠ id)
    (Hc : uint.Z c ≤ uint.Z s.logst.committed)
    (Hm : uint.Z c ≤ uint.Z ((prvalsMatch s.prvals !! to).getD (W64 0))) :
    HeartbeatOk id (toPState s)
      (Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) c (W64 0) [] [] cl) := by
  unfold HeartbeatOk matchOf toPState
  simp only [Hl, ↓reduceIte]
  exact ⟨trivial, trivial, trivial, Hto, Hc, Hm⟩

/-- `ownTracker` at two indices that are equal (by computation: a state reached by
record updates). -/
private theorem ownTracker_cast (cfg : GSet w64) (tv : tracker.ProgressTracker) (t t' : Trk)
    (h : t = t') : ownTracker (GF := GF) cfg tv t ⊢ ownTracker cfg tv t' := h ▸ .rfl

/-- The same proof as `bcastAppend`'s (`proof_raft__bcastAppend.v`): the caller
invariant of `Visit` is the raft struct with a tracker-shaped hole (the wand of
`ownRaftPhys_tracker_prvals`), quantified over the `Progress` values; `ms`
accumulates. The difference is the fact accumulated: each heartbeat is `HeartbeatOk` at
`toPState s`. The closure's `sendHeartbeat` is called at
`{ sendMsgs s ms with prvals := pvsx }`, whose `committed` is `s`'s and whose `Match`
values are `s`'s (the invariant's `Hmm`), so its bounds are bounds at `s`. -/
theorem raft.bcastHeartbeatWithCtx.wp_proof
    (wp_ProgressTracker_Visit : tracker.ProgressTracker.Visit.spec (GF := GF) (hG := hG))
    (wp_raft_sendHeartbeat : raft.sendHeartbeat.spec (GF := GF) (hG := hG)) :
    raft.bcastHeartbeatWithCtx.spec (GF := GF) (hG := hG) := by
  intro cfg r id s ctx cl Hlead
  wp_start as Hphys
  iNamed Hphys
  wp_auto
  icases ownRaftPhys_tracker_prvals $$ Hphys with ⟨%tv, Htrkf, Htrk, Hrest⟩
  wp_apply wp_ProgressTracker_Visit cfg _ tv ⟨s.votes, s.progress, s.prvals⟩ _
      (fun _ pvsx => iprop(∃ (ms : List Msg),
        "rp" ∷ r_ptr ↦ r ∗
        "cp" ∷ ctx_ptr ↦ ctx ∗
        "%Hms" ∷ ⌜∀ m ∈ ms, HeartbeatOk id (toPState s) m ∧ m.ctx = cl⌝ ∗
        "%Hmm" ∷ ⌜prvalsMatch pvsx = prvalsMatch s.prvals⌝ ∗
        "Hrest" ∷ (∀ tvx pvsx', r.[raft, go!"trk"] ↦ tvx -∗
            ownTracker cfg tvx ⟨s.votes, s.progress, pvsx'⟩ -∗
            ownRaftPhys cfg r id { sendMsgs s ms with prvals := pvsx' })))
    $$ [$Htrkf $Htrk r ctx Hrest]
  · isplitl [r ctx Hrest]
    · iexists []
      simp only [named]
      iframe r ctx
      isplitr
      · ipureintro; simp
      isplitr
      · ipureintro; trivial
      iintro %tvx %pvsx Hf Ht
      ihave Hphys := Hrest $$ %tvx %pvsx Hf Ht
      iapply ownRaftPhys_eq cfg r id _ _ (by cases s; simp [sendMsgs]) $$ Hphys
    -- the closure
    imodintro
    unfold visitClosure
    iintro %i %pr %tv0 %pvs0 %p %D
    wp_start as ⟨%Hicfg, %Hpri, %Hpvi, %HmaxI, Htrkf, Hpr, Hback, HI⟩
    iNamed HI
    ihave Htrk := Hback $$ Hpr
    ihave Hphys := Hrest $$ Htrkf Htrk
    wp_auto
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    have Hmi : prvalsMatch (<[i := p]> pvs0) = prvalsMatch s.prvals := by
      rw [prvalsMatch_insert_same pvs0 i p p Hpvi rfl, Hmm]
    by_cases Hii : i = id
    · -- the leader itself: nothing is sent
      rw [decide_eq_true Hii]
      wp_auto
      icases ownRaftPhys_tracker_prvals $$ Hphys with ⟨%tv1, Htrkf, Htrk, Hrest⟩
      ihave Htrk := ownTracker_cast cfg tv1 _ ⟨s.votes, s.progress, <[i := p]> pvs0⟩ ?_ $$ Htrk
      · rfl
      iapply HΦ
      iexists tv1, _
      iframe Htrkf Htrk
      iexists ms
      simp only [named]
      iframe rp cp
      isplitr
      · ipureintro; exact Hms
      isplitr
      · ipureintro; exact Hmi
      iintro %tvx %pvsx Hf Ht
      ihave Hphys := Hrest $$ %tvx %pvsx Hf [Ht]
      · iapply ownTracker_cast cfg tvx ⟨s.votes, s.progress, pvsx⟩ _ ?_ $$ Ht
        rfl
      iapply ownRaftPhys_eq cfg r id _ _ (by cases s; rfl) $$ Hphys
    · -- a peer: one heartbeat
      rw [decide_eq_false Hii]
      wp_auto
      wp_apply wp_raft_sendHeartbeat _ _ _ _ i ctx cl Hii Hicfg $$ [$Hphys]
        as %c %pvs' ⟨Hphys, %Hc1, %Hc2, %Hmm'⟩
      · iexact Hctx
      try wp_auto
      icases ownRaftPhys_tracker_prvals $$ Hphys with ⟨%tv1, Htrkf, Htrk, Hrest⟩
      ihave Htrk := ownTracker_cast cfg tv1 _ ⟨s.votes, s.progress, pvs'⟩ ?_ $$ Htrk
      · rfl
      iapply HΦ
      iexists tv1, _
      iframe Htrkf Htrk
      iexists ms ++ [Msg.mkV .heartbeat id i s.term false (W64 0) (W64 0) c (W64 0) [] [] cl]
      simp only [named]
      iframe rp cp
      isplitr
      · ipureintro
        intro m Hm
        rcases List.mem_append.1 Hm with Hm | Hm
        · exact Hms m Hm
        · rw [List.mem_singleton] at Hm
          subst Hm
          refine ⟨heartbeatOk_intro id s i c cl Hlead Hii Hc1 ?_, rfl⟩
          simp only at Hc2
          rw [Hmi] at Hc2
          exact Hc2
      isplitr
      · ipureintro; simp only at Hmm'; rw [Hmm', Hmi]
      iintro %tvx %pvsx Hf Ht
      ihave Hphys := Hrest $$ %tvx %pvsx Hf [Ht]
      · iapply ownTracker_cast cfg tvx ⟨s.votes, s.progress, pvsx⟩ _ ?_ $$ Ht
        rfl
      iapply ownRaftPhys_eq cfg r id _ _ (by cases s; simp [sendMsgs, List.append_assoc]) $$ Hphys
  iintro ⟨%tvfin, %pvsfin, Htrkf, Htrk, HI⟩
  iNamed HI
  ihave Hphys := Hrest $$ %tvfin %pvsfin Htrkf [Htrk]
  · iapply ownTracker_cast cfg tvfin _ _ ?_ $$ Htrk
    rfl
  wp_auto
  iapply HΦ $$ %ms %pvsfin
  iframe Hphys
  ipureintro
  exact ⟨Hms, Hmm⟩

end proof

end EtcdGrove
end Perennial
